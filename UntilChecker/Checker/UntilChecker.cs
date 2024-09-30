using System.Diagnostics;
using System.Numerics;
using Timepiece;
using UntilChecker.IR;
using UntilChecker.DataTypes;
using ZenLib;
using ZenLib.ModelChecking;

namespace UntilChecker.Checker;

public class UntilChecker<TNode, TRoute, TSym, TNetwork>(
  TNetwork network,
  Func<TNode, TNode, Zen<TSym>, Zen<bool>> convergeBefore,
  Func<TNode, Zen<TRoute>, Zen<TSym>, Zen<bool>> preAnnotations,
  Func<TNode, Zen<TRoute>, Zen<TSym>, Zen<bool>> postAnnotations) :
  Checker<TNode, TRoute, TSym, TNetwork>(network)
  where TNode: notnull
  where TNetwork : Network<TNode, TRoute, TSym>
{
  public readonly Func<TNode, TNode, Zen<TSym>, Zen<bool>> ConvergeBefore = convergeBefore;
  public readonly Func<TNode, Zen<TRoute>, Zen<TSym>, Zen<bool>> PreAnnotations = preAnnotations;
  public readonly Func<TNode, Zen<TRoute>, Zen<TSym>, Zen<bool>> PostAnnotations = postAnnotations;

  public Zen<bool> InitialCheckCondition(TNode node, Zen<TSym> sym)
  {
    var isRoot = ZenExtension.And(Network.Digraph[node].Select(n =>
      Zen.Not(ConvergeBefore(n, node, sym))));
    return Zen.If(
      isRoot,
      PostAnnotations(node, Network.InitialRoutes(node, sym), sym),
      PreAnnotations(node, Network.InitialRoutes(node, sym), sym));
  }

  public Zen<bool> PreCheckCondition(
    TNode src, TNode dst, Zen<TRoute> srcRoute, Zen<TRoute> dstRoute, Zen<TRoute> newDstRoute, Zen<TSym> sym) =>
    Zen.Implies(
      Zen.And(
        Zen.Or(
          PreAnnotations(src, srcRoute, sym),
          Zen.And(PostAnnotations(src, srcRoute, sym), Zen.Not(ConvergeBefore(src, dst, sym)))),
        PreAnnotations(dst, dstRoute, sym)),
      PreAnnotations(dst, newDstRoute, sym));

  public Zen<bool> PostCheckCondition(
    TNode src, TNode dst, Zen<TRoute> srcRoute, Zen<TRoute> dstRoute, Zen<TRoute> newDstRoute, Zen<TSym> sym) =>
    Zen.Implies(
      Zen.And(
        Zen.Or(PreAnnotations(src, srcRoute, sym), PostAnnotations(src, srcRoute, sym)),
        PostAnnotations(dst, dstRoute, sym)),
      PostAnnotations(dst, newDstRoute, sym));

  public Zen<bool> LivenessCheckCondition(
    TNode src, TNode dst, Zen<TRoute> srcRoute, Zen<TRoute> dstRoute, Zen<TRoute> newDstRoute, Zen<TSym> sym) =>
    Zen.Implies(
      Zen.And(
        ConvergeBefore(src, dst, sym),
        PostAnnotations(src, srcRoute, sym),
        PreAnnotations(dst, dstRoute, sym)),
      PostAnnotations(dst, newDstRoute, sym));

  public Zen<bool> DagCheckCondition(
    IDictionary<TNode, Zen<bool>> acc, Zen<TSym> sym) =>
    Zen.Implies(
      ZenExtension.And(network.Digraph.Nodes.Select(node =>
        Zen.Implies(
          ZenExtension.And(network.Digraph[node].Select(neighbor =>
            Zen.Implies(
              ConvergeBefore(neighbor, node, sym),
              acc[neighbor]))),
          acc[node]))),
      ZenExtension.And(network.Digraph.Nodes.Select(node => acc[node])));

  protected override IDictionary<string, Func<Option<CheckError>>> GenerateTasks()
  {
    var tasks = new Dictionary<string, Func<Option<CheckError>>>();
    var routes = Network.Digraph.MapNodes(node => Zen.Symbolic<TRoute>($"route-{node}"));
    var sym = Zen.Symbolic<TSym>("symbolics");
    var constraint = Network.Constraint(sym);
    var acc = network.Digraph.MapNodes(n => Zen.Symbolic<bool>($"acc-{n}"));

    var dagCheck = DagCheckCondition(acc, sym);
    tasks.Add("dag", () =>
    {
      var result = Zen.And(constraint, Zen.Not(dagCheck)).Solve();
      return result.IsSatisfiable()
        ? Option.Some<CheckError>(new DagError<TNode, TRoute, TSym, TNetwork>(
          this, result, acc, sym))
        : Option.None<CheckError>();
    });

    foreach (var node in Network.Digraph.Nodes)
    {
      var initCheck = InitialCheckCondition(node, sym);
      tasks.Add($"init-{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(initCheck)).Solve();
        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new NodeError<TNode, TRoute, TSym, TNetwork>(
            this, result, node, Network.InitialRoutes(node, sym), sym))
          : Option.None<CheckError>();
      });
    }

    foreach (var (neighbor, node) in Network.Digraph.Edges())
    {
      var newRoute = Network.MergeFunction(
        routes[node],
        Network.TransferFunctions(neighbor, node, routes[neighbor], sym));
      var preCheck = PreCheckCondition(
        neighbor, node, routes[neighbor], routes[node], newRoute, sym);
      var postCheck = PostCheckCondition(
        neighbor, node, routes[neighbor], routes[node], newRoute, sym);
      var livenessCheck = LivenessCheckCondition(
        neighbor, node, routes[neighbor], routes[node], newRoute, sym);

      tasks.Add($"edge-{neighbor},{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(preCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<TNode, TRoute, TSym, TNetwork>(
            "pre-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute, sym));
        result = Zen.And(constraint, Zen.Not(postCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<TNode, TRoute, TSym, TNetwork>(
            "post-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute, sym));
        result = Zen.And(constraint, Zen.Not(livenessCheck)).Solve();

        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new EdgeError<TNode, TRoute, TSym, TNetwork>(
            "liveness-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute, sym))
          : Option.None<CheckError>();
      });
    }

    return tasks;
  }
}

public record DagError<TNode, TRoute, TSym, TNetwork>(
  UntilChecker<TNode, TRoute, TSym, TNetwork> Checker,
  ZenSolution Model,
  IDictionary<TNode, Zen<bool>> Acc,
  Zen<TSym> Sym) : CheckError
  where TNode : notnull
  where TNetwork : Network<TNode, TRoute, TSym>
{
  public override void Report()
  {
    Console.WriteLine("dag check");
    var subgraph = Checker.Network.Digraph.Nodes.Where(node => !Model.Get(Acc[node])).ToList();
    Console.Write("the following nodes form a cycle:\n  ");
    foreach (var node in subgraph)
      Console.Write($"{node} ");
    Console.WriteLine("\nconverge before relationship between these nodes:");
    foreach (var edge in Checker.Network.Digraph.Edges())
      if (subgraph.Contains(edge.Item1) && subgraph.Contains(edge.Item2) &&
          Model.Get(Checker.ConvergeBefore(edge.Item1, edge.Item2, Sym)))
        Console.WriteLine($"  {edge.Item1} converges before {edge.Item2}");
    Console.WriteLine($"symbolics := {Model.Get(Sym)}");
  }
}

public record NodeError<TNode, TRoute, TSym, TNetwork>(
  UntilChecker<TNode, TRoute, TSym, TNetwork> Checker,
  ZenSolution Model,
  TNode Node, Zen<TRoute> Route, Zen<TSym> Sym) : CheckError
  where TNode: notnull
  where TNetwork: Network<TNode, TRoute, TSym>
{
  public override void Report()
  {
    Console.WriteLine($"node check at {Node}");
    Console.WriteLine($"node {Node} has route := {Model.Get(Route)}");
    Console.WriteLine($"symbolics := {Model.Get(Sym)}");
  }
}

public record EdgeError<TNode, TRoute, TSym, TNetwork>(
  string Kind,
  UntilChecker<TNode, TRoute, TSym, TNetwork> Checker,
  ZenSolution Model,
  TNode Src, TNode Dst, Zen<TRoute> SrcRoute, Zen<TRoute> DstRoute, Zen<TRoute> NewDstRoute, Zen<TSym> Sym) : CheckError
  where TNode: notnull
  where TNetwork: Network<TNode, TRoute, TSym>
{
  public override void Report()
  {
    Console.WriteLine($"{Kind} check at src {Src}, dst {Dst}");
    Console.WriteLine($"node {Src} has route := {Model.Get(SrcRoute)}");
    Console.WriteLine($"node {Dst} has route := {Model.Get(DstRoute)}");
    Console.WriteLine($"after update, {Dst} has new route := {Model.Get(NewDstRoute)}");
    Console.WriteLine($"{Src} converge before {Dst}: {Model.Get(Checker.ConvergeBefore(Src, Dst, Sym))}");
    Console.WriteLine($"{Dst} converge before {Src}: {Model.Get(Checker.ConvergeBefore(Dst, Src, Sym))}");
    Console.WriteLine($"symbolics := {Model.Get(Sym)}");
  }
}

public static class UntilCheckerExtension
{
  private static bool Repair<TSym>(
    this UntilChecker<string, BgpRoute, TSym, CiscoNetwork<TSym>> checker,
    string task,
    CheckError err,
    TemplateArguments args,
    bool quiet)
  {
    if (err is not EdgeError<string, BgpRoute, TSym, CiscoNetwork<TSym>> error)
    {
      Console.WriteLine($"error at {task} is not repairable.");
      Console.Out.WriteLine("----------------------");
      return false;
    }

    var src = error.Src;
    var dst = error.Dst;
    var network = checker.Network;
    var config = network.Config;

    var exportPolicy = config.NodeConfigs[src].Polices[dst].ExportPolicy;
    var importPolicy = config.NodeConfigs[dst].Polices[src].ImportPolicy;
    if (!quiet)
    {
      Console.WriteLine($"start repair, src = {src}, dst = {dst}");
      Console.WriteLine($"export policy to be repaired:\n{exportPolicy.Debug()}");
      Console.WriteLine($"import policy to be repaired:\n{importPolicy.Debug()}");
      // Console.WriteLine($"rank of src {src} is {error.Model.Get(checker.Ranks[src])}");
      // Console.WriteLine($"rank of dst {dst} is {error.Model.Get(checker.Ranks[dst])}");
    }

    var exportTemplate = exportPolicy.GenerateTemplate(args);
    var importTemplate = importPolicy.GenerateTemplate(args);

    List<(BgpRoute, BgpRoute, TSym)> counterExamples = [
      (error.Model.Get(error.SrcRoute), error.Model.Get(error.DstRoute), error.Model.Get(error.Sym))];
    if (!quiet)
      Console.WriteLine($"counter example: {counterExamples[0]}");

    for (int i = 0; i < args.MaxRetry; i++)
    {
      if (!quiet)
        Console.WriteLine($"Start {i}-th repair...");
      var model = Zen.Minimize(
        exportTemplate.Cost + importTemplate.Cost,
        Zen.And(
          exportTemplate.Constraint,
          importTemplate.Constraint,
          ZenExtension.And(
            counterExamples.Select(cex =>
             {
                var srcRoute = cex.Item1;
                var dstRoute = cex.Item2;
                var sym = cex.Item3;
                var newDstState = network.MergeFunction(
                  dstRoute,
                  importTemplate.TransferFunction(exportTemplate.TransferFunction(srcRoute))
                    .IncreaseAsLength()
                    .AddAs(config.NodeConfigs[src].LocalAs));
                var preCheck = checker.PreCheckCondition(src, dst, srcRoute, dstRoute, newDstState, sym);
                var postCheck = checker.PostCheckCondition(src, dst, srcRoute, dstRoute, newDstState, sym);
                var livenessCheck = checker.LivenessCheckCondition(src, dst, srcRoute, dstRoute, newDstState, sym);
                return Zen.And(preCheck, postCheck, livenessCheck);
              }))));

      if (model.IsSatisfiable())
      {
        var exportProposal = exportTemplate.Repair(model);
        var importProposal = importTemplate.Repair(model);

        if (!quiet)
        {
          Console.Out.WriteLine("proposal generated");
          Console.Out.WriteLine($"export policy proposal:\n{exportProposal.Debug()}");
          Console.Out.WriteLine($"import policy proposal:\n{importProposal.Debug()}");
        }

        var srcRoute = Zen.Symbolic<BgpRoute>($"srcRoute");
        var dstRoute = Zen.Symbolic<BgpRoute>($"dstRoute");
        var sym = Zen.Symbolic<TSym>("symbolics");
        var constraint = network.Constraint(sym);
        var newDstRoute = checker.Network.MergeFunction(
          dstRoute,
          importProposal.Transfer(exportProposal.Transfer(srcRoute))
            .IncreaseAsLength()
            .AddAs(config.NodeConfigs[src].LocalAs));
        // Console.WriteLine($"{newDstRoute.ToString()}");
        var preCheck = checker.PreCheckCondition(src, dst, srcRoute, dstRoute, newDstRoute, sym);
        var postCheck = checker.PostCheckCondition(src, dst, srcRoute, dstRoute, newDstRoute, sym);
        var livenessCheck = checker.LivenessCheckCondition(src, dst, srcRoute, dstRoute, newDstRoute, sym);
        // Console.WriteLine($"{livenessCheck}");

        model = Zen.And(constraint, Zen.Not(Zen.And(preCheck, postCheck, livenessCheck))).Solve();
        // if (!model.IsSatisfiable()) model = Zen.And(constraint, Zen.Not(postCheck)).Solve();
        // if (!model.IsSatisfiable()) model = Zen.And(constraint, Zen.Not(livenessCheck)).Solve();

        if (model.IsSatisfiable())
        {
          counterExamples.Add((model.Get(srcRoute), model.Get(dstRoute), model.Get(sym)));
          if (!quiet)
          {
            Console.Out.WriteLine("proposal failed!");
            Console.Out.WriteLine($"counterexample: {counterExamples.Last()}, newDstRoute := {model.Get(newDstRoute)}");
          }
        }
        else
        {
          if (!quiet)
          {
            Console.Out.WriteLine("repair succeed!");
            Console.Out.WriteLine($"repaired import policy: {importProposal.Debug()}");
            Console.Out.WriteLine($"repaired export policy: {exportProposal.Debug()}");
            Console.Out.WriteLine("----------------------");
          }

          return true;
        }
      }
      else
      {
        if (!quiet)
          Console.Out.WriteLine("repair is impossible for this template");
        break;
      }
    }

    if (!quiet)
    {
      Console.Out.WriteLine("repair failed, sorry!");
      Console.Out.WriteLine("please try to change arguments of template generation");
      Console.Out.WriteLine("----------------------");
    }

    return false;
  }

  public static void CheckAndRepair<TSym>(
    this UntilChecker<string, BgpRoute, TSym, CiscoNetwork<TSym>> checker,
    TemplateArguments args,
    bool quiet,
    bool noRepair)
  {
    var errors = checker.Check(quiet);
    if (noRepair) return;
    var globalTimer = Stopwatch.StartNew();
    var timeCollector = new Dictionary<string, long>(errors.Count);
    var failedCount = 0;
    foreach (var p in errors)
    {
      var localTimer = Stopwatch.StartNew();
      var result = Repair(checker, p.Key, p.Value, args, quiet);
      timeCollector[p.Key] = localTimer.ElapsedMilliseconds;
      if (!result) failedCount++;
    }
    var wallTime = globalTimer.ElapsedMilliseconds;
    Console.WriteLine($"All repairs ended. Total time used: {wallTime} ms");
    StatisticsExtensions.ReportTimes(timeCollector, Statistics.Summary, wallTime, true);
    if (failedCount == 0)
      Console.WriteLine("All repairs succeed. Congrats!");
    else
      Console.WriteLine($"{failedCount}/{errors.Count} repairs failed. Please try to change template generation arguments.");
  }
}
