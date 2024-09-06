using System.Collections;
using System.Collections.Concurrent;
using System.Diagnostics;
using System.Numerics;
using Timepiece;
using UntilChecker.IR;
using UntilChecker.DataTypes;
using ZenLib;
using ZenLib.ModelChecking;

namespace UntilChecker.Checker;

public class UntilChecker<NodeType, RouteType, NetworkType> :
  Checker<NodeType, RouteType, NetworkType>
  where NodeType: notnull
  where NetworkType : Network<NodeType, RouteType>
{
  public readonly IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PhiAnnotations;
  public readonly IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PsiAnnotations;

  public readonly IDictionary<(NodeType, NodeType), Zen<bool>> ConvergeBefore;

  public UntilChecker(
    NetworkType network,
    IDictionary<(NodeType, NodeType), Zen<bool>> convergeBefore,
    IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
    IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations): base(network)
  {
    ConvergeBefore = convergeBefore;
    PhiAnnotations = phiAnnotations;
    PsiAnnotations = psiAnnotations;
  }

  public UntilChecker(
    NetworkType network,
    IDictionary<NodeType, Zen<BigInteger>> ranks,
    IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
    IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations) : base(network)
  {
    ConvergeBefore = network.Digraph.MapEdges(p => ranks[p.Item1] < ranks[p.Item2]);
    PhiAnnotations = phiAnnotations;
    PsiAnnotations = psiAnnotations;
  }

  public Zen<bool> InitialCheckCondition(NodeType node)
  {
    var noConvergeBefore = ZenExtension.And(Network.Digraph[node].Select(n =>
      Zen.Not(ConvergeBefore[(n, node)])));
    return Zen.If(
      noConvergeBefore,
      PsiAnnotations[node](Network.InitialRoutes[node]),
      PhiAnnotations[node](Network.InitialRoutes[node]));
  }

  public Zen<bool> PreCheckCondition(
    NodeType src, NodeType dst, Zen<RouteType> srcState, Zen<RouteType> dstState, Zen<RouteType> newDstState) =>
    Zen.Implies(
      Zen.And(
        Zen.Or(PhiAnnotations[src](srcState), PsiAnnotations[src](srcState)),
        Zen.Implies(ConvergeBefore[(dst, src)], PhiAnnotations[src](srcState)),
        PhiAnnotations[dst](dstState)),
      Zen.Or(PhiAnnotations[dst](newDstState), PsiAnnotations[dst](newDstState)));

  public Zen<bool> PostCheckCondition(
    NodeType src, NodeType dst, Zen<RouteType> srcState, Zen<RouteType> dstState, Zen<RouteType> newDstState) =>
    Zen.Implies(
      Zen.And(
        Zen.Or(PhiAnnotations[src](srcState), PsiAnnotations[src](srcState)),
        PsiAnnotations[dst](dstState)),
      PsiAnnotations[dst](newDstState));

  public Zen<bool> LivenessCheckCondition(
    NodeType src, NodeType dst, Zen<RouteType> srcState, Zen<RouteType> dstState, Zen<RouteType> newDstState) =>
    Zen.Implies(
      Zen.And(
        ConvergeBefore[(src, dst)],
        Zen.Or(PhiAnnotations[dst](dstState), PsiAnnotations[dst](dstState)),
        PsiAnnotations[src](srcState)),
      PsiAnnotations[dst](newDstState));


  protected override IDictionary<string, Func<Option<CheckError>>> GenerateTasks()
  {
    var tasks = new Dictionary<string, Func<Option<CheckError>>>();
    var routes = Network.Digraph.MapNodes(node => Zen.Symbolic<RouteType>($"route-{node}"));
    var constraint = Network.Symbolics.Length != 0 ? Zen.And(Network.Symbolics.Select(sym => sym.Encode())) : Zen.True();

    foreach (var node in Network.Digraph.Nodes)
    {
      var initCheck = InitialCheckCondition(node);
      tasks.Add($"init-{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(initCheck)).Solve();
        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new NodeError<NodeType, RouteType, NetworkType>(this, result, node, Network.InitialRoutes[node]))
          : Option.None<CheckError>();
      });
    }

    foreach (var (neighbor, node) in Network.Digraph.Edges())
    {
      var newRoute = Network.MergeFunction(
        routes[node],
        Network.TransferFunctions[(neighbor, node)](routes[neighbor]));

      var preCheck = PreCheckCondition(neighbor, node, routes[neighbor], routes[node], newRoute);
      var postCheck = PostCheckCondition(neighbor, node, routes[neighbor], routes[node], newRoute);
      if (neighbor.ToString() == "r1239" && node.ToString() == "r1241")
        Console.WriteLine($"r1239 to r1241!!!");
      var livenessCheck = LivenessCheckCondition(neighbor, node, routes[neighbor], routes[node], newRoute);

      tasks.Add($"edge-{neighbor},{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(preCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            "pre-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute));
        result = Zen.And(constraint, Zen.Not(postCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            "post-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute));
        result = Zen.And(constraint, Zen.Not(livenessCheck)).Solve();

        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            "liveness-check", this, result, neighbor, node, routes[neighbor], routes[node], newRoute))
          : Option.None<CheckError>();
      });
    }

    return tasks;
  }
}

public class NodeError<NodeType, RouteType, NetworkType>(
  UntilChecker<NodeType, RouteType, NetworkType> checker,
  ZenSolution model,
  NodeType node, Zen<RouteType> route) : CheckError
  where NetworkType: Network<NodeType, RouteType>
{
  public override void Report()
  {
    Console.WriteLine($"node check at {node}");
    Console.WriteLine($"node {node} has route := {model.Get(route)}");
    foreach (var sym in checker.Network.Symbolics) Console.WriteLine($"symbolic {sym.Name} := {sym.GetSolution(model)}");
  }
}

public class EdgeError<NodeType, RouteType, NetworkType>(
  string kind,
  UntilChecker<NodeType, RouteType, NetworkType> checker,
  ZenSolution model,
  NodeType src,
  NodeType dst,
  Zen<RouteType> srcRoute,
  Zen<RouteType> dstRoute,
  Zen<RouteType> newDstRoute) : CheckError
  where NetworkType : Network<NodeType, RouteType>
{
  public readonly ZenSolution Model = model;
  public readonly NodeType Src = src;
  public readonly NodeType Dest = dst;
  public readonly RouteType SrcState = model.Get(srcRoute);
  public readonly RouteType DstState = model.Get(dstRoute);

  public override void Report()
  {
    Console.WriteLine($"{kind} check at src {Src}, dst {Dest}");
    Console.WriteLine($"node {Src} has route := {SrcState}");
    Console.WriteLine($"node {Dest} has route := {DstState}");
    Console.WriteLine($"after update, {Dest} has new route := {Model.Get(newDstRoute)}");
    Console.WriteLine($"{Src} converge before {Dest}: {Model.Get(checker.ConvergeBefore[(Src, Dest)])}");
    Console.WriteLine($"{Dest} converge before {Src}: {Model.Get(checker.ConvergeBefore[(Dest, Src)])}");
    foreach (var sym in checker.Network.Symbolics)
      Console.WriteLine($"symbolic {sym.Name} := {sym.GetSolution(Model)}");
  }
}

public static class UntilCheckerExtension
{
  public static bool Repair(
    this UntilChecker<string, RouteEnvironment, CiscoNetwork> checker,
    string task,
    CheckError err,
    TemplateArguments args,
    bool quiet)
  {
    EdgeError<string, RouteEnvironment, CiscoNetwork> error;
    try
    {
      error = (EdgeError<string, RouteEnvironment, CiscoNetwork>)err;
    }
    catch (InvalidCastException)
    {
      Console.WriteLine($"error at {task} is not repairable.");
      Console.Out.WriteLine("----------------------");
      return false;
    }

    var src = error.Src;
    var dst = error.Dest;
    var network = checker.Network;
    var config = network.Config;
    var constraint = network.Symbolics.Length != 0 ? Zen.And(network.Symbolics.Select(sym => sym.Encode())) : Zen.True();

    var exportPolicy = config.NodeConfigs[src].Polices[dst].ExportPolicy;
    var importPolicy = config.NodeConfigs[dst].Polices[src].ImportPolicy;
    if (!quiet)
    {
      Console.WriteLine($"export policy to be repaired:\n{exportPolicy.Debug()}");
      Console.WriteLine($"import policy to be repaired:\n{importPolicy.Debug()}");
      // Console.WriteLine($"rank of src {src} is {error.Model.Get(checker.Ranks[src])}");
      // Console.WriteLine($"rank of dst {dst} is {error.Model.Get(checker.Ranks[dst])}");
    }

    var exportTemplate = exportPolicy.GenerateTemplate(args);
    var importTemplate = importPolicy.GenerateTemplate(args);

    List<(RouteEnvironment, RouteEnvironment)> counterExamples = [(error.SrcState, error.DstState)];
    if (!quiet)
      Console.WriteLine($"counter example:\n  src {src} = {error.SrcState}\n  dst {dst} = {error.DstState}");

    for (int i = 0; i < args.MaxRetry; i++)
    {
      if (!quiet)
        Console.WriteLine($"Start {i}-th repair...");
      var model = Zen.Minimize(
        exportTemplate.Cost + importTemplate.Cost,
        Zen.And(
          exportTemplate.Constraint,
          importTemplate.Constraint,
          Zen.And(
            counterExamples.Select(cex =>
              {
                var srcState = cex.Item1;
                var dstState = cex.Item2;
                var newDstState = network.MergeFunction(
                  dstState,
                  importTemplate.TransferFunction(exportTemplate.TransferFunction(srcState))
                    .IncrementAsPathLength(BigInteger.One)
                    .AddAsSet(config.NodeConfigs[src].LocalAs));
                var preCheck = checker.PreCheckCondition(src, dst, srcState, dstState, newDstState);
                var postCheck = checker.PostCheckCondition(src, dst, srcState, dstState, newDstState);
                var livenessCheck = checker.LivenessCheckCondition(src, dst, srcState, dstState, newDstState);
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

        var srcState = Zen.Symbolic<RouteEnvironment>("srcState");
        var dstState = Zen.Symbolic<RouteEnvironment>("dstState");
        var newDstState = checker.Network.MergeFunction(
          dstState,
          importProposal.Transfer(exportProposal.Transfer(srcState))
            .IncrementAsPathLength(BigInteger.One)
            .AddAsSet(config.NodeConfigs[src].LocalAs));
        var preCheck = checker.PreCheckCondition(src, dst, srcState, dstState, newDstState);
        var postCheck = checker.PostCheckCondition(src, dst, srcState, dstState, newDstState);
        var livenessCheck = checker.LivenessCheckCondition(src, dst, srcState, dstState, newDstState);

        model = Zen.And(constraint, Zen.Not(preCheck)).Solve();
        if (!model.IsSatisfiable()) model = Zen.And(constraint, Zen.Not(postCheck)).Solve();
        if (!model.IsSatisfiable()) model = Zen.And(constraint, Zen.Not(livenessCheck)).Solve();

        if (model.IsSatisfiable())
        {
          if (!quiet)
          {
            Console.Out.WriteLine("proposal failed!");
            Console.Out.WriteLine($"failed model: {model.VariableAssignment}");
            Console.Out.WriteLine(
              $"counterexample\n  src {src} = {model.Get(srcState)}\n  dst {dst} = {model.Get(dstState)}");
          }

          counterExamples.Add((model.Get(srcState), model.Get(dstState)));
        }
        else
        {
          if (!quiet)
          {
            Console.Out.WriteLine("repair succeed!");
            Console.Out.WriteLine($"repaired import policy: {importProposal.Debug()}");
            Console.Out.WriteLine($"repaired export policy: {exportPolicy.Debug()}");
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

  public static void CheckAndRepair(
    this UntilChecker<string, RouteEnvironment, CiscoNetwork> checker,
    TemplateArguments args,
    bool quiet)
  {
    var errors = checker.Check(quiet);
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
