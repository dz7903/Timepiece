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

public class UntilChecker<NodeType, RouteType, NetworkType>(
  NetworkType network,
  IDictionary<NodeType, Zen<BigInteger>> ranks,
  IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
  IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations) :
  Checker<NodeType, RouteType, NetworkType>(network)
  where NodeType: notnull
  where NetworkType : Network<NodeType, RouteType>
{
  public readonly IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PhiAnnotations = phiAnnotations;
  public readonly IDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PsiAnnotations = psiAnnotations;
  public readonly IDictionary<NodeType, Zen<BigInteger>> Ranks = ranks;

  public Zen<bool> PreCheckCondition(
    NodeType src, NodeType dst, Zen<RouteType> srcState, Zen<RouteType> dstState, Zen<RouteType> newDstState) =>
    Zen.Implies(
      Zen.And(
        Zen.Or(PhiAnnotations[src](srcState), PsiAnnotations[src](srcState)),
        Zen.Implies(Ranks[src] > Ranks[dst], PhiAnnotations[src](srcState)),
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
        Ranks[src] < Ranks[dst],
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
      var initCheck = Zen.If(
        Ranks[node] == BigInteger.Zero,
        PsiAnnotations[node](Network.InitialRoutes[node]),
        PhiAnnotations[node](Network.InitialRoutes[node]));
      tasks.Add($"init-{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(initCheck)).Solve();
        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new NodeError<NodeType, RouteType>(
            result, node, Network.InitialRoutes[node], Network.Symbolics))
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
      var livenessCheck = LivenessCheckCondition(neighbor, node, routes[neighbor], routes[node], newRoute);

      tasks.Add($"edge-{neighbor},{node}", () =>
      {
        var result = Zen.And(constraint, Zen.Not(preCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            this, "pre-check", result, neighbor, node, routes[neighbor], routes[node], newRoute, Network.Symbolics));
        result = Zen.And(constraint, Zen.Not(postCheck)).Solve();
        if (result.IsSatisfiable())
          return Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            this, "post-check", result, neighbor, node, routes[neighbor], routes[node], newRoute, Network.Symbolics));
        result = Zen.And(constraint, Zen.Not(livenessCheck)).Solve();

        return result.IsSatisfiable()
          ? Option.Some<CheckError>(new EdgeError<NodeType, RouteType, NetworkType>(
            this, "liveness-check", result, neighbor, node, routes[neighbor], routes[node], newRoute, Network.Symbolics))
          : Option.None<CheckError>();
      });
    }

    return tasks;
  }
}

public class NodeError<NodeType, RouteType>(
  ZenSolution model, NodeType node, Zen<RouteType> route, IEnumerable<ISymbolic> symbolics) : CheckError
{
  public override void Report()
  {
    Console.WriteLine($"node check at {node}");
    Console.WriteLine($"node {node} has route := {model.Get(route)}");
    foreach (var sym in symbolics) Console.WriteLine($"symbolic {sym.Name} := {sym.GetSolution(model)}");
  }
}

public class EdgeError<NodeType, RouteType, NetworkType>(
  UntilChecker<NodeType, RouteType, NetworkType> checker,
  string kind,
  ZenSolution model,
  NodeType src,
  NodeType dst,
  Zen<RouteType> srcRoute,
  Zen<RouteType> dstRoute,
  Zen<RouteType> newDstRoute,
  IEnumerable<ISymbolic> symbolics) : CheckError
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
    foreach (var sym in symbolics)
      Console.WriteLine($"symbolic {sym.Name} := {sym.GetSolution(Model)}");
  }
}

public static class UntilCheckerExtension
{
  public static void Repair(
    this UntilChecker<string, RouteEnvironment, CiscoNetwork> checker,
    string task,
    CheckError err,
    TemplateArguments args)
  {
    EdgeError<string, RouteEnvironment, CiscoNetwork> error;
    try
    {
      error = (EdgeError<string, RouteEnvironment, CiscoNetwork>)err;
    }
    catch (InvalidCastException e)
    {
      throw new NotSupportedException($"error at {task} is not repairable");
    }

    var src = error.Src;
    var dst = error.Dest;
    var network = checker.Network;
    var config = network.Config;
    var constraint = network.Symbolics.Length != 0 ? Zen.And(network.Symbolics.Select(sym => sym.Encode())) : Zen.True();

    var exportPolicy = config.NodeConfigs[src].Polices[dst].ExportPolicy;
    var importPolicy = config.NodeConfigs[dst].Polices[src].ImportPolicy;
    Console.WriteLine($"export policy to be repaired:\n{exportPolicy.Debug()}");
    Console.WriteLine($"import policy to be repaired:\n{importPolicy.Debug()}");
    Console.WriteLine($"rank of src {src} is {error.Model.Get(checker.Ranks[src])}");
    Console.WriteLine($"rank of dst {dst} is {error.Model.Get(checker.Ranks[dst])}");

    var exportTemplate = exportPolicy.GenerateTemplate(args);
    var importTemplate = importPolicy.GenerateTemplate(args);

    List<(RouteEnvironment, RouteEnvironment)> counterExamples = [(error.SrcState, error.DstState)];
    Console.WriteLine($"counter example:\n  src {src} = {error.SrcState}\n  dst {dst} = {error.DstState}");

    for (int i = 0; i < args.MaxRetry; i++)
    {
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
        Console.Out.WriteLine("proposal generated");
        Console.Out.WriteLine($"export policy proposal:\n{exportProposal.Debug()}");
        Console.Out.WriteLine($"import policy proposal:\n{importProposal.Debug()}");

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
          Console.Out.WriteLine("proposal failed!");
          Console.Out.WriteLine($"failed model: {model.VariableAssignment}");
          Console.Out.WriteLine($"counterexample\n  src {src} = {model.Get(srcState)}\n  dst {dst} = {model.Get(dstState)}");
          counterExamples.Add((model.Get(srcState), model.Get(dstState)));
        }
        else
        {
          Console.Out.WriteLine("repair succeed!");
          Console.Out.WriteLine($"repaired import policy: {importProposal.Debug()}");
          Console.Out.WriteLine($"repaired export policy: {exportPolicy.Debug()}");
          Console.Out.WriteLine("----------------------");
          return;
        }
      }
      else
      {
        Console.Out.WriteLine("repair is impossible for this template");
        break;
      }
    }
    Console.Out.WriteLine("repair failed, sorry!");
    Console.Out.WriteLine("please try to change arguments of template generation");
  }

  public static void CheckAndRepair(
    this UntilChecker<string, RouteEnvironment, CiscoNetwork> checker,
    TemplateArguments args)
  {
    var errors = checker.Check();
    var globalTimer = Stopwatch.StartNew();
    var timeCollector = new Dictionary<string, long>(errors.Count);
    foreach (var p in errors)
    {
      var localTimer = Stopwatch.StartNew();
      Repair(checker, p.Key, p.Value, args);
      timeCollector[p.Key] = localTimer.ElapsedMilliseconds;
    }
    var wallTime = globalTimer.ElapsedMilliseconds;
    Console.WriteLine($"All repair tasks ended. Total time used: {wallTime} ms");
    StatisticsExtensions.ReportTimes(timeCollector, Statistics.Summary, wallTime, true);
  }
}
