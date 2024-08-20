using Timepiece;
using ZenLib;
using UntilChecker.IR;
using UntilChecker.DataTypes;

namespace UntilChecker.Checker;

public class Network<NodeType, RouteType>(
  Digraph<NodeType> digraph,
  IDictionary<NodeType, Zen<RouteType>> initialRoutes,
  IDictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> transferFunctions,
  Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> mergeFunction,
  ISymbolic[] symbolics) where NodeType: notnull
{
  public readonly Digraph<NodeType> Digraph = digraph;
  public readonly IDictionary<NodeType, Zen<RouteType>> InitialRoutes = initialRoutes;
  public readonly IDictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> TransferFunctions = transferFunctions;
  public readonly Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> MergeFunction = mergeFunction;
  public readonly ISymbolic[] Symbolics = symbolics;
}

public class CiscoNetwork(
  Configruation config,
  IDictionary<string, Zen<RouteEnvironment>> initialRoutes,
  ISymbolic[] symbolics
) : Network<string, RouteEnvironment>(
   config.ToDigraph(),
   initialRoutes,
   config.ToDigraph().MapEdges<Func<Zen<RouteEnvironment>, Zen<RouteEnvironment>>>(
     p => r => config.TransferFunction(p.Item1, p.Item2, r)),
   RouteEnvironmentExtensions.MinOptional,
   symbolics)
{
  public readonly Configruation Config = config;

  public static CiscoNetwork StaticDest(Configruation config, string dest, SymbolicValue<RouteEnvironment> symDestInit)
  {
    return new CiscoNetwork(
      config,
      config.ToDigraph().MapNodes(
        n => n == dest ? symDestInit.Value : Zen.Constant(new RouteEnvironment())),
      [symDestInit]);
  }

  public static CiscoNetwork DynamicDest(Configruation config, SymbolicValue<RouteEnvironment> symDestInit)
  {
    var digraph = config.ToDigraph();
    var symDest = new SymbolicValue<string>("dest", dest => Zen.Or(digraph.Nodes.Select(n => n == dest)));
    return new CiscoNetwork(
      config,
      digraph.MapNodes(n => Zen.If(n == symDest.Value, symDestInit.Value, Zen.Constant(new RouteEnvironment()))),
      [symDest, symDestInit]);
  }
}

