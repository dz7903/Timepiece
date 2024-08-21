using System.Numerics;
using Timepiece;
using UntilChecker.Checker;
using UntilChecker.DataTypes;
using UntilChecker.IR;
using ZenLib;

namespace UntilChecker;

public static class Benchmark
{
  private static CiscoNetwork CreateNetwork(Configruation config)
  {
    return CiscoNetwork.StaticDest(config, "edge0_0",
      new SymbolicValue<RouteEnvironment>("destRoute",
        r => r == Zen.Constant(new RouteEnvironment()).WithResultValue(true)));
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Reach(Configruation config)
  {
    var network = CreateNetwork(config);
    var ranks = network.Digraph.BreadthFirstSearch("edge0_0")
      .ToDictionary(p => p.Key, p => Zen.Constant(p.Value));
    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      ranks,
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r => Zen.Not(r.GetResultValue())),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          Zen.And(
            r.GetResultValue(),
            r.GetWeight() == RouteEnvironment.DefaultWeight)));
    return checker;
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> ASLength(Configruation config)
  {
    var network = CreateNetwork(config);
    var ranks = network.Digraph.BreadthFirstSearch("edge0_0")
      .ToDictionary(p => p.Key, p => Zen.Constant(p.Value));
    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      ranks,
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r => Zen.Not(r.GetResultValue())),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          Zen.And(
            r.GetResultValue(),
            r.GetWeight() == RouteEnvironment.DefaultWeight,
            r.GetLp() == RouteEnvironment.DefaultLp,
            r.GetAsPathLength() == ranks[n]
          )));
    return checker;
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> ValleyFree(Configruation config)
  {
    var network = CreateNetwork(config);
    var bfs = network.Digraph.BreadthFirstSearch("edge0_0");
    var ranks = bfs.ToDictionary(p => p.Key, p => Zen.Constant(p.Value));
    var upNodes = network.Digraph.Nodes.Where(n =>
      bfs[n] == 1 || bfs[n] == 2 && n.StartsWith("core")).ToHashSet();

    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      ranks,
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r => Zen.Not(r.GetResultValue())),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          n == "edge0_0" || upNodes.Contains(n) ?
            Zen.And(
              r.GetResultValue(),
              r.GetWeight() == RouteEnvironment.DefaultWeight,
              r.GetLp() == RouteEnvironment.DefaultLp,
              r.GetAsPathLength() == ranks[n],
              Zen.Not(r.HasCommunity("1:0"))) :
            Zen.And(
              r.GetResultValue(),
              r.GetWeight() == RouteEnvironment.DefaultWeight,
              r.GetLp() == RouteEnvironment.DefaultLp,
              r.GetAsPathLength() == ranks[n],
              r.HasCommunity("1:0"))));
    return checker;
  }
}
