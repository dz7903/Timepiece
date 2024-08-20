using System.Numerics;
using Timepiece;
using UntilChecker.Checker;
using UntilChecker.DataTypes;
using UntilChecker.IR;
using ZenLib;

namespace UntilChecker;

public static class Benchmark
{
  private static (CiscoNetwork, Dictionary<string, Zen<BigInteger>>) CreateNetwork(Configruation config)
  {
    var network = CiscoNetwork.StaticDest(config, "edge0_0",
      new SymbolicValue<RouteEnvironment>("destRoute",
        r => r == Zen.Constant(new RouteEnvironment()).WithResultValue(true)));
    var ranks = network.Digraph.BreadthFirstSearch("edge0_0").ToDictionary(p => p.Key, p => Zen.Constant(p.Value));
    return (network, ranks);
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Reach(Configruation config)
  {
    var (network, ranks) = CreateNetwork(config);
    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      ranks,
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r => Zen.Not(r.GetResultValue())),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          Zen.And(
            r.GetResultValue(),
            r.GetWeight() == RouteEnvironment.DefaultWeight
            )));
    return checker;
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> ASLength(Configruation config)
  {
    var (network, ranks) = CreateNetwork(config);
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
}
