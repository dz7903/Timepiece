using System.Collections;
using System.Diagnostics;
using System.Numerics;
using Timepiece;
using Timepiece.Angler.Ast.AstExpr;
using Timepiece.DataTypes;
using UntilChecker.Checker;
using UntilChecker.DataTypes;
using UntilChecker.IR;
using ZenLib;

namespace UntilChecker;

public static class Benchmark
{
  private static CiscoNetwork CreateNetwork(Configruation config, string dest)
  {
    return CiscoNetwork.StaticDest(config, dest,
      new SymbolicValue<RouteEnvironment>("destRoute",
        r => r == Zen.Constant(new RouteEnvironment()).WithResultValue(true)));
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Reach(Configruation config)
  {
    var network = CreateNetwork(config, "edge0_0");
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
    var network = CreateNetwork(config, "edge0_0");
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
    var network = CreateNetwork(config, "edge0_0");
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

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Hijack( Configruation config)
  {
    var internalPrefix = new Ipv4Prefix("42.0.0.0/8");
    var destPrefix = new SymbolicValue<Ipv4Prefix>("destPrefix", prefix => internalPrefix.Matches(prefix, true));
    var hijackRoute = new SymbolicValue<RouteEnvironment>("hijackRoute", r => r.GetPrefix() == destPrefix.Value);
    var hijackAs = config.NodeConfigs["hijack"].LocalAs;

    var network = new CiscoNetwork(
      config,
      config.ToDigraph().MapNodes<Zen<RouteEnvironment>>(
        n => n switch
        {
          "hijack" => hijackRoute.Value,
          "edge0_0" => Zen.Constant(new RouteEnvironment()).WithResultValue(true).WithPrefix(destPrefix.Value),
          _ => Zen.Constant(new RouteEnvironment())
        }),
      [destPrefix, hijackRoute]);
    var ranks = network.Digraph.BreadthFirstSearch("edge0_0")
      .ToDictionary(p => p.Key, p => Zen.Constant(p.Value));

    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      ranks,
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          n == "hijack" ? Zen.Implies(r.GetResultValue(), r == hijackRoute.Value) : Zen.Not(r.GetResultValue())),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          n == "hijack" ? Zen.Implies(r.GetResultValue(), r == hijackRoute.Value) :
            Zen.And(
              r.GetResultValue(),
              Zen.Not(r.GetAsSet().Contains(hijackAs)))));

    return checker;
  }

  private static (Dictionary<string, int>, HashSet<string>, HashSet<string>, HashSet<(string, string)>) WanBFS(Configruation config, string dest)
  {
    var dag = new HashSet<(string, string)>();
    var uphill = new HashSet<string> { dest };
    var downhill = new HashSet<string>();
    var dist = new Dictionary<string, int> { {dest, 0} };
    var q = new Queue<string>();
    q.Enqueue(dest);
    while (q.Count > 0)
    {
      var node = q.Dequeue();
      var d = dist[node];
      foreach (var (neighbor, policy) in config.NodeConfigs[node].Polices)
        if (uphill.Contains(node) && policy.ImportPolicy[0].MapName.StartsWith("prov"))
        {
          if (uphill.Contains(neighbor)) continue;
          if (downhill.Contains(neighbor))
          {
            if (dist[neighbor] == d + 1)
              Console.WriteLine($"WARNING: {neighbor} has both a up path and a down path to {dest} with same distance");
            continue;
          }
          uphill.Add(neighbor);
          dist[neighbor] = d + 1;
          dag.Add((node, neighbor));
          q.Enqueue(neighbor);
        }
        else if ((uphill.Contains(node) && policy.ImportPolicy[0].MapName.StartsWith("peer")) ||
                 policy.ImportPolicy[0].MapName.StartsWith("cust"))
        {
          if (downhill.Contains(neighbor)) continue;
          if (uphill.Contains(neighbor))
          {
            if (dist[neighbor] == d + 1)
              Console.WriteLine($"WARNING: {neighbor} has both a up path and a down path to {dest} with same distance");
            continue;
          }
          downhill.Add(neighbor);
          dist[neighbor] = d + 1;
          dag.Add((node, neighbor));
          q.Enqueue(neighbor);
        }
    }

    // Console.WriteLine("uphill:");
    // foreach (var node in uphill) Console.Write($"{node} ");
    // Console.WriteLine("\ndownhill:");
    // foreach (var node in downhill) Console.Write($"{node} ");
    // Console.WriteLine("\ndag:");
    // foreach (var (u, v) in dag) Console.Write($"({u}, {v}) ");
    // Console.WriteLine("\ndist:");
    // foreach (var p in dist) Console.Write($"({p.Key}, {p.Value})");
    // Console.WriteLine("\n\n");

    return (dist, uphill, downhill, dag);
  }

  public static UntilChecker<string, RouteEnvironment, CiscoNetwork> WanSingleDest(Configruation config, string dest)
  {
    var network = CreateNetwork(config, dest);
    var (dist, uphill, downhill, dag) = WanBFS(config, dest);
    // var ranks = network.Digraph.MapNodes(n =>
    //   uphill.Contains(n) ? Zen.Constant(new BigInteger(dist[n])) :
    //   downhill.Contains(n) ? Zen.Constant(new BigInteger(dist[n])) :
    //   BigInteger.Zero);
    var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
      network,
      network.Digraph.MapEdges(p => Zen.Constant(dag.Contains(p))),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          n == dest ? Zen.False() :
          uphill.Contains(n) ? Zen.Implies(
            r.GetResultValue(),
            Zen.And(
              r.GetWeight() == RouteEnvironment.DefaultWeight,
              r.GetLp() == RouteEnvironment.DefaultLp,
              r.GetAsPathLength() >= new BigInteger(dist[n]),
              Zen.Not(r.HasCommunity("1:1")))) :
          downhill.Contains(n) ? Zen.Implies(
            r.GetResultValue(),
            Zen.And(
              r.GetWeight() == RouteEnvironment.DefaultWeight,
              r.GetLp() == RouteEnvironment.DefaultLp,
              r.GetAsPathLength() >= new BigInteger(dist[n]),
              r.HasCommunity("1:1"))) :
          Zen.False()),
      network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
        n => r =>
          n == dest ? r == Zen.Constant(new RouteEnvironment()).WithResultValue(true) :
          uphill.Contains(n) ? Zen.And(
            r.GetResultValue(),
            r.GetWeight() == RouteEnvironment.DefaultWeight,
            r.GetLp() == RouteEnvironment.DefaultLp,
            r.GetAsPathLength() == new BigInteger(dist[n]),
            Zen.Not(r.HasCommunity("1:1"))) :
          downhill.Contains(n) ? Zen.And(
            r.GetResultValue(),
            r.GetWeight() == RouteEnvironment.DefaultWeight,
            r.GetLp() == RouteEnvironment.DefaultLp,
            r.GetAsPathLength() == new BigInteger(dist[n]),
            r.HasCommunity("1:1")) :
          Zen.Not(r.GetResultValue())));
    return checker;
  }

  // public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Wan(
  //   // Dictionary<string, int> uphill,
  //   // Dictionary<string, int> downhill,
  //   // HashSet<(string, string)> dag,
  //   Configruation config,
  //   List<string> dests)
  // {
  //   var bfs = dests.ToDictionary(d => d, d => WanBFS(config, d));
  //   var dest = new SymbolicValue<string>("dest",
  //     dest => ZenExtension.Or(dests.Select(d => dest == d)));
  //   var network = new CiscoNetwork(
  //     config,
  //     config.ToDigraph().MapNodes<Zen<RouteEnvironment>>(
  //       n => Zen.If(n == dest.Value, Zen.Constant(new RouteEnvironment()).WithResultValue(true), Zen.Constant(new RouteEnvironment()))),
  //     [dest]);
  //
  //   // var network = CreateNetwork(config, dest);
  //   var ranks = network.Digraph.MapNodes(n =>
  //     uphill.ContainsKey(n) ? Zen.Constant(new BigInteger(uphill[n])) :
  //     downhill.ContainsKey(n) ? Zen.Constant(new BigInteger(downhill[n])) :
  //     BigInteger.Zero);
  //   var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
  //     network,
  //     network.Digraph.MapEdges(p => Zen.Constant(dag.Contains(p))),
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         n == dest ? Zen.False() :
  //         uphill.ContainsKey(n) ? Zen.Implies(
  //           r.GetResultValue(),
  //           Zen.And(
  //             r.GetWeight() == RouteEnvironment.DefaultWeight,
  //             r.GetLp() == RouteEnvironment.DefaultLp,
  //             r.GetAsPathLength() >= new BigInteger(uphill[n]),
  //             Zen.Not(r.HasCommunity("1:1")))) :
  //         downhill.ContainsKey(n) ? Zen.Implies(
  //           r.GetResultValue(),
  //           Zen.And(
  //             r.GetWeight() == RouteEnvironment.DefaultWeight,
  //             r.GetLp() == RouteEnvironment.DefaultLp,
  //             r.GetAsPathLength() >= new BigInteger(downhill[n]),
  //             r.HasCommunity("1:1"))) :
  //         Zen.False()),
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         n == dest ? r == Zen.Constant(new RouteEnvironment()).WithResultValue(true) :
  //         uphill.ContainsKey(n) ? Zen.And(
  //           r.GetResultValue(),
  //           r.GetWeight() == RouteEnvironment.DefaultWeight,
  //           r.GetLp() == RouteEnvironment.DefaultLp,
  //           r.GetAsPathLength() == new BigInteger(uphill[n]),
  //           Zen.Not(r.HasCommunity("1:1"))) :
  //         downhill.ContainsKey(n) ? Zen.And(
  //           r.GetResultValue(),
  //           r.GetWeight() == RouteEnvironment.DefaultWeight,
  //           r.GetLp() == RouteEnvironment.DefaultLp,
  //           r.GetAsPathLength() == new BigInteger(downhill[n]),
  //           r.HasCommunity("1:1")) :
  //         Zen.Not(r.GetResultValue())));
  //   return checker;
  // }

}
