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
  public static UntilChecker<string, BgpRoute, string, CiscoNetwork<string>> Reach(
    Configruation config, List<string> destinations)
  {
    if (destinations.Count == 0) destinations = ["edge0_0"];

    var network = new CiscoNetwork<string>(
      config,
      (n, dest) => Zen.If<BgpRoute>(n == dest, BgpRoute.DefaultRoute(), BgpRoute.NoRoute()),
      dest => ZenExtension.Or(destinations.Select(d => d == dest)));

    var bfs = destinations.ToDictionary(d => d,
      d => network.Digraph.BreadthFirstSearch(d));
    var cb = destinations.ToDictionary(d => d,
      d => network.Digraph.Edges(p => bfs[d][p.Item1] < bfs[d][p.Item2]).ToHashSet());

    var checker = new UntilChecker<string, BgpRoute, string, CiscoNetwork<string>>(
      network,
      (src, dst, sym) => cb.Aggregate(
        Zen.False(),
        (b, p) =>
          Zen.If(sym == p.Key, p.Value.Contains((src, dst)), b)),
      (n, r, _) => Zen.True(),
      (n, r, _) => r.IsValid());
    return checker;
  }

  public static UntilChecker<string, BgpRoute, string, CiscoNetwork<string>> AsLength(
    Configruation config, List<string> destinations)
  {
    if (destinations.Count == 0) destinations = ["edge0_0"];

    var network = new CiscoNetwork<string>(
      config,
      (n, dest) => Zen.If<BgpRoute>(n == dest, BgpRoute.DefaultRoute(), BgpRoute.NoRoute()),
      dest => ZenExtension.Or(destinations.Select(d => d == dest)));

    var bfs = destinations.ToDictionary(d => d,
      d => network.Digraph.BreadthFirstSearch(d));
    var cb = destinations.ToDictionary(d => d,
      d => network.Digraph.Edges(p => bfs[d][p.Item1] < bfs[d][p.Item2]).ToHashSet());
    var dist = (string n, Zen<string> sym) =>
      destinations.Aggregate(Zen.Constant(BigInteger.Zero),
        (d, dest) => Zen.If(sym == dest, bfs[dest][n], d));

    var checker = new UntilChecker<string, BgpRoute, string, CiscoNetwork<string>>(
      network,
      (src, dst, sym) => cb.Aggregate(
        Zen.False(),
        (b, p) =>
          Zen.If(sym == p.Key, p.Value.Contains((src, dst)), b)),
      (n, r, sym) =>
        Zen.Implies(r.IsValid(),
          Zen.And(
            r.GetLp() == RouteEnvironment.DefaultLp,
            r.GetAsLength() >= dist(n, sym))),
      (n, r, sym) =>
        Zen.And(
          r.IsValid(),
          r.GetLp() == RouteEnvironment.DefaultLp,
          r.GetAsLength() == dist(n, sym)));
    return checker;
  }

  public static UntilChecker<string, BgpRoute, string, CiscoNetwork<string>> ValleyFree(
    Configruation config, List<string> destinations)
  {
    if (destinations.Count == 0) destinations = ["edge0_0"];

    var network = new CiscoNetwork<string>(
      config,
      (n, dest) => Zen.If<BgpRoute>(n == dest, BgpRoute.DefaultRoute(), BgpRoute.NoRoute()),
      dest => ZenExtension.Or(destinations.Select(d => d == dest)));

    var bfs = destinations.ToDictionary(d => d,
      d => network.Digraph.BreadthFirstSearch(d));
    var cb = destinations.ToDictionary(d => d,
      d => network.Digraph.Edges(p => bfs[d][p.Item1] < bfs[d][p.Item2]).ToHashSet());
    var dist = (string n, Zen<string> sym) =>
      destinations.Aggregate(Zen.Constant(BigInteger.Zero),
        (d, dest) => Zen.If(sym == dest, bfs[dest][n], d));
    var uphill = (string n, Zen<string> sym) =>
      destinations.Aggregate(Zen.False(),
        (b, dest) => Zen.If(
          sym == dest,
          bfs[dest][n] <= 1 || bfs[dest][n] == 2 && n.StartsWith("core"),
          b));

    var checker = new UntilChecker<string, BgpRoute, string, CiscoNetwork<string>>(
      network,
      (src, dst, sym) => cb.Aggregate(
        Zen.False(),
        (b, p) =>
          Zen.If(sym == p.Key, p.Value.Contains((src, dst)), b)),
      (n, r, sym) =>
        Zen.Implies(r.IsValid(),
          Zen.And(
            r.GetLp() == RouteEnvironment.DefaultLp,
            r.GetAsLength() > dist(n, sym))),
      (n, r, sym) =>
        Zen.And(
          r.IsValid(),
          r.GetLp() == RouteEnvironment.DefaultLp,
          r.GetAsLength() == dist(n, sym),
          Zen.If(uphill(n, sym), Zen.Not(r.HasCommunity("1:0")), r.HasCommunity("1:0"))));
    return checker;
  }

  public static UntilChecker<string, BgpRoute, Pair<string, BgpRoute>, CiscoNetwork<Pair<string, BgpRoute>>> Hijack(
    Configruation config, List<string> destinations)
  {
    if (destinations.Count == 0) destinations = ["edge0_0"];
    var internalPrefix = new Ipv4Prefix("42.0.0.0/8");
    // var destPrefix = new SymbolicValue<Ipv4Prefix>("destPrefix", prefix => internalPrefix.Matches(prefix, true));
    // var hijackRoute = new SymbolicValue<BgpRoute>("hijackRoute", r => r.GetPrefix() == destPrefix.Value);
    var hijackAs = config.NodeConfigs["hijack"].LocalAs;

    // (destination, hijackRoute)
    var network = new CiscoNetwork<Pair<string, BgpRoute>>(
      config,
      (n, sym) =>
        n == "hijack" ? sym.Item2() :
          Zen.If<BgpRoute>(
            n == sym.Item1(),
            Zen.Constant(BgpRoute.DefaultRoute()).WithPrefix(sym.Item2().GetPrefix()),
            BgpRoute.NoRoute()),
      sym =>
        Zen.And(
          ZenExtension.Or(destinations.Select(d => d == sym.Item1())),
          sym.Item2().IsValid(),
          Zen.If(
            sym.Item1() == "hijack",
            Zen.Not(internalPrefix.Matches(sym.Item2().GetPrefix(), true)),
            internalPrefix.Matches(sym.Item2().GetPrefix(), true))));

    var bfs = destinations.ToDictionary(d => d,
      d => network.Digraph.BreadthFirstSearch(d));
    var cb = destinations.ToDictionary(d => d,
      d =>
        d == "hijack"?
          network.Digraph.Edges(p => bfs[d][p.Item1] < bfs[d][p.Item2]).ToHashSet() :
          network.Digraph.Edges(p => p.Item1 != "hijack" && p.Item2 != "hijack" && bfs[d][p.Item1] < bfs[d][p.Item2]).ToHashSet());

    var checker = new UntilChecker<string, BgpRoute, Pair<string, BgpRoute>, CiscoNetwork<Pair<string, BgpRoute>>>(
      network,
      (src, dst, sym) => cb.Aggregate(
        Zen.False(),
        (b, p) =>
          Zen.If(sym.Item1() == p.Key, p.Value.Contains((src, dst)), b)),
      (n, r, sym) =>
        n == "hijack" ? Zen.False() :
          Zen.Implies(
            Zen.And(r.IsValid(), sym.Item1() != "hijack"),
            Zen.Not(r.HasAs(hijackAs))),
      (n, r, sym) =>
        n == "hijack" ?
          Zen.And(
            r.IsValid(),
            Zen.If(
              sym.Item1() == "hijack",
              Zen.Not(internalPrefix.Matches(r.GetPrefix(), true)),
              internalPrefix.Matches(r.GetPrefix(), true))) :
          Zen.And(
            r.IsValid(),
            Zen.Implies(
              sym.Item1() != "hijack",
              Zen.Not(r.HasAs(hijackAs)))));
    return checker;
  }



  private static int Pod(string n) =>
    n.StartsWith("core") ? -1 : int.Parse(n[4..n.IndexOf('_')]);

  private static Zen<bool> Constraint(Configruation config, Zen<string> dest, Zen<int> destPod) =>
    ZenExtension.Or(config.NodeConfigs.Keys
      .Where(node => node.StartsWith("edge"))
      .Select(node => Zen.And(dest == node, destPod == Pod(node))));

  private static Zen<bool> ConvergeBefore(string node1, string node2, Zen<string> dest, Zen<int> destPod)
  {
    var pod1 = Pod(node1);
    var pod2 = Pod(node2);
    return Zen.Or(
      Zen.And(node1 == dest, node2.StartsWith("aggr"), pod1 == pod2),
      Zen.And(pod1 == destPod, pod1 == pod2, node1.StartsWith("aggr"), node2.StartsWith("edge"), node2 != dest),
      Zen.And(pod1 == destPod, node1.StartsWith("aggr"), node2.StartsWith("core")),
      Zen.And(pod2 != destPod, node1.StartsWith("core"), node2.StartsWith("aggr")),
      Zen.And(pod1 != destPod, pod1 == pod2, node1.StartsWith("aggr"), node2.StartsWith("edge")));
  }

  private static Zen<BigInteger> Distance(string node, Zen<string> dest, Zen<int> destPod)
  {
    var pod = Pod(node);
    return Zen.If(
      node == dest, BigInteger.Zero,
      Zen.If(
        Zen.And(node.StartsWith("aggr"), pod == destPod), BigInteger.One,
        Zen.If(
          node.StartsWith("core"), new BigInteger(2),
          Zen.If<BigInteger>(
            Zen.And(node.StartsWith("edge"), pod == destPod), new BigInteger(2),
            node.StartsWith("aggr") ? new BigInteger(3) : new BigInteger(4)))));
  }

  private static Zen<BgpRoute> InitialRoute(string node, Zen<string> dest) =>
    Zen.If<BgpRoute>(node == dest, BgpRoute.DefaultRoute(), BgpRoute.NoRoute());

  public static UntilChecker<string, BgpRoute, Pair<string, int>, CiscoNetwork<Pair<string, int>>> ReachSymbolic(
    Configruation config)
  {
    var network = new CiscoNetwork<Pair<string, int>>(
      config,
      (node, sym) => InitialRoute(node, sym.Item1()),
      sym => Constraint(config, sym.Item1(), sym.Item2()));

    var checker = new UntilChecker<string, BgpRoute, Pair<string, int>, CiscoNetwork<Pair<string, int>>>(
      network,
      (src, dst, sym) => ConvergeBefore(src, dst, sym.Item1(), sym.Item2()),
      (n, r, _) => Zen.True(),
      (n, r, _) => r.IsValid());
    return checker;
  }

  // public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Hijack(
  //   Configruation config, List<string> dests)
  // {
  //   var internalPrefix = new Ipv4Prefix("42.0.0.0/8");
  //   var destPrefix = new SymbolicValue<Ipv4Prefix>("destPrefix", prefix => internalPrefix.Matches(prefix, true));
  //   var hijackRoute = new SymbolicValue<RouteEnvironment>("hijackRoute", r => r.GetPrefix() == destPrefix.Value);
  //   var hijackAs = config.NodeConfigs["hijack"].LocalAs;
  //
  //   if (dests.Count == 0) dests = ["edge0_0"];
  //   var symDest = SymbolicDest(dests);
  //   var network = new CiscoNetwork(
  //     config,
  //     config.ToDigraph().MapNodes<Zen<RouteEnvironment>>(
  //       n => n == "hijack" ? hijackRoute.Value : Zen.If(symDest.Value == n, DefaultRoute(), NoRoute())),
  //     [destPrefix, hijackRoute]);
  //   var cb = ConvergeBefore(network, dests);
  //
  //   var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
  //     network,
  //     symDest.Value,
  //     cb,
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         n == "hijack" ? Zen.Implies(r.GetResultValue(), r == hijackRoute.Value) :
  //           Zen.Implies(
  //             r.GetResultValue(),
  //             Zen.Not(r.GetAsSet().Contains(hijackAs))
  //             )),
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         n == "hijack" ? Zen.Implies(r.GetResultValue(), r == hijackRoute.Value) :
  //           Zen.And(
  //             r.GetResultValue(),
  //             Zen.Not(r.GetAsSet().Contains(hijackAs)))));
  //
  //   return checker;
  // }
  //
  // private static (Dictionary<string, int>, HashSet<string>, HashSet<string>, HashSet<(string, string)>) WanBFS(Configruation config, string dest)
  // {
  //   var dag = new HashSet<(string, string)>();
  //   var uphill = new HashSet<string> { dest };
  //   var downhill = new HashSet<string>();
  //   var dist = new Dictionary<string, int> { {dest, 0} };
  //   var q = new Queue<string>();
  //   q.Enqueue(dest);
  //   while (q.Count > 0)
  //   {
  //     var node = q.Dequeue();
  //     var d = dist[node];
  //     foreach (var (neighbor, policy) in config.NodeConfigs[node].Polices)
  //       if (uphill.Contains(node) && policy.ImportPolicy[0].MapName.StartsWith("prov"))
  //       {
  //         if (uphill.Contains(neighbor)) continue;
  //         if (downhill.Contains(neighbor))
  //         {
  //           if (dist[neighbor] == d + 1)
  //             Console.WriteLine($"WARNING: {neighbor} has both a up path and a down path to {dest} with same distance");
  //           continue;
  //         }
  //         uphill.Add(neighbor);
  //         dist[neighbor] = d + 1;
  //         dag.Add((node, neighbor));
  //         q.Enqueue(neighbor);
  //       }
  //       else if ((uphill.Contains(node) && policy.ImportPolicy[0].MapName.StartsWith("peer")) ||
  //                policy.ImportPolicy[0].MapName.StartsWith("cust"))
  //       {
  //         if (downhill.Contains(neighbor)) continue;
  //         if (uphill.Contains(neighbor))
  //         {
  //           if (dist[neighbor] == d + 1)
  //             Console.WriteLine($"WARNING: {neighbor} has both a up path and a down path to {dest} with same distance");
  //           continue;
  //         }
  //         downhill.Add(neighbor);
  //         dist[neighbor] = d + 1;
  //         dag.Add((node, neighbor));
  //         q.Enqueue(neighbor);
  //       }
  //   }
  //
  //   // Console.WriteLine("uphill:");
  //   // foreach (var node in uphill) Console.Write($"{node} ");
  //   // Console.WriteLine("\ndownhill:");
  //   // foreach (var node in downhill) Console.Write($"{node} ");
  //   // Console.WriteLine("\ndag:");
  //   // foreach (var (u, v) in dag) Console.Write($"({u}, {v}) ");
  //   // Console.WriteLine("\ndist:");
  //   // foreach (var p in dist) Console.Write($"({p.Key}, {p.Value})");
  //   // Console.WriteLine("\n\n");
  //
  //   return (dist, uphill, downhill, dag);
  // }
  //
  // public static UntilChecker<string, RouteEnvironment, CiscoNetwork> Wan(Configruation config, List<string> dests)
  // {
  //   var symDest = SymbolicDest(dests);
  //   var network = CreateNetwork(config, dests, symDest);
  //   var bfs = dests.ToDictionary(dest => dest, dest => WanBFS(config, dest));
  //   var uphill = network.Digraph.MapNodes(n =>
  //     dests.Aggregate(Zen.False(), (b, dest) =>
  //       Zen.If(symDest.Value == dest, bfs[dest].Item2.Contains(n), b)));
  //   var downhill = network.Digraph.MapNodes(n =>
  //     dests.Aggregate(Zen.False(), (b, dest) =>
  //       Zen.If(symDest.Value == dest, bfs[dest].Item3.Contains(n), b)));
  //   var cb = dests.ToDictionary(dest => dest, dest =>
  //     network.Digraph.Edges(p => bfs[dest].Item4.Contains(p)).ToHashSet());
  //   var dist = network.Digraph.MapNodes(n =>
  //     dests.Aggregate(Zen.Constant(BigInteger.Zero), (d, dest) =>
  //       Zen.If(symDest.Value == dest, new BigInteger(bfs[dest].Item1[n]), d)));
  //
  //   var checker = new UntilChecker<string, RouteEnvironment, CiscoNetwork>(
  //     network,
  //     symDest.Value,
  //     cb,
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         Zen.If(
  //           n == symDest.Value,
  //           Zen.False(),
  //           Zen.If(
  //             uphill[n],
  //             Zen.Implies(
  //               r.GetResultValue(),
  //               Zen.And(
  //                 r.GetWeight() == RouteEnvironment.DefaultWeight,
  //                 r.GetLp() == RouteEnvironment.DefaultLp,
  //                 r.GetAsPathLength() >= dist[n],
  //                 Zen.Not(r.HasCommunity("1:1")))),
  //             Zen.If(
  //               downhill[n],
  //               Zen.Implies(
  //                 r.GetResultValue(),
  //                 Zen.And(
  //                   r.GetWeight() == RouteEnvironment.DefaultWeight,
  //                   r.GetLp() == RouteEnvironment.DefaultLp,
  //                   r.GetAsPathLength() >= dist[n],
  //                   r.HasCommunity("1:1"))),
  //               Zen.False())))),
  //     network.Digraph.MapNodes<Func<Zen<RouteEnvironment>, Zen<bool>>>(
  //       n => r =>
  //         Zen.If(
  //           n == symDest.Value,
  //           r == DefaultRoute(),
  //           Zen.If(
  //             uphill[n],
  //             Zen.And(
  //               r.GetResultValue(),
  //               r.GetWeight() == RouteEnvironment.DefaultWeight,
  //               r.GetLp() == RouteEnvironment.DefaultLp,
  //               r.GetAsPathLength() == dist[n],
  //               Zen.Not(r.HasCommunity("1:1"))),
  //             Zen.If(
  //               downhill[n],
  //               Zen.And(
  //                 r.GetResultValue(),
  //                 r.GetWeight() == RouteEnvironment.DefaultWeight,
  //                 r.GetLp() == RouteEnvironment.DefaultLp,
  //                 r.GetAsPathLength() == dist[n],
  //                 r.HasCommunity("1:1")),
  //               Zen.Not(r.GetResultValue()))))));
  //   return checker;
  // }

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
