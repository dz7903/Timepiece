using System.Diagnostics;
using Newtonsoft.Json;
using UntilChecker;
using Timepiece;
using UntilChecker.Checker;
using UntilChecker.DataTypes;
using UntilChecker.IR;
using ZenLib;

namespace UntilChecker.tests;

public class Tests
{
  private static void TopoSort(Digraph<string> graph, HashSet<(string, string)> cb)
  {
    var deg = new Dictionary<string, int>();
    foreach (var node in graph.Nodes)
      deg[node] = 0;
    foreach (var (_, node) in cb)
      deg[node] += 1;
    var q = new Queue<string>();
    foreach (var p in deg)
      if (p.Value == 0)
        q.Enqueue(p.Key);
    int count = 0;
    while (q.Count > 0)
    {
      var node = q.Dequeue();
      count++;
      foreach (var neighbor in graph[node])
      {
        deg[neighbor] -= 1;
        if (deg[neighbor] == 0)
          q.Enqueue(neighbor);
      }
    }
    Assert.That(graph.NNodes, Is.EqualTo(count));
  }

  private static long TestStatic(Digraph<string> graph)
  {
    long time = 0;
    foreach (var node in graph.Nodes)
      if (node.StartsWith("edge"))
      {
        var bfs = graph.BreadthFirstSearch(node);
        var cb = graph.Edges(p => bfs[p.Item1] < bfs[p.Item2]).ToHashSet();
        var timer = Stopwatch.StartNew();
        TopoSort(graph, cb);
        time += timer.ElapsedMilliseconds;
      }
    return time;
  }

  private static long TestSymbolic(Configruation config)
  {
    var checker = Benchmark.ReachSymbolic(config);
    var sym = Zen.Symbolic<Pair<string, int>>("sym");
    var acc = checker.Network.Digraph.MapNodes(node => Zen.Symbolic<bool>($"acc-{node}"));
    var check = Zen.And(checker.Network.Constraint(sym), Zen.Not(checker.DagCheckCondition(acc, sym)));
    var timer = Stopwatch.StartNew();
    Assert.That(!check.Solve().IsSatisfiable());
    return timer.ElapsedMilliseconds;
  }

  [Test]
  public static void TestDag()
  {
    var reader = new JsonTextReader(new StreamReader("../fattree20.cisco.json"));
    var serializer = new JsonSerializer();
    var config = new Configruation(serializer.Deserialize<Dictionary<string, Node>>(reader));
    var graph = config.ToDigraph();
    Console.WriteLine($"Test static destination: {TestStatic(graph)} ms in total");
    Console.WriteLine($"Test symbolic destination: {TestSymbolic(config)} ms in total");
    Assert.Pass();
  }
}
