using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using Timepiece.Networks;
using ZenLib;

namespace Timepiece;

public static class Profile
{
  /// <summary>
  /// Run verification for the given network and print the resulting times for comparison
  /// of Minesweeper-style versus Timepiece-style.
  /// </summary>
  /// <param name="network"></param>
  /// <typeparam name="T"></typeparam>
  /// <typeparam name="TS"></typeparam>
  public static void RunCmp<T, TS>(Network<T, TS> network)
  {
    RunMonoWithStats(network);

    Console.WriteLine($"Modular verification took {Time(RunAnnotated, network)}ms");
  }

  public static void RunCmpPerNode<T, TS>(Network<T, TS> network)
  {
    RunMonoWithStats(network);
    RunAnnotatedWithStats(network);
  }

  public static void RunMonoWithStats<T, TS>(Network<T, TS> network)
  {
    Console.WriteLine($"Monolithic verification took {Time(RunMono, network)}ms");
  }

  public static void RunMono<T, TS>(Network<T, TS> network)
  {
    try
    {
      var s = network.CheckMonolithic();
      if (!s.HasValue) return;
      s.Value.ReportCheckFailure();
      Console.WriteLine("Error, monolithic verification failed!");
    }
    catch (ZenException e)
    {
      Console.WriteLine("Error, monolithic verification did not complete:");
      Console.WriteLine(e.Message);
    }
  }

  public static void RunAnnotatedWithStats<T, TS>(Network<T, TS> network)
  {
    var processes = Environment.ProcessorCount;
    Console.WriteLine($"Environment.ProcessorCount: {processes}");
    var numNodes = network.Topology.Nodes.Length;
    var nodeTimes = new ConcurrentDictionary<string, long>(processes * 2, numNodes);
    try
    {
      var t = Time(net =>
      {
        var s = net.CheckAnnotationsWith(nodeTimes, LogCheckTime);
        var passed = true;
        var failedNodes = new List<string>();
        foreach (var (node, counterexample) in s)
        {
          if (!counterexample.HasValue) continue;
          passed = false;
          failedNodes.Add(node);
          Console.WriteLine($"    Counterexample for node {node}:");
          counterexample.Value.ReportCheckFailure();
          Console.WriteLine();
        }

        if (passed)
        {
          Console.WriteLine("    All the modular checks passed!");
          return;
        }

        Console.WriteLine("Error, unsound annotations provided or assertions failed!");
        var allFailed = failedNodes.Aggregate(new StringBuilder(), (builder, n) => builder.Append($" {n}"));
        Console.WriteLine(
          $"Counterexamples occurred at nodes:{allFailed}");
      }, network);
      Console.WriteLine($"Modular verification took {t}ms");
    }
    catch (ZenException e)
    {
      Console.WriteLine("Error, modular verification did not complete:");
      Console.WriteLine(e.Message);
    }
    finally
    {
      if (!nodeTimes.IsEmpty) ReportCheckTimes(nodeTimes, Statistics.Summary);
    }
  }

  public static void RunAnnotated<T, TS>(Network<T, TS> network)
  {
    var s = network.CheckAnnotations();
    if (!s.HasValue)
    {
      Console.WriteLine("    All the modular checks passed!");
      return;
    }

    s.Value.ReportCheckFailure();
    Console.WriteLine("Error, unsound annotations provided or assertions failed!");
  }

  private static long Time<T, TS>(Action<Network<T, TS>> f, Network<T, TS> network)
  {
    var timer = Stopwatch.StartNew();
    f(network);
    return timer.ElapsedMilliseconds;
  }

  public static Option<State<T, TS>> LogCheckTime<T, TS>(string node,
    IDictionary<string, long> times,
    Func<Option<State<T, TS>>> checkFunction)
  {
    var timer = Stopwatch.StartNew();
    var s = checkFunction();
    // add the time to the dictionary
    times.Add(node, timer.ElapsedMilliseconds);
    return s;
  }

  /// <summary>
  /// Available statistics to query on modular checks.
  /// </summary>
  [Flags]
  private enum Statistics
  {
    None = 0,
    Maximum = 1 << 0,
    Minimum = 1 << 1,
    Average = 1 << 2,
    Median = 1 << 3,
    NinetyNinthPercentile = 1 << 4,
    Total = 1 << 5,
    Individual = 1 << 6,
    Summary = Maximum | Minimum | Average | Median | NinetyNinthPercentile | Total,
    All = Summary | Individual
  }

  /// <summary>
  /// Report the time taken by all the checks.
  /// </summary>
  /// <param name="times"></param>
  /// <param name="stats"></param>
  /// <exception cref="ArgumentOutOfRangeException"></exception>
  private static void ReportCheckTimes(IDictionary<string, long> times, Statistics stats)
  {
    Console.WriteLine("Check statistics:");
    foreach (Statistics stat in Enum.GetValues(typeof(Statistics)))
    {
      if ((stats & stat) == stat)
      {
        switch (stat)
        {
          case Statistics.Maximum:
            var (maxNode, maxTime) = times.MaxBy(p => p.Value);
            Console.WriteLine($"Maximum check time: node {maxNode} in {maxTime}ms");
            break;
          case Statistics.Minimum:
            var (minNode, minTime) = times.MinBy(p => p.Value);
            Console.WriteLine($"Minimum check time: node {minNode} in {minTime}ms");
            break;
          case Statistics.Average:
            var avg = times.Average(p => p.Value);
            Console.WriteLine($"Average check time: {avg}ms");
            break;
          case Statistics.Median:
            var midpoint = times.Count / 2;
            var (medianNode, medianTime) = times.OrderBy(p => p.Value).ElementAt(midpoint);
            Console.WriteLine($"Median check time: node {medianNode} in {medianTime}ms");
            break;
          case Statistics.NinetyNinthPercentile:
            var ninetyNinth = (int) (times.Count * 0.99);
            var (ninetyNinthNode, ninetyNinthTime) = times.OrderBy(p => p.Value).ElementAt(ninetyNinth);
            Console.WriteLine($"99th percentile check time: node {ninetyNinthNode} in {ninetyNinthTime}ms");
            break;
          case Statistics.Total:
            var total = times.Sum(p => p.Value);
            Console.WriteLine($"Total check time: {total}ms");
            break;
          case Statistics.Individual:
            foreach (var (node, time) in times)
            {
              Console.WriteLine($"Node {node} took {time}ms");
            }

            break;
          case Statistics.None:
          case Statistics.Summary:
          case Statistics.All:
            break;
          default:
            throw new ArgumentOutOfRangeException(nameof(stats));
        }
      }
    }
  }
}
