using System.Collections.Concurrent;
using System.Diagnostics;
using Timepiece;
using ZenLib;

namespace UntilChecker.Checker;


public abstract class Checker<NodeType, RouteType, NetworkType>(NetworkType network)
  where NodeType : notnull
  where NetworkType : Network<NodeType, RouteType>
{
  public readonly NetworkType Network = network;

  protected abstract IDictionary<string, Func<Option<CheckError>>> GenerateTasks();

  public IDictionary<string, CheckError> Check()
  {
    var processes = Environment.ProcessorCount;
    Trace.WriteLine($"Environment.ProcessorCount: {processes}");
    var tasks = GenerateTasks();
    Trace.WriteLine($"{tasks.Count} tasks generated.");
    var timeCollector = new ConcurrentDictionary<string, long>(processes * 2, tasks.Count);
    var errorCollector = new ConcurrentDictionary<string, CheckError>(processes * 2, tasks.Count);

    var globalTimer = Stopwatch.StartNew();
    Parallel.ForEach(tasks, p =>
    {
      var localTimer = Stopwatch.StartNew();
      var result = p.Value();
      timeCollector[p.Key] = localTimer.ElapsedMilliseconds;
      if (result.IsSome())
        errorCollector[p.Key] = result.Value;
    });
    var wallTime = globalTimer.ElapsedMilliseconds;
    Console.WriteLine($"All tasks ended. Total time used: {wallTime} ms");
    StatisticsExtensions.ReportTimes(timeCollector, Statistics.Summary, wallTime, true);

    if (errorCollector.IsEmpty)
      Console.WriteLine("All tasks passed. Congrats!");
    else
    {
      Console.WriteLine($"{errorCollector.Count} tasks failed.");
      foreach (var (task, err) in errorCollector)
      {
        Console.WriteLine($"task {task} failed");
        err.Report();
        Console.WriteLine();
      }
    }
    return errorCollector;
  }
}

public abstract class CheckError
{
  public abstract void Report();
}
