using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.CommandLine;
using System.Diagnostics;
using System.Numerics;
using Newtonsoft.Json;
using Timepiece;
using UntilChecker;
using UntilChecker.Checker;
using UntilChecker.DataTypes;
using UntilChecker.IR;

Console.WriteLine("Hello, World!");
var rootCommand = new RootCommand("UntilChecker benchmark");

var fileArgument = new Argument<string>(
  "file",
  "The .cisco.json file to use");
var benchArgument = new Argument<string>(
  "bench",
  "The name of benchmark");
var destArgument = new Argument<List<string>>(
  "dest",
  "Destinations for verification");
var noRepairOption = new Option<bool>(
  ["--no-repair"],
  "check without any repair");
var quietOption = new Option<bool>(
  ["-q", "--quiet"]);

rootCommand.AddArgument(fileArgument);
rootCommand.AddArgument(benchArgument);
rootCommand.AddArgument(destArgument);
rootCommand.AddOption(noRepairOption);
rootCommand.AddOption(quietOption);

rootCommand.SetHandler(
  (file, bench, dests, noRepair, quiet) =>
  {
    var reader = new JsonTextReader(new StreamReader(file));
    var serializer = new JsonSerializer();
    var config = new Configruation(
      serializer.Deserialize<Dictionary<string, Node>>(reader) ?? throw new FormatException($"failed to deserialize {file}"));

    var args = new TemplateArguments(5, ["1:0", "1:1", "1:2"], 2, 2, 2);

    switch (bench)
    {
      case "reach":
      {
        var checker = Benchmark.Reach(config, dests);
        checker.CheckAndRepair(args, quiet, noRepair);
        break;
      }

      case "aslength":
      {
        var checker = Benchmark.AsLength(config, dests);
        checker.CheckAndRepair(args, quiet, noRepair);
        break;
      }

      case "vf":
      {
        var checker = Benchmark.ValleyFree(config, dests);
        checker.CheckAndRepair(args, quiet, noRepair);
        break;
      }

      case "hijack":
      {
        var checker = Benchmark.Hijack(config, dests);
        checker.CheckAndRepair(args, quiet, noRepair);
        break;
      }

      case "reach-symbolic":
      {
        var checker = Benchmark.ReachSymbolic(config);
        checker.CheckAndRepair(args, quiet, noRepair);
        break;
      }

      default:
        throw new ArgumentException($"no benchmark called {bench}");
    }
    
  }, fileArgument, benchArgument, destArgument, noRepairOption, quietOption);

rootCommand.Invoke(args);
