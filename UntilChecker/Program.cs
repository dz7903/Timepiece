using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.CommandLine;
using System.Diagnostics;
using System.Numerics;
using Newtonsoft.Json;
using Timepiece;
using UntilChecker;
using UntilChecker.Checker;
using UntilChecker.IR;

Console.WriteLine("Hello, World!");
var rootCommand = new RootCommand("UntilChecker benchmark");

var fileArgument = new Argument<string>(
  "file",
  "The .cisco.json file to use");
var benchArgument = new Argument<string>(
  "bench",
  "The name of benchmark");
var noRepairOption = new Option<bool>(
  ["--no-repair"],
  "check without any repair");
var quietOption = new Option<bool>(
  ["-q", "--quiet"]);

rootCommand.AddArgument(fileArgument);
rootCommand.AddArgument(benchArgument);
rootCommand.AddOption(noRepairOption);
rootCommand.AddOption(quietOption);

rootCommand.SetHandler(
  (file, bench, noRepair, quiet) =>
  {
    var reader = new JsonTextReader(new StreamReader(file));
    var serializer = new JsonSerializer();
    var config = new Configruation(
      serializer.Deserialize<Dictionary<string, Node>>(reader) ?? throw new FormatException($"failed to deserialize {file}"));

    var checker = bench switch {
      "reach" => Benchmark.Reach(config),
      "aslength" => Benchmark.ASLength(config),
      "vf" => Benchmark.ValleyFree(config),
      "hijack" => Benchmark.Hijack(config),
      _ => throw new ArgumentException($"no benchmark named {bench}")
    };

    var args = new TemplateArguments(5, ["1:0", "1:1", "1:2"], 2, 0, 2);
    if (noRepair)
      checker.Check(quiet);
    else
      checker.CheckAndRepair(args, quiet);
  }, fileArgument, benchArgument, noRepairOption, quietOption);

rootCommand.Invoke(args);
