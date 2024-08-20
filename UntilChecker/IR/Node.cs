using System.Collections.Immutable;
using System.Numerics;
using Newtonsoft.Json;
using Timepiece;
using ZenLib;
using UntilChecker.DataTypes;
using ZenLib.ModelChecking;

namespace UntilChecker.IR;

public record TemplateArguments(
  uint MaxRetry,
  IEnumerable<string> TagsCollection,
  int ExtraMatchLines,
  int ExtraSetLines,
  int ExtraClauses);

public record Template<TTransfer, TRep>(
  TTransfer TransferFunction,
  Zen<BigInteger> Cost,
  Zen<bool> Constraint,
  Func<ZenSolution, TRep> Repair);

public record Configruation (
  IDictionary<string, Node> NodeConfigs)
{
  public Zen<RouteEnvironment> TransferFunction(string src, string dst, Zen<RouteEnvironment> r)
  {
    var exportPolicy = NodeConfigs[src].Polices[dst].ExportPolicy;
    var importPolicy = NodeConfigs[dst].Polices[src].ImportPolicy;
    return importPolicy.Transfer(exportPolicy.Transfer(r))
      .IncrementAsPathLength(BigInteger.One)
      .AddAsSet(NodeConfigs[src].LocalAs);
  }

  public Digraph<string> ToDigraph()
  {
    return new Digraph<string>(
      NodeConfigs.Select(p =>
     new KeyValuePair<string, ImmutableSortedSet<string>>(p.Key, p.Value.Polices.Keys.ToImmutableSortedSet())));
  }
}

[method: JsonConstructor]
public record Node(
  [JsonProperty("address", Required = Required.Always)]
  string Address,
  [JsonProperty("localAs", Required = Required.Always)]
  uint LocalAs,

  [JsonProperty("policies")] Dictionary<string, Policy> Polices
);

[method: JsonConstructor]
public record Policy(
  [JsonProperty("import", Required = Required.Always)]
  List<Clause> ImportPolicy,
  [JsonProperty("export", Required = Required.Always)]
  List<Clause> ExportPolicy,

  [JsonProperty("ip", Required = Required.Always)]
  string Ip,

  [JsonProperty("remoteAs", Required = Required.Always)]
  uint RemoteAs
);

public static class RouteMap
{
  public static Zen<RouteEnvironment> Transfer(this List<Clause> routeMap, Zen<RouteEnvironment> r)
  {
    var result = Enumerable.Reverse(routeMap).Aggregate(
      Zen.Constant(new RouteEnvironment()),
      (after, clause) => clause.TransferFunction(r, after));
    return result;
  }

  public static Template<Func<Zen<RouteEnvironment>, Zen<RouteEnvironment>>, List<Clause>> GenerateTemplate(
    this List<Clause> routeMap, TemplateArguments args)
  {
    // (template, disable)
    var templates = routeMap.Select(rm => (rm.GenerateTemplate(args), Zen.Symbolic<bool>())).ToList();
    var lastSeqNum = routeMap.Count != 0 ? routeMap.Last().SeqNum : 0;
    var extraTemplates = Enumerable.Range(0, args.ExtraClauses)
      .Select(i => Clause.GenerateFreshTemplate(args, $"generated{i}", lastSeqNum + 10 * i));
    return new Template<Func<Zen<RouteEnvironment>, Zen<RouteEnvironment>>, List<Clause>>(
      r =>
        Enumerable.Reverse(templates).Aggregate(
          Zen.Constant(new RouteEnvironment()),
          (after, p) =>
            Zen.If(p.Item2, after, p.Item1.TransferFunction(r, after))),
      templates.Aggregate(
        Zen.Constant(BigInteger.Zero),
        (sum, p) =>
          Zen.If(p.Item2, Zen.Constant(new BigInteger(2)), p.Item1.Cost)),
      ZenExtension.And(templates.Select(p => p.Item1.Constraint)),
      model =>
        templates.Where(p => !model.Get(p.Item2))
          .Select(p => p.Item1.Repair(model)).ToList());
  }

  public static string Debug(this List<Clause> routeMap)
  {
    return "[" + String.Join(",", routeMap.Select(clause => clause.Debug())) + "]";
  }
}

