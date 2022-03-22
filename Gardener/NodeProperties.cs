using System.Collections.Immutable;
using System.Numerics;
using Gardener.AstFunction;
using Karesansui;
using NetTools;
using Newtonsoft.Json.Linq;
using ZenLib;

namespace Gardener;

/// <summary>
/// Representation of the properties of a node as parsed from JSON.
/// Tracks the node's prefixes and its routing policies.
/// </summary>
/// <typeparam name="T">The type of routes for the node.</typeparam>
public class NodeProperties<T>
{
  public NodeProperties(List<IPAddressRange> prefixes, Dictionary<string, RoutingPolicies> policies,
    string? assert, AstTemporalOperator<T>? invariant, Dictionary<string, AstFunction<T>> declarations,
    Dictionary<string, JObject> constants)
  {
    Prefixes = prefixes;
    Policies = policies;
    Assert = assert;
    Invariant = invariant;
    Declarations = declarations;
    Constants = constants;
    DisambiguateVariableNames();
  }

  /// <summary>
  /// Additional function declarations.
  /// </summary>
  public Dictionary<string, AstFunction<T>> Declarations { get; set; }

  /// <summary>
  /// Additional constant declarations.
  /// </summary>
  public Dictionary<string, JObject> Constants { get; set; }

  public AstTemporalOperator<T>? Invariant { get; set; }

  public List<IPAddressRange> Prefixes { get; }

  public Dictionary<string, RoutingPolicies> Policies { get; }

  public string? Assert { get; }

  /// <summary>
  /// Make the arguments to all AstFunctions unique.
  /// </summary>
  private void DisambiguateVariableNames()
  {
    foreach (var function in Declarations.Values)
    {
      function.Rename(function.Arg, $"${function.Arg}~{VarCounter.Request()}");
      Console.WriteLine($"New function arg: {function.Arg}");
    }
  }

  public KaresansuiNode<T> CreateNode(Func<List<IPAddressRange>, Zen<T>> initFunction,
    Func<string, AstPredicate<T>> predicateLookupFunction,
    AstFunction<T> defaultExport,
    AstFunction<T> defaultImport)
  {
    var init = initFunction(Prefixes);

    var safetyProperty = Assert is null
      ? _ => true
      : predicateLookupFunction(Assert).Evaluate(new State<T>());

    var invariant = Invariant is null
      ? (_, _) => true
      : Invariant.Evaluate(predicateLookupFunction);

    var imports = new Dictionary<string, Func<Zen<T>, Zen<T>>>();
    var exports = new Dictionary<string, Func<Zen<T>, Zen<T>>>();
    foreach (var (neighbor, policies) in Policies)
    {
      var exportAstFunctions = policies.Export.Select(policyName => Declarations[policyName]);
      var importAstFunctions = policies.Import.Select(policyName => Declarations[policyName]);
      exports[neighbor] = AstFunction<T>.Compose(exportAstFunctions, defaultExport).Evaluate(new State<T>());
      imports[neighbor] = AstFunction<T>.Compose(importAstFunctions, defaultImport).Evaluate(new State<T>());
    }

    return new KaresansuiNode<T>(init, safetyProperty, invariant, imports.ToImmutableDictionary(),
      exports.ToImmutableDictionary());
  }
}
