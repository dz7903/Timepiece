using System.Text;

namespace Timepiece.Angler.Networks;

public enum QueryType
{
  Internet2BlockToExternal,
  Internet2BlockToExternalFaultTolerant,
  Internet2NoMartians,
  Internet2NoMartiansContra,
  Internet2NoMartiansFaultTolerant,
  Internet2NoMartiansContraFaultTolerant,
  Internet2NoPrivateAs,
  Internet2NoPrivateAsContra,
  Internet2NoPrivateAsFaultTolerant,
  Internet2Reachable,
  Internet2ReachableInternal,
  FatReachable,
  FatReachableAllToR,
  FatPathLength,
  FatPathLengthAllToR,
  FatValleyFreedom,
  FatValleyFreedomAllToR,
  FatHijackFiltering,
  FatHijackFilteringAllToR,
  Internet2BlockToExternalSafety,
  Internet2NoMartiansSafety,
  Internet2NoMartiansContraSafety,
  Internet2NoPrivateAsSafety,
  Internet2NoPrivateAsContraSafety,
  Internet2ReachableUntil,
  Internet2ReachableInternalUntil,
  Internet2BlockToExternalSafetyEdge,
  Internet2NoMartiansSafetyEdge,
  Internet2NoMartiansContraSafetyEdge,
  Internet2ReachableUntilEdge,
  Internet2ReachableInternalUntilEdge,
}

public static class QueryTypeExtensions
{
  public static string ShortHand(this QueryType qt)
  {
    return qt switch
    {
      QueryType.Internet2BlockToExternal => "bte",
      QueryType.Internet2BlockToExternalFaultTolerant => "bteFT",
      QueryType.Internet2NoMartians => "mars",
      QueryType.Internet2NoMartiansContra => "marsC",
      QueryType.Internet2NoMartiansFaultTolerant => "marsFT",
      QueryType.Internet2NoMartiansContraFaultTolerant => "marsCFT",
      QueryType.Internet2NoPrivateAs => "private",
      QueryType.Internet2NoPrivateAsContra => "privateC",
      QueryType.Internet2NoPrivateAsFaultTolerant => "privateFT",
      QueryType.Internet2Reachable => "reach",
      QueryType.Internet2ReachableInternal => "reachInternal",
      QueryType.FatReachable => "fatReach",
      QueryType.FatReachableAllToR => "fatReachAll",
      QueryType.FatPathLength => "fatLength",
      QueryType.FatPathLengthAllToR => "fatLengthAll",
      QueryType.FatValleyFreedom => "fatValley",
      QueryType.FatValleyFreedomAllToR => "fatValleyAll",
      QueryType.FatHijackFiltering => "fatHijack",
      QueryType.FatHijackFilteringAllToR => "fatHijackAll",
      QueryType.Internet2BlockToExternalSafety => "bteS",
      QueryType.Internet2NoMartiansSafety => "marsS",
      QueryType.Internet2NoMartiansContraSafety => "marsCS",
      QueryType.Internet2NoPrivateAsSafety => "privateS",
      QueryType.Internet2NoPrivateAsContraSafety => "privateCS",
      QueryType.Internet2ReachableUntil => "reachU",
      QueryType.Internet2ReachableInternalUntil => "reachInternalU",
      QueryType.Internet2BlockToExternalSafetyEdge => "bteSE",
      QueryType.Internet2NoMartiansSafetyEdge => "marsSE",
      QueryType.Internet2NoMartiansContraSafetyEdge => "marsSCE",
      QueryType.Internet2ReachableUntilEdge => "reachUE",
      QueryType.Internet2ReachableInternalUntilEdge => "reachInternalUE",
      _ => throw new ArgumentOutOfRangeException(nameof(qt), qt, $"Invalid {nameof(QueryType)} with no shorthand.")
    };
  }

  private static readonly Dictionary<string, QueryType> QueryNames = Enum.GetValues<QueryType>()
    .SelectMany(qt => new[] {(qt.ShortHand(), qt), ($"{qt}", qt)})
    .ToDictionary(p => p.Item1, p => p.Item2);

  internal static string AcceptableQueryValues()
  {
    var sb = new StringBuilder();
    sb.AppendLine("Acceptable values:");
    foreach (var qt in Enum.GetValues<QueryType>())
    {
      sb.AppendLine($"- '{qt.ShortHand()}' or '{qt}' for '{qt}'");
    }

    return sb.ToString();
  }

  public static QueryType ToQueryType(this string s)
  {
    return QueryNames.TryGetValue(s, out var queryType)
      ? queryType
      : throw new ArgumentOutOfRangeException(nameof(s), s,
        $"Invalid network query type name! {AcceptableQueryValues()}");
  }
}
