using System.Numerics;
using System.Runtime.Serialization;
using System.Text;
using JsonSubTypes;
using Newtonsoft.Json;
using Newtonsoft.Json.Converters;
using Timepiece.DataTypes;
using UntilChecker.DataTypes;
using ZenLib;

namespace UntilChecker.IR;

[method: JsonConstructor]
public record Clause(
  [JsonProperty("action", Required = Required.Always)]
  ClauseAction Action,

  [JsonProperty("mapName", Required = Required.Always)]
  string MapName,

  [JsonProperty("seqNum", Required = Required.Always)]
  long SeqNum,

  // TODO: no match clause = always match?
  [JsonProperty("matchList")] List<MatchLine>? MatchList,

  // no set clause = no change
  [JsonProperty("setList")] List<SetLine>? SetList
)
{
  public Zen<BgpRoute> TransferFunction(Zen<BgpRoute> r, Zen<BgpRoute> otherwise)
  {
    var matched = MatchList != null ? ZenExtension.And(MatchList.Select(line => line.Match(r))) : Zen.True();
    var afterSet = SetList != null ? SetList.Aggregate(r, (after, line) => line.Apply(after)) : r;
    return Zen.If(matched, IsPermit(Action) ? afterSet : BgpRoute.NoRoute(), otherwise);
  }

  public Template<Func<Zen<BgpRoute>, Zen<BgpRoute>, Zen<BgpRoute>>, Clause> GenerateTemplate(TemplateArguments args)
  {
    // (template, disable)
    var matchTemplates =
      MatchList != null ? MatchList.Select(line => (line.GenerateTemplate(args), Zen.Symbolic<bool>())).ToList() : [];
    for (var i = 0; i < args.ExtraMatchLines; i++)
      matchTemplates.Add((MatchCommunity.GenerateFreshTemplate(args), Zen.Symbolic<bool>()));
    var setTemplates =
      SetList != null ?
        SetList.Select(line => (line.GenerateTemplate(args), Zen.Symbolic<bool>())).ToList() :
        [];
    // for (var i = 0; i < args.ExtraMatchLines; i++)
      // setTemplates.Add((SetCommunity.));
    var toggleAction = Zen.Symbolic<bool>();
    // var isPermit = Zen.If<bool>(toggle, !IsPermit(Action), IsPermit(Action));
    return new Template<Func<Zen<BgpRoute>, Zen<BgpRoute>, Zen<BgpRoute>>, Clause>(
      (r, other) =>
        Zen.If(
          ZenExtension.And(
            matchTemplates.Select(p =>
              Zen.If(p.Item2, Zen.True(), p.Item1.TransferFunction(r)))),
          Zen.If(
            Zen.If<bool>(toggleAction, !IsPermit(Action), IsPermit(Action)),
            setTemplates.Aggregate(r, (after, p) =>
              Zen.If(p.Item2, after, p.Item1.TransferFunction(after))),
            BgpRoute.NoRoute()),
          r),
      Zen.If(toggleAction, Zen.Constant(BigInteger.One), BigInteger.Zero) +
        matchTemplates.Aggregate(Zen.Constant(BigInteger.Zero), (sum, p) =>
          sum + Zen.If(p.Item2, new BigInteger(10), p.Item1.Cost)) +
        setTemplates.Aggregate(Zen.Constant(BigInteger.Zero), (sum, p) =>
          sum + Zen.If(p.Item2, new BigInteger(10), p.Item1.Cost)),
      Zen.And(
        ZenExtension.And(matchTemplates.Select(p => p.Item1.Constraint)),
        ZenExtension.And(setTemplates.Select(p => p.Item1.Constraint))),
      model =>
      {
        // Console.Write("match disabled: ");
        // foreach (var p in matchTemplates) Console.Write($"{model.Get(p.Item2)}");
        // Console.WriteLine();
        return new Clause(
          model.Get(toggleAction) ? Toggle(Action) : Action,
          MapName,
          SeqNum,
          matchTemplates.Where(p => !model.Get(p.Item2))
            .Select(p => p.Item1.Repair(model)).ToList(),
          setTemplates.Where(p => !model.Get(p.Item2))
            .Select(p => p.Item1.Repair(model)).ToList());
      }
      );
  }

  public static Template<Func<Zen<BgpRoute>, Zen<BgpRoute>, Zen<BgpRoute>>, Clause> GenerateFreshTemplate(
    TemplateArguments args, string name, long seqNum)
  {
    var matchTemplates = new List<Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine>> { MatchCommunity.GenerateFreshTemplate(args) };
    var setTemplates = new List<Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine>> { };
    var isPermit = Zen.Symbolic<bool>();

    return new Template<Func<Zen<BgpRoute>, Zen<BgpRoute>, Zen<BgpRoute>>, Clause>(
      (r, other) =>
        Zen.If(
          ZenExtension.And(matchTemplates.Select(template => template.TransferFunction(r))),
          Zen.If(isPermit,
            setTemplates.Aggregate(r, (after, template) => template.TransferFunction(after)),
            BgpRoute.NoRoute()),
          other),
      Zen.Constant(new BigInteger(100))
      + matchTemplates.Aggregate(Zen.Constant(BigInteger.Zero), (sum, template) => sum + template.Cost)
      + setTemplates.Aggregate(Zen.Constant(BigInteger.Zero), (sum, template) => sum + template.Cost),
      Zen.And(
        ZenExtension.And(matchTemplates.Select(template => template.Constraint)),
        ZenExtension.And(setTemplates.Select(template => template.Constraint))),
      model => new Clause(
        model.Get(isPermit) ? ClauseAction.Permit : ClauseAction.Deny,
        name,
        seqNum,
        matchTemplates.Select(template => template.Repair(model)).ToList(),
        setTemplates.Select(template => template.Repair(model)).ToList())
      );
  }

  private static bool IsPermit(ClauseAction action) => action switch
    {
      ClauseAction.Deny => false,
      ClauseAction.Permit => true,
      _ => throw new ArgumentOutOfRangeException(nameof(action), action, null)
    };

  private static ClauseAction Toggle(ClauseAction action) => action switch
    {
      ClauseAction.Deny => ClauseAction.Permit,
      ClauseAction.Permit => ClauseAction.Deny,
      _ => throw new ArgumentOutOfRangeException(nameof(action), action, null)
    };

  public string Debug()
  {
    StringBuilder builder = new StringBuilder();
    builder.Append($"Clause({Action}, Seq={SeqNum}, Match=");
    if (MatchList == null)
      builder.Append("[]");
    else
      builder.Append($"[{String.Join(",", MatchList.Select(line => line.Debug()))}]");
    builder.Append(", Set=");
    if (SetList == null)
      builder.Append("[]");
    else
      builder.Append($"[{String.Join(",", SetList.Select(line => line.Debug()))}]");
    builder.Append(')');
    return builder.ToString();
  }
};

[JsonConverter(typeof(StringEnumConverter))]
public enum ClauseAction
{
  [EnumMember(Value = "PERMIT")]
  Permit,
  [EnumMember(Value = "DENY")]
  Deny
};

[JsonConverter(typeof(JsonSubtypes), "type")]
[JsonSubtypes.KnownSubType(typeof(MatchCommunity), "community_list")]
[JsonSubtypes.KnownSubType(typeof(MatchIpPrefix), "ip_prefix")]
public abstract record MatchLine
{
  public abstract Zen<bool> Match(Zen<BgpRoute> r);
  public abstract Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine> GenerateTemplate(TemplateArguments args);
  public abstract string Debug();
}

[method: JsonConstructor]
public record MatchCommunity(
  // [JsonProperty("listNames", Required = Required.Always)]
  // string[] ListNames,
  [JsonProperty("communities", Required = Required.Always)]
  List<string> Communities) : MatchLine
{
  public override Zen<bool> Match(Zen<BgpRoute> r) => ZenExtension.Or(Communities.Select(tag => r.HasCommunity(tag)));
  public override Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine> GenerateTemplate(TemplateArguments args)
  {
    var disable = Communities.ToDictionary(tag => tag, tag => Zen.Symbolic<bool>($"disable-{tag}"));
    return new Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine>(
      r => ZenExtension.Or(Communities.Select(tag => Zen.And(Zen.Not(disable[tag]), r.HasCommunity(tag)))),
      Communities.Aggregate(
        Zen.Constant(BigInteger.Zero),
        (sum, tag) => sum + Zen.If(disable[tag], Zen.Constant(BigInteger.One), Zen.Constant(BigInteger.Zero))),
      ZenExtension.Or(disable.Select(p => Zen.Not(p.Value))), // At least one tag is needed in the match clause
      model => new MatchCommunity(Communities.Where(tag => !model.Get(disable[tag])).ToList()));
  }

  public static Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine> GenerateFreshTemplate(TemplateArguments args)
  {
    var enable = args.TagsCollection.ToDictionary(tag => tag, tag => Zen.Symbolic<bool>($"enable-{tag}"));
    return new Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine>(
      r => ZenExtension.Or(args.TagsCollection.Select(tag => Zen.And(enable[tag], r.HasCommunity(tag)))),
      args.TagsCollection.Aggregate(
        Zen.Constant(BigInteger.Zero),
        (sum, tag) => sum + Zen.If(enable[tag], Zen.Constant(new BigInteger(100)), Zen.Constant(BigInteger.Zero))),
      ZenExtension.Or(enable.Select(p => p.Value)), // At least one tag is needed in the match clause
      model => new MatchCommunity(args.TagsCollection.Where(tag => model.Get(enable[tag])).ToList()));
  }

  public override string Debug() => $"MatchCommunity({String.Join(",", Communities)})";
}

[method: JsonConstructor]
public record MatchIpPrefix(
  [JsonProperty("ip_prefix", Required = Required.Always)]
  List<string> Prefixes) : MatchLine
{
  // private readonly List<Ipv4Prefix> prefixes = Prefixes.Select(pref ix => new Ipv4Prefix(prefix)).ToList();

  public override Zen<bool> Match(Zen<BgpRoute> r)
  {
    // TODO exact=true?
    return Zen.And(Prefixes.Select(prefix => new Ipv4Prefix(prefix).Matches(r.GetPrefix(), true)));
  }

  public override Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine> GenerateTemplate(TemplateArguments args)
  {
    var modify = Prefixes.ToDictionary(prefix => prefix, prefix => Zen.Symbolic<bool>($"modify-{prefix}"));
    var newPrefix = Prefixes.ToDictionary(prefix => prefix, prefix => Zen.Symbolic<Ipv4Prefix>($"newPrefix-{prefix}"));
    return new Template<Func<Zen<BgpRoute>, Zen<bool>>, MatchLine>(
      r => ZenExtension.Or(Prefixes.Select(prefix =>
        Zen.If(
          modify[prefix],
          newPrefix[prefix].Matches1(r.GetPrefix()),
          new Ipv4Prefix(prefix).Matches(r.GetPrefix(), true)))),
      Prefixes.Aggregate(
        Zen.Constant(BigInteger.Zero),
        (sum, prefix) => sum + Zen.If(modify[prefix], Zen.Constant(BigInteger.One), Zen.Constant(BigInteger.Zero))),
      Zen.True(), // At least one tag is needed in the match clause
      model => new MatchIpPrefix(Prefixes.Select(prefix => model.Get(modify[prefix]) ? model.Get(newPrefix[prefix]).ToString() : prefix).ToList()));
  }
  public override string Debug() => $"MatchIPPrefix({String.Join(",", Prefixes)})";
}

[JsonConverter(typeof(JsonSubtypes), "type")]
[JsonSubtypes.KnownSubType(typeof(SetLocalPreference), "set_local_preference")]
[JsonSubtypes.KnownSubType(typeof(SetCommunity), "set_community")]
[JsonSubtypes.KnownSubType(typeof(SetAdditiveCommunity), "set_additive_community")]
[JsonSubtypes.KnownSubType(typeof(DeleteCommunity), "delete_community")]
public abstract record SetLine
{
  public abstract Zen<BgpRoute> Apply(Zen<BgpRoute> r);
  public abstract Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine> GenerateTemplate(TemplateArguments args);
  public abstract string Debug();
}


[method: JsonConstructor]
public record SetLocalPreference(
  [JsonProperty("localPreference", Required = Required.Always)]
  uint LocalPreference) : SetLine
{
  public override Zen<BgpRoute> Apply(Zen<BgpRoute> r) => r.WithLp(LocalPreference);
  public override Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine> GenerateTemplate(TemplateArguments args)
  {
    var changed = Zen.Symbolic<bool>();
    var newLp = Zen.Symbolic<uint>();
    return new Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine>(
      r => Zen.If(changed, r.WithLp(newLp), r.WithLp(LocalPreference)),
      Zen.If(changed, Zen.Constant(new BigInteger(2)), BigInteger.Zero),
      Zen.True(),
      model => new SetLocalPreference(model.Get(changed) ? model.Get(newLp) : LocalPreference));
  }

  public override string Debug() => $"SetLP({LocalPreference})";
}

[method: JsonConstructor]
public record SetCommunity(
  [JsonProperty("communities", Required = Required.Always)]
  List<string> Communities) : SetLine
{
  public override Zen<BgpRoute> Apply(Zen<BgpRoute> r) => r.WithCommunities(Zen.Constant(new CSet<string>(Communities)));
  public override Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine> GenerateTemplate(TemplateArguments args)
  {
    throw new NotImplementedException();
  }
  public override string Debug() => $"SetCommunity({String.Join(",", Communities)})";
}

[method: JsonConstructor]
public record SetAdditiveCommunity(
  [JsonProperty("communities", Required = Required.Always)]
  List<string> Communities) : SetLine
{
  public override Zen<BgpRoute> Apply(Zen<BgpRoute> r)
  {
    Zen<CSet<string>> communities = r.GetCommunities();
    foreach (var community in Communities)
      communities = communities.Add(community);
    return r.WithCommunities(communities);
  }
  public override Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine> GenerateTemplate(TemplateArguments args)
  {
    // var disable =
    throw new NotImplementedException();
  }
  public override string Debug() => $"AddCommunity({String.Join(",", Communities)})";
}

[method: JsonConstructor]
public record DeleteCommunity(
  [JsonProperty("communities", Required = Required.Always)]
  List<string> Communities) : SetLine
{
  public override Zen<BgpRoute> Apply(Zen<BgpRoute> r)
  {
    Zen<CSet<string>> communities = r.GetCommunities();
    foreach (var community in Communities)
      communities = communities.Delete(community);
    return r.WithCommunities(communities);
  }
  public override Template<Func<Zen<BgpRoute>, Zen<BgpRoute>>, SetLine> GenerateTemplate(TemplateArguments args)
  {
    throw new NotImplementedException();
  }
  public override string Debug() => $"DeleteCommunity({String.Join(",", Communities)})";
}
