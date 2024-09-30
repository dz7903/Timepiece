using System.Numerics;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace UntilChecker.DataTypes;

[ZenObject]
public class BgpRoute
{
  public const uint DefaultLp = 100;

  public Ipv4Prefix Prefix { get; set; }
  public uint Lp { get; set; }
  public CSet<uint> AsSet { get; set; }
  public BigInteger AsLength { get; set; }
  public CSet<string> Communities { get; set; }
  public bool Valid { get; set; }

  public BgpRoute(
    Ipv4Prefix prefix,
    uint lp,
    CSet<uint> asSet,
    BigInteger asLength,
    CSet<string> communities,
    bool valid)
  {
    Prefix = prefix;
    Lp = lp;
    AsSet = asSet;
    AsLength = asLength;
    Communities = communities;
    Valid = valid;
  }

  public static BgpRoute NoRoute() =>
    new BgpRoute(new Ipv4Prefix(), 0, new CSet<uint>(), 0, new CSet<string>(), false);

  public BgpRoute()
  {
    Valid = false;
  }

  public static BgpRoute DefaultRoute() =>
    new BgpRoute(new Ipv4Prefix(), DefaultLp, new CSet<uint>(), 0, new CSet<string>(), true);

  public override string ToString() =>
    Valid ? $"BgpRoute(Valid=true, Prefix={Prefix}, Lp={Lp}, AsSet=[{
      string.Join(", ", AsSet.Map.Values.Keys)
    }], AsLength={AsLength}, Communities=[{
      string.Join(", ", Communities.Map.Values.Keys)
    }])" : $"BgpRoute(Valid=false)";

}

public static class BgpRouteExtensions
{
  public static Zen<bool> IsValid(this Zen<BgpRoute> s) =>
    s.GetValid();

  public static Zen<bool> IsNonValid(this Zen<BgpRoute> s) =>
    Not(IsValid(s));

  public static Zen<BgpRoute> IncreaseAsLength(this Zen<BgpRoute> s) =>
    s.WithAsLength(s.GetAsLength() + BigInteger.One);

  public static Zen<bool> HasCommunity(this Zen<BgpRoute> s, string community) =>
    s.GetCommunities().Contains(community);

  public static Zen<BgpRoute> AddCommunity(this Zen<BgpRoute> s, string community) =>
    s.WithCommunities(s.GetCommunities().Add(community));

  public static Zen<bool> HasAs(this Zen<BgpRoute> s, uint asNum) =>
    s.GetAsSet().Contains(asNum);

  public static Zen<BgpRoute> AddAs(this Zen<BgpRoute> s, uint asNum) =>
    s.WithAsSet(s.GetAsSet().Add(asNum));

  public static Zen<BgpRoute> Min(Zen<BgpRoute> s1, Zen<BgpRoute> s2) =>
    If(s1.IsNonValid(), s2,
      If(s2.IsNonValid(), s1,
        If(s1.GetLp() > s2.GetLp(), s1,
          If(s1.GetLp() < s2.GetLp(), s2,
            If(s1.GetAsLength() < s2.GetAsLength(), s1,
              If(s1.GetAsLength() > s2.GetAsLength(), s2, s1))))));
}
