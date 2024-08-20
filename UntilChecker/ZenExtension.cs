using ZenLib;

namespace UntilChecker;

public static class ZenExtension
{
  public static Zen<bool> And(IEnumerable<Zen<bool>>? exprs)
  {
    if (exprs == null) return Zen.True();
    var enumerable = exprs.ToList();
    return !enumerable.Any() ? Zen.True() : Zen.And(enumerable);
  }

  public static Zen<bool> Or(IEnumerable<Zen<bool>>? exprs)
  {
    if (exprs == null) return Zen.True();
    var enumerable = exprs.ToList();
    return !enumerable.Any() ? Zen.False() : Zen.Or(enumerable);
  }
}
