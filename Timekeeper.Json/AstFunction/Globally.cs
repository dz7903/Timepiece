using System.Numerics;
using Timekeeper;
using ZenLib;

namespace Gardener.AstFunction;

public class Globally<T> : AstTemporalOperator<T>
{
  public string Predicate { get; }

  public Globally(string p)
  {
    Predicate = p;
  }

  public override Func<Zen<T>, Zen<BigInteger>, Zen<bool>> Evaluate(Func<string, AstPredicate<T>> getter)
  {
    var f = getter(Predicate).Evaluate(new AstState<T>());
    return Lang.Globally(f);
  }

  public override string ToString()
  {
    return $"Globally({Predicate})";
  }
}
