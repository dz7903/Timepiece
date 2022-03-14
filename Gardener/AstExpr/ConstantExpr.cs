using ZenLib;

namespace Gardener.AstExpr;

public class ConstantExpr<T, TState> : Expr<T, TState>
{
  private readonly T _value;

  public ConstantExpr(T value)
  {
    _value = value;
  }

  public override Func<Zen<TState>, Zen<T>> Evaluate(State<TState> state)
  {
    return _ => Zen.Constant(_value);
  }

  public override void Rename(string oldVar, string newVar)
  { }
}
