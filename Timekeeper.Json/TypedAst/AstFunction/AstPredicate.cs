using Timekeeper.Json.TypedAst.AstExpr;
using ZenLib;

namespace Timekeeper.Json.TypedAst.AstFunction;

/// <summary>
///   A unary function from type T to bool, aka a predicate over type T.
/// </summary>
/// <typeparam name="T">The predicate's argument type.</typeparam>
public class AstPredicate<T> : AstFunctionBase<T, Expr<bool>>
{
  public AstPredicate(string arg, Expr<bool> expr) : base(arg, expr)
  {
  }

  public Func<Zen<T>, Zen<bool>> Evaluate(AstState astState)
  {
    astState.Add(Arg, new Func<Zen<T>, Zen<T>>(t => t));
    return Body.Evaluate<T>(astState);
  }
}
