using ZenLib;

namespace Timekeeper.Json.TypedAst;

public interface IEvaluable<T1, T2>
{
  Func<Zen<T1>, Zen<T2>> Evaluate(AstState astState);
}

public interface IEvaluable<T1, T2, T3>
{
  Func<Zen<T1>, Zen<T2>, Zen<T3>> Evaluate(AstState astState);
}
