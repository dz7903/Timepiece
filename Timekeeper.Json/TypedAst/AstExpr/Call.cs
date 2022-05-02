using ZenLib;

namespace Timekeeper.Json.TypedAst.AstExpr;

public class Call<T> : Expr<T>
{
  public Call(string name)
  {
    Name = name;
  }

  public string Name { get; set; }

  public override Func<Zen<TS>, Zen<T>> Evaluate<TS>(AstState astState)
  {
    throw new NotImplementedException();
  }

  public override void Rename(string oldVar, string newVar)
  {
    ; // no-op
  }
}
