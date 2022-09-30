using ZenLib;

namespace Timepiece.Angler.UntypedAst.AstExpr;

public class PairExpr : BinaryOpExpr
{
  public PairExpr(Expr first, Expr second) : base(first, second,
    (e1, e2) => Pair.Create(e1, e2))
  {
  }
}
