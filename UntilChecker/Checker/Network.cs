using Timepiece;
using ZenLib;
using UntilChecker.IR;
using UntilChecker.DataTypes;

namespace UntilChecker.Checker;

public class Network<TNode, TRoute, TSym>(
  Digraph<TNode> digraph,
  Func<TNode, Zen<TSym>, Zen<TRoute>> initialRoutes,
  Func<TNode, TNode, Zen<TRoute>, Zen<TSym>, Zen<TRoute>> transferFunctions,
  Func<Zen<TRoute>, Zen<TRoute>, Zen<TRoute>> mergeFunction,
  Func<Zen<TSym>, Zen<bool>> constraint) where TNode: notnull
{
  public readonly Digraph<TNode> Digraph = digraph;
  public readonly Func<TNode, Zen<TSym>, Zen<TRoute>> InitialRoutes = initialRoutes;
  public readonly Func<TNode, TNode, Zen<TRoute>, Zen<TSym>, Zen<TRoute>> TransferFunctions = transferFunctions;
  public readonly Func<Zen<TRoute>, Zen<TRoute>, Zen<TRoute>> MergeFunction = mergeFunction;
  public readonly Func<Zen<TSym>, Zen<bool>> Constraint = constraint;
}

public class CiscoNetwork<TSym>(
  Configruation config,
  Func<string, Zen<TSym>, Zen<BgpRoute>> initialRoutes,
  Func<Zen<TSym>, Zen<bool>> constraint
) : Network<string, BgpRoute, TSym>(
   config.ToDigraph(),
   initialRoutes,
   (src, dst, r, _) => config.TransferFunction(src, dst, r),
   BgpRouteExtensions.Min,
   constraint)
{
  public readonly Configruation Config = config;

  // public static CiscoNetwork<TSym> StaticDest(Configruation config, string dest, Func<Zen<TSym>, Zen<bool>> constraint)
  // {
  //   return new CiscoNetwork<TSym>(
  //     config,
  //     (n, sym) =>
  //       n == dest ? Zen.Constant(BgpRoute.DefaultRoute()) : Zen.Constant(BgpRoute.NoRoute()),
  //     constraint);
  // }
  //
  // public static CiscoNetwork<Pair<TSym, string>> DynamicDest(Configruation config, List<string> destinations, Func<Zen<TSym>, Zen<bool>> constraint)
  // {
  //   return new CiscoNetwork<Pair<TSym, string>>(
  //     config,
  //     (n, sym) =>
  //       Zen.If<BgpRoute>(n == sym.Item2(), BgpRoute.DefaultRoute(), BgpRoute.NoRoute()),
  //     sym => constraint(sym.Item1()));
  // }
}

