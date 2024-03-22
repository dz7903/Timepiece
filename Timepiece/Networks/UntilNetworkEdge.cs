using System;
using System.Collections.Generic;
using System.Linq;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace Timepiece.Networks;

public class UntilNetworkEdge<RouteType, NodeType> : UntilNetwork<RouteType, NodeType>
{
  public UntilNetworkEdge(UntilNetwork<RouteType, NodeType> net) : base(
    net.Digraph, net.TransferFunctions, net.MergeFunction, net.InitialValues,
    net.ParentRelation, net.PhiAnnotations, net.PsiAnnotations, net.LivenessProperties, net.Symbolics)
  {}

  public new Dictionary<NodeType, Option<State<RouteType, NodeType>>> CheckAnnotationsWith<TAcc>(TAcc collector, Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType>>>, Option<State<RouteType, NodeType>>> f)
  {
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));
    var s1 = Digraph.Nodes.AsParallel()
      .Select(node => (node, f(node, collector, () =>
        CheckInitial(node).OrElse(() =>
          CheckLiveness(node)))))
      .ToDictionary();
    var s2 = Digraph.Edges().AsParallel()
      .Select(
        p => (p.Item2, f(p.Item2, collector, () =>
          CheckPreEdge(p.Item1, p.Item2, routes).OrElse(() =>
            CheckPostEdge(p.Item1, p.Item2, routes)))))
      .ToDictionary();
    foreach (var x in s2)
      s1.Add(x.Key, x.Value);
    return s1;
  }

  private Option<State<RouteType, NodeType>> CheckPreEdge(
    NodeType neighbor, NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    var newNodeRoute = MergeFunction(routes[node], TransferFunctions[(neighbor, node)](routes[neighbor]));
    var check = If(
      ParentRelation[(neighbor, node)],
      Implies(
        PhiAnnotations[neighbor](routes[neighbor]),
        PhiAnnotations[node](MergeFunction(InitialValues[node],
          TransferFunctions[(neighbor, node)](routes[neighbor])))),
      Implies(
        And(
          Or(PhiAnnotations[neighbor](routes[neighbor]), PsiAnnotations[neighbor](routes[neighbor])),
          Implies(ParentRelation[(node, neighbor)], PhiAnnotations[neighbor](routes[neighbor])),
          PhiAnnotations[node](routes[node])),
        PhiAnnotations[node](newNodeRoute)));
    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Pre check at edge {neighbor} -> {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.UntilPre);
    return Option.Some(state);
  }

  private Option<State<RouteType, NodeType>> CheckPostEdge(
    NodeType neighbor, NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    var newNodeRoute = MergeFunction(routes[node], TransferFunctions[(neighbor, node)](routes[neighbor]));
    var check = If(
      ParentRelation[(neighbor, node)],
      Implies(
        PsiAnnotations[neighbor](routes[neighbor]),
        PsiAnnotations[node](MergeFunction(InitialValues[node],
          TransferFunctions[(neighbor, node)](routes[neighbor])))),
      Implies(
        And(
          Or(PhiAnnotations[neighbor](routes[neighbor]), PsiAnnotations[neighbor](routes[neighbor])),
          PsiAnnotations[node](routes[node])),
        PsiAnnotations[node](newNodeRoute)));
    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Pre check at edge {neighbor} -> {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.UntilPost);
    return Option.Some(state);
  }

}
