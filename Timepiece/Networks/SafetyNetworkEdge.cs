using System;
using System.Collections.Generic;
using System.Linq;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace Timepiece.Networks;

public class SafetyNetworkEdge<RouteType, NodeType> : SafetyNetwork<RouteType, NodeType>
{
  public SafetyNetworkEdge(SafetyNetwork<RouteType, NodeType> net) : base(
    net.Digraph, net.TransferFunctions, net.MergeFunction,
    net.InitialValues, net.Annotations, net.SafetyProperties, net.Symbolics)
  {}

  public new Dictionary<NodeType, Option<State<RouteType, NodeType>>> CheckAnnotationsWith<TAcc>(TAcc collector, Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType>>>, Option<State<RouteType, NodeType>>> f)
  {
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));
    var s1 = Digraph.Nodes.AsParallel()
      .Select(node => (node, f(node, collector, () => CheckInitial(node).OrElse(() => CheckSafety(node)))))
      .ToDictionary();
    var s2 = Digraph.Edges().AsParallel()
      .Select(
        p => (p.Item2, f(p.Item2, collector, () => CheckInductiveEdge(p.Item1, p.Item2, routes))))
      .ToDictionary();
    foreach (var x in s2)
      s1.Add(x.Key, x.Value);
    return s1;
  }

  private Option<State<RouteType, NodeType>> CheckInductiveEdge(
    NodeType neighbor, NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    var newNodeRoute = MergeFunction(routes[node], TransferFunctions[(neighbor, node)](routes[neighbor]));
    var check = Implies(
      And(
        Annotations[neighbor](routes[neighbor]),
        Annotations[node](routes[node])),
      Annotations[node](newNodeRoute)
    );

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Inductive check at edge {neighbor} -> {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.Inductive);
    return Option.Some(state);
  }
}
