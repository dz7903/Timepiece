#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace Timepiece.Networks;

public class SafetyNetwork<RouteType, NodeType> : Network<RouteType, NodeType>, ICheckable<RouteType, NodeType>
  where NodeType : notnull {
  public SafetyNetwork(
    Digraph<NodeType> digraph,
    Dictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> transferFunctions,
    Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> mergeFunction,
    Dictionary<NodeType, Zen<RouteType>> initialValues,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> annotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> safetyProperties,
    ISymbolic[] symbolics) :
    base(
      digraph, transferFunctions, mergeFunction, initialValues,
      // new Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>>(),
      // new Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>>(),
      // new Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>>(),
      symbolics) {
    Annotations = annotations;
    SafetyProperties = safetyProperties;
  }

  public SafetyNetwork(Network<RouteType, NodeType> net,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> annotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> safetyProperties) :
    this(
      net.Digraph, net.TransferFunctions, net.MergeFunction, net.InitialValues,
      annotations, safetyProperties, net.Symbolics) {
  }

  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> Annotations { get; set; }
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> SafetyProperties { get; set; }

  public bool PrintFormulas { get; set; }

  public Dictionary<NodeType, Option<State<RouteType, NodeType>>> CheckAnnotationsWith<TAcc>(TAcc collector, Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType>>>, Option<State<RouteType, NodeType>>> f)
  {
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));
    var s = Digraph.Nodes
      // call f for each node
      .AsParallel()
      .Select(node => (node, f(node, collector, () => CheckAnnotations(node, routes))))
      .ToDictionary(x => x.Item1, x => x.Item2);
    return s;
  }

  private Option<State<RouteType, NodeType>> CheckAnnotations(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    return CheckInitial(node).OrElse(() => CheckInductive(node, routes)).OrElse(() => CheckSafety(node));
  }

  protected Option<State<RouteType, NodeType>> CheckInitial(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");
    var check = Implies(route == InitialValues[node], Annotations[node](route));
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Initial check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();
    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var state = new State<RouteType, NodeType>(model, node, route, Symbolics, SmtCheck.Initial);
    return Option.Some(state);
  }

  protected Option<State<RouteType, NodeType>> CheckSafety(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");
    var check = Implies(Annotations[node](route), SafetyProperties[node](route));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Safety check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var state = new State<RouteType, NodeType>(model, node, route, Symbolics, SmtCheck.Safety);
    return Option.Some(state);
  }

  protected Option<State<RouteType, NodeType>> CheckInductive(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    // get the new route as the merge of all neighbors
    var newNodeRoute = UpdateNodeRoute(node, routes);

    var assume = new List<Zen<bool>> {};
    assume.AddRange(Digraph[node].Select(neighbor =>
      Annotations[neighbor](routes[neighbor])));

    // now we need to ensure the new route after merging implies the annotation for this node.
    var check = Implies(And(assume.ToArray()), Annotations[node](newNodeRoute));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Inductive check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.Inductive);
    return Option.Some(state);
  }

  /// <summary>
  ///   Verify the network using a stable routes encoding.
  /// </summary>
  /// <returns>Some state if verification fails with a counterexample, and None otherwise.</returns>
  public Option<State<RouteType, NodeType>> CheckMonolithic()
  {
    // create symbolic values for each node.
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));

    // add the assertions
    var assertions = Digraph.Nodes.Select(node => SafetyProperties[node](routes[node]));

    // add constraints for each node, that its route is the merge of all the neighbors and init
    var constraints = Digraph.Nodes.Select(node =>
      routes[node] == UpdateNodeRoute(node, routes));

    var query = And(GetSymbolicConstraints(), And(constraints.ToArray()), Not(And(assertions.ToArray())));
    if (PrintFormulas)
    {
      Console.WriteLine("Monolithic check:");
      Console.WriteLine(query.Format());
    }

    // negate and try to prove unsatisfiable.
    var model = query.Solve();

    if (model.IsSatisfiable())
      return Option.Some(new State<RouteType, NodeType>(model, routes, Symbolics));

    Console.WriteLine("    The monolithic checks passed!");
    return Option.None<State<RouteType, NodeType>>();
  }
}
