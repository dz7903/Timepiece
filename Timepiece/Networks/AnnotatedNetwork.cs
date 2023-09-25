using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace Timepiece.Networks;

/// <summary>
///   Represents an annotated network.
/// </summary>
/// <typeparam name="RouteType">The type of the routes.</typeparam>
/// <typeparam name="NodeType">The type of nodes.</typeparam>
/// <typeparam name="SymbolicType">The type of symbolic values associated with the network.</typeparam>
public class AnnotatedNetwork<RouteType, NodeType, SymbolicType> : Network<RouteType, NodeType, SymbolicType>
{
  /// <summary>
  ///   Construct a new <c>AnnotatedNetwork{T,TV,TS}</c>.
  /// </summary>
  /// <param name="digraph">The network topology.</param>
  /// <param name="transferFunction">A Dictionary from edges to transfer functions.</param>
  /// <param name="mergeFunction">The merge function.</param>
  /// <param name="initialValues">A Dictionary from nodes to initial routes.</param>
  /// <param name="annotations">A Dictionary from nodes to temporal predicates.</param>
  /// <param name="modularProperties">A Dictionary from nodes to temporal predicates.</param>
  /// <param name="monolithicProperties">A Dictionary from nodes to predicates.</param>
  /// <param name="symbolics">An array of symbolic values.</param>
  public AnnotatedNetwork(
    Digraph<NodeType> digraph,
    Dictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> transferFunction,
    Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> mergeFunction,
    Dictionary<NodeType, Zen<RouteType>> initialValues,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> annotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> modularProperties,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> monolithicProperties,
    SymbolicValue<SymbolicType>[] symbolics) : base(digraph, transferFunction, mergeFunction, initialValues, symbolics)
  {
    Annotations = annotations;
    ModularProperties = modularProperties;
    MonolithicProperties = monolithicProperties;
  }

  /// <summary>
  ///   Construct a new <c>AnnotatedNetwork{T,TS}</c> using an alternate properties definition.
  ///   For modular checking, for each node we check a property
  ///   <c>Globally(safetyProperties[n])</c> and <c>Finally(convergeTime, stableProperties[n])</c>.
  ///   For monolithic checking, for each node we check a property
  ///   <c>safetyProperties[n]</c> and <c>stableProperties[n]</c>.
  /// </summary>
  /// <param name="digraph">The network topology.</param>
  /// <param name="transferFunction"></param>
  /// <param name="mergeFunction"></param>
  /// <param name="initialValues"></param>
  /// <param name="annotations"></param>
  /// <param name="stableProperties">Properties which are true at convergence.</param>
  /// <param name="safetyProperties">Properties which are always true (in the modular network).</param>
  /// <param name="convergeTime">The convergence time of the network.</param>
  /// <param name="symbolics"></param>
  public AnnotatedNetwork(Digraph<NodeType> digraph,
    Dictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> transferFunction,
    Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> mergeFunction,
    Dictionary<NodeType, Zen<RouteType>> initialValues,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> annotations,
    IReadOnlyDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> stableProperties,
    IReadOnlyDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> safetyProperties,
    BigInteger convergeTime,
    SymbolicValue<SymbolicType>[] symbolics) : this(digraph,
    transferFunction, mergeFunction, initialValues, annotations,
    // modular properties: Finally(stable) + Globally(safety)
    digraph.MapNodes(n =>
      Lang.Intersect(Lang.Finally(convergeTime, stableProperties[n]), Lang.Globally(safetyProperties[n]))),
    // monolithic properties: stable + safety
    digraph.MapNodes(n => Lang.Intersect(stableProperties[n], safetyProperties[n])),
    symbolics)
  {
  }

  /// <summary>
  /// Construct a new <c>AnnotatedNetwork{T,TS}</c> from another.
  /// </summary>
  /// <param name="net"></param>
  /// <param name="annotations"></param>
  /// <param name="modularProperties"></param>
  /// <param name="monolithicProperties"></param>
  public AnnotatedNetwork(Network<RouteType, NodeType, SymbolicType> net,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> annotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> modularProperties,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> monolithicProperties) : this(net.Digraph,
    net.TransferFunction,
    net.MergeFunction,
    net.InitialValues, annotations, modularProperties, monolithicProperties, net.Symbolics)
  {
  }

  /// <summary>
  /// Construct a new <c>AnnotatedNetwork{T,TS}</c> from another, using an alternate properties definition.
  /// </summary>
  /// <param name="net"></param>
  /// <param name="annotations"></param>
  /// <param name="stableProperties"></param>
  /// <param name="safetyProperties"></param>
  /// <param name="convergeTime"></param>
  public AnnotatedNetwork(Network<RouteType, NodeType, SymbolicType> net,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> annotations,
    IReadOnlyDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> stableProperties,
    IReadOnlyDictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> safetyProperties,
    BigInteger convergeTime) : this(net.Digraph, net.TransferFunction, net.MergeFunction,
    net.InitialValues, annotations, stableProperties, safetyProperties, convergeTime, net.Symbolics)
  {
  }

  /// <summary>
  ///   The modular safety properties that we want to check (includes time).
  /// </summary>
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> ModularProperties { get; set; }

  /// <summary>
  ///   The monolithic safety properties that we want to check (assumes stable states).
  /// </summary>
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> MonolithicProperties { get; set; }

  /// <summary>
  ///   The invariant/annotation function for each node. Takes a route and a time and returns a boolean.
  /// </summary>
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<BigInteger>, Zen<bool>>> Annotations { get; set; }

  /// <summary>
  ///   Setting to control whether or not to print the constructed formulae to the user.
  /// </summary>
  public bool PrintFormulas { get; set; }

  /// <summary>
  ///   Check that the annotations are sound, calling the given function f on each node's check.
  /// </summary>
  /// <param name="collector"></param>
  /// <param name="f"></param>
  /// <returns></returns>
  public Dictionary<NodeType, Option<State<RouteType, NodeType, SymbolicType>>> CheckAnnotationsWith<TAcc>(
    TAcc collector,
    Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType, SymbolicType>>>,
      Option<State<RouteType, NodeType, SymbolicType>>> f)
  {
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));
    var time = Symbolic<BigInteger>("time");
    var s = Digraph.Nodes
      // call f for each node
      .AsParallel()
      .Select(node => (node, f(node, collector, () => CheckAnnotations(node, routes, time))))
      .ToDictionary(x => x.Item1, x => x.Item2);
    return s;
  }

  public Option<State<RouteType, NodeType, SymbolicType>> CheckAnnotations(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes,
    Zen<BigInteger> time)
  {
    return CheckBaseCase(node).OrElse(() => CheckInductive(node, routes, time)).OrElse(() => CheckAssertions(node));
  }

  /// <summary>
  ///   Check that the annotations are sound.
  /// </summary>
  /// <returns>True if the annotations pass, false otherwise.</returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckAnnotations()
  {
    return CheckBaseCase().OrElse(CheckInductive).OrElse(CheckAssertions);
  }

  public Option<State<RouteType, NodeType, SymbolicType>> CheckBaseCase(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");

    // if the route is the initial value, then the annotation holds (i.e., the annotation contains the route at time 0).
    var check = Implies(route == InitialValues[node],
      Annotations[node](route, new BigInteger(0)));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.Write($"Initial check at {node}: ");
      Console.WriteLine(query);
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType, SymbolicType>>();
    var state = new State<RouteType, NodeType, SymbolicType>(model, node, route, Option.None<Zen<BigInteger>>(),
      Symbolics, SmtCheck.Base);
    return Option.Some(state);
  }

  /// <summary>
  ///   Ensure that all the base check pass for all nodes.
  /// </summary>
  /// <returns>None if the annotations pass, a counterexample State otherwise.</returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckBaseCase()
  {
    return Digraph.Nodes.AsParallel().Aggregate(Option.None<State<RouteType, NodeType, SymbolicType>>(),
      (current, node) => current.OrElse(() => CheckBaseCase(node)));
  }

  /// <summary>
  ///   Ensure that the inductive invariants imply the assertions.
  /// </summary>
  /// <returns>None if the annotations pass, a counterexample State otherwise.</returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckAssertions()
  {
    return Digraph.Nodes.AsParallel().Aggregate(Option.None<State<RouteType, NodeType, SymbolicType>>(),
      (current, node) => current.OrElse(() => CheckAssertions(node)));
  }

  public Option<State<RouteType, NodeType, SymbolicType>> CheckAssertions(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");
    var time = Symbolic<BigInteger>("time");

    // ensure the inductive invariant implies the assertions we want to prove.
    var check = Implies(Annotations[node](route, time), ModularProperties[node](route, time));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.Write($"Safety check at {node}: ");
      Console.WriteLine(query);
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType, SymbolicType>>();
    var state = new State<RouteType, NodeType, SymbolicType>(model, node, route, Option.Some(time), Symbolics,
      SmtCheck.Safety);
    return Option.Some(state);
  }

  /// <summary>
  ///   Ensure that the inductive checks all pass.
  /// </summary>
  /// <returns>None if the annotations pass, a counterexample State otherwise.</returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckInductive()
  {
    // create symbolic values for each node.
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));

    // create a symbolic time variable.
    var time = Symbolic<BigInteger>("time");

    // check the inductive invariant for each node.
    // Parallel.ForEach(Topology.Nodes, node => CheckInductive(node, routes, time))
    return Digraph.Nodes.AsParallel().Select(
        node => CheckInductive(node, routes, time))
      .Aggregate(Option.None<State<RouteType, NodeType, SymbolicType>>(), (current, s) => current.OrElse(() => s));
  }

  /// <summary>
  ///   Test the inductive check for the given node.
  /// </summary>
  /// <param name="node">The node to test.</param>
  /// <param name="routes">A dictionary mapping nodes to symbolic routes.</param>
  /// <param name="time">The symbolic time to test.</param>
  /// <returns>
  ///   Some State if a counterexample is returned where the inductive check does not hold,
  ///   and otherwise None.
  /// </returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckInductive(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes,
    Zen<BigInteger> time)
  {
    // get the new route as the merge of all neighbors
    var newNodeRoute = UpdateNodeRoute(node, routes);

    // collect all of the symbolics from neighbors.
    var assume = new List<Zen<bool>> {time > new BigInteger(0)};
    assume.AddRange(Digraph[node].Select(neighbor =>
      Annotations[neighbor](routes[neighbor], time - new BigInteger(1))));

    // now we need to ensure the new route after merging implies the annotation for this node.
    var check = Implies(And(assume.ToArray()), Annotations[node](newNodeRoute, time));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.Write($"Inductive check at {node}: ");
      Console.WriteLine(query);
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType, SymbolicType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType, SymbolicType>(model, node, newNodeRoute, neighborRoutes, time,
      Symbolics);
    return Option.Some(state);
  }

  /// <summary>
  ///   Check the network using a stable routes encoding.
  /// </summary>
  /// <returns>Some state if verification fails with a counterexample, and None otherwise.</returns>
  public Option<State<RouteType, NodeType, SymbolicType>> CheckMonolithic()
  {
    // create symbolic values for each node.
    var routes = Digraph.MapNodes(node => Symbolic<RouteType>($"{node}-route"));

    // add the assertions
    var assertions = Digraph.Nodes.Select(node => MonolithicProperties[node](routes[node]));

    // add constraints for each node, that its route is the merge of all the neighbors and init
    var constraints = Digraph.Nodes.Select(node =>
      routes[node] == UpdateNodeRoute(node, routes));

    var check = And(GetSymbolicConstraints(), And(constraints.ToArray()), Not(And(assertions.ToArray())));

    // negate and try to prove unsatisfiable.
    var model = check.Solve();

    if (model.IsSatisfiable())
      return Option.Some(new State<RouteType, NodeType, SymbolicType>(model, routes, Symbolics));

    Console.WriteLine("    The monolithic checks passed!");
    return Option.None<State<RouteType, NodeType, SymbolicType>>();
  }
}
