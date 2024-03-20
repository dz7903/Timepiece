#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Timepiece.DataTypes;
using ZenLib;
using static ZenLib.Zen;

namespace Timepiece.Networks;

public class UntilNetwork<RouteType, NodeType> : Network<RouteType, NodeType>, ICheckable<RouteType, NodeType> where NodeType : notnull {

  public UntilNetwork(
    Digraph<NodeType> digraph,
    Dictionary<(NodeType, NodeType), Func<Zen<RouteType>, Zen<RouteType>>> transferFunctions,
    Func<Zen<RouteType>, Zen<RouteType>, Zen<RouteType>> mergeFunction,
    Dictionary<NodeType, Zen<RouteType>> initialValues,
    Dictionary<(NodeType, NodeType), Zen<bool>> parentRelation,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> livenessProperties,
    ISymbolic[] symbolics) :
    base(
      digraph, transferFunctions, mergeFunction, initialValues, symbolics) {
    ParentRelation = parentRelation;
    PhiAnnotations = phiAnnotations;
    PsiAnnotations = psiAnnotations;
    LivenessProperties = livenessProperties;
  }

  public UntilNetwork(Network<RouteType, NodeType> net,
    Dictionary<(NodeType, NodeType), Zen<bool>> parentRelation,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> livenessProperties) :
    this(
      net.Digraph, net.TransferFunctions, net.MergeFunction, net.InitialValues,
      parentRelation, phiAnnotations, psiAnnotations, livenessProperties, net.Symbolics) {
  }

  public UntilNetwork(Network<RouteType, NodeType> net,
    Dictionary<NodeType, Zen<BigInteger>> witnessTime,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> phiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> psiAnnotations,
    Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> livenessProperties) :
    this(
      net.Digraph, net.TransferFunctions, net.MergeFunction, net.InitialValues,
      net.Digraph.MapEdges(e => witnessTime[e.Item1] < witnessTime[e.Item2]),
      phiAnnotations, psiAnnotations, livenessProperties, net.Symbolics) {
  }

  public Dictionary<(NodeType, NodeType), Zen<bool>> ParentRelation { get; set; }
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PhiAnnotations { get; set; }
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> PsiAnnotations { get; set; }
  public Dictionary<NodeType, Func<Zen<RouteType>, Zen<bool>>> LivenessProperties { get; set; }

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

  public Option<State<RouteType, NodeType>> CheckAnnotations(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    return CheckInitial(node)
      .OrElse(() => CheckPre(node, routes))
      .OrElse(() => CheckPost(node, routes))
      .OrElse(() => CheckLiveness(node));
  }

  public Option<State<RouteType, NodeType>> CheckInitial(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");
    var check = Implies(route == InitialValues[node],
      If(
        Digraph[node].Exists(neighbor =>
          ParentRelation[(neighbor, node)]),
        PhiAnnotations[node](route),
        PsiAnnotations[node](route)
      ));
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

  public Option<State<RouteType, NodeType>> CheckLiveness(NodeType node)
  {
    var route = Symbolic<RouteType>($"{node}-route");
    var check = Implies(PsiAnnotations[node](route), LivenessProperties[node](route));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Liveness check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var state = new State<RouteType, NodeType>(model, node, route, Symbolics, SmtCheck.UntilLiveness);
    return Option.Some(state);
  }

  public Option<State<RouteType, NodeType>> CheckPre(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    // get the new route as the merge of all neighbors
    var newNodeRoute = UpdateNodeRoute(node, routes);

    var assume = new List<Zen<bool>> {};
    assume.AddRange(Digraph[node].Select(neighbor =>
      Zen.Or(
        PhiAnnotations[neighbor](routes[neighbor]),
        PsiAnnotations[neighbor](routes[neighbor])
      )));
    assume.AddRange(Digraph[node].Select(neighbor =>
      Zen.Implies(
        ParentRelation[(node, neighbor)],
        PhiAnnotations[neighbor](routes[neighbor])
      )));
    var assume1 = new List<Zen<bool>> {};
    assume1.AddRange(Digraph[node].Select(neighbor =>
      Zen.And(ParentRelation[(neighbor, node)], PhiAnnotations[neighbor](routes[neighbor]))));
    assume.Add(Zen.Or(assume1));

    // now we need to ensure the new route after merging implies the annotation for this node.
    var check = Implies(And(assume.ToArray()), PhiAnnotations[node](newNodeRoute));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Pre-stable check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.UntilPre);
    return Option.Some(state);
  }

  public Option<State<RouteType, NodeType>> CheckPost(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes)
  {
    // get the new route as the merge of all neighbors
    var newNodeRoute = UpdateNodeRoute(node, routes);

    var assume = new List<Zen<bool>> {};
    assume.AddRange(Digraph[node].Select(neighbor =>
      Zen.Or(
        PhiAnnotations[neighbor](routes[neighbor]),
        PsiAnnotations[neighbor](routes[neighbor])
      )));
    assume.AddRange(Digraph[node].Select(neighbor =>
      Zen.Implies(
        ParentRelation[(neighbor, node)],
        PsiAnnotations[neighbor](routes[neighbor])
      )));

    // now we need to ensure the new route after merging implies the annotation for this node.
    var check = Implies(And(assume.ToArray()), PsiAnnotations[node](newNodeRoute));

    // negate and try to prove unsatisfiable.
    var query = And(GetSymbolicConstraints(), Not(check));
    if (PrintFormulas)
    {
      Console.WriteLine($"Post-stable check at {node}: ");
      Console.WriteLine(query.Format());
    }

    var model = query.Solve();

    if (!model.IsSatisfiable()) return Option.None<State<RouteType, NodeType>>();
    var neighborRoutes = routes.Where(pair => Digraph[node].Contains(pair.Key));
    var state = new State<RouteType, NodeType>(model, node, newNodeRoute, neighborRoutes, Symbolics, SmtCheck.UntilPost);
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
    var assertions = Digraph.Nodes.Select(node => LivenessProperties[node](routes[node]));

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
