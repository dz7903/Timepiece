using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Threading.Tasks;
using ZenLib;

namespace Timepiece.Networks;

public interface ICheckable<RouteType, NodeType>
{
  public Digraph<NodeType> Digraph { get; }

  public Option<State<RouteType, NodeType>> CheckAnnotations(NodeType node,
    IReadOnlyDictionary<NodeType, Zen<RouteType>> routes,
    Zen<BigInteger> time);

  private Dictionary<NodeType, Zen<RouteType>> NodeRoutes() =>
    Digraph.MapNodes(node => Zen.Symbolic<RouteType>($"{node}-route"));

  public void CheckAnnotationsWithExceptionWith<TAcc>(
    TAcc collector,
    Action<NodeType, TAcc, Action> f)
  {
    var routes = NodeRoutes();
    var time = Zen.Symbolic<BigInteger>("time");
    Parallel.ForEach(Digraph.Nodes, node =>
    {
      f(node, collector, () =>
      {
        Option<State<RouteType, NodeType>> result = CheckAnnotations(node, routes, time);
        if (result.HasValue)
        {
          throw new CheckException<RouteType, NodeType>(result.Value);
        }
      });
    });
  }
}
