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

  public Dictionary<NodeType, Option<State<RouteType, NodeType>>> CheckAnnotationsWith<TAcc>(
    TAcc collector,
    Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType>>>,
      Option<State<RouteType, NodeType>>> f);

  public void CheckAnnotationsFastWith<TAcc>(
    TAcc collector,
    Func<NodeType, TAcc, Func<Option<State<RouteType, NodeType>>>,
      Option<State<RouteType, NodeType>>> f)
  {
    CheckAnnotationsWith(collector, (node, collector, g) =>
    {
      var result = f(node, collector, g);
      if (result.HasValue)
        throw new CheckException<RouteType, NodeType>(result.Value);
      return Option.None<State<RouteType, NodeType>>();
    });
  }
}
