using System;

namespace Timepiece.Networks;

public class CheckException<RouteType, NodeType>(State<RouteType, NodeType> state) : Exception
{
  public State<RouteType, NodeType> State { get; } = state;
}
