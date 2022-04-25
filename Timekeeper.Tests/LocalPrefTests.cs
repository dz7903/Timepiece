using System;
using System.Collections.Generic;
using System.Numerics;
using Timekeeper.Networks;
using Xunit;
using ZenLib;
using static ZenLib.Zen;

namespace Timekeeper.Tests;

using LpRoute = Pair<BigInteger, BigInteger>;

public static class LocalPrefTests
{
  private static LocalPref Net(
    Dictionary<string, Func<Zen<LpRoute>, Zen<BigInteger>, Zen<bool>>> annotations)
  {
    var topology = Topologies.Path(2);

    var initialValues = new Dictionary<string, Zen<LpRoute>>
    {
      {"A", Pair.Create(Constant(BigInteger.One), Constant(BigInteger.Zero))},
      {"B", Pair.Create(Constant(BigInteger.One), Constant(new BigInteger(10)))}
    };

    var convergeTime = new BigInteger(10);
    return new LocalPref(topology, initialValues, annotations, convergeTime);
  }

  [Fact]
  public static void SoundAnnotationsPassChecks()
  {
    var annotations = new Dictionary<string, Func<Zen<LpRoute>, Zen<BigInteger>, Zen<bool>>>
    {
      // NOTE: if we change the annotations from Item1() == 1 to Item1() <= 1,
      // the assertions will fail but the annotations still hold
      {
        "A",
        Lang.Equals<LpRoute>(Pair.Create<BigInteger, BigInteger>(BigInteger.One, BigInteger.Zero))
      },
      {
        "B",
        Lang.Until(BigInteger.One,
          r => r == Pair.Create<BigInteger, BigInteger>(BigInteger.One, new BigInteger(10)),
          Lang.Both<BigInteger, BigInteger>(fst => fst == BigInteger.One,
            snd => And(snd > BigInteger.Zero, snd < new BigInteger(10))))
      }
    };
    var net = Net(annotations);

    NetworkAssert.CheckSound(net);
  }

  [Fact]
  public static void UnsoundAnnotationsFailChecks()
  {
    var annotations = new Dictionary<string, Func<Zen<LpRoute>, Zen<BigInteger>, Zen<bool>>>
    {
      {
        "A",
        Lang.Globally<LpRoute>(route => And(route.Item1() <= BigInteger.One,
          Implies(route.Item1() == BigInteger.One, route.Item2() == BigInteger.Zero)))
      },
      {
        "B",
        Lang.Until<LpRoute>(BigInteger.One, route => route.Item1() <= BigInteger.One,
          route => And(route.Item1() <= BigInteger.One,
            Implies(route.Item1() == BigInteger.One, route.Item2() < new BigInteger(10))))
      }
    };
    var net = Net(annotations);

    NetworkAssert.CheckUnsound(net);
  }
}
