using System;
using System.Numerics;
using System.Collections.Generic;
using ZenLib;
using static ZenLib.Language;

namespace ZenDemo
{
    public class LocalPref
    {
        /// <summary>
        /// Generate a simple example network.
        /// </summary>
        public static Network<Pair<uint, uint>> Net()
        {
            var nodes = new string[] { "A", "B" };

            var neighbors = new Dictionary<string, List<string>>
            {
                { "A", new List<string> { "B" } },
                { "B", new List<string> { "A" } },
            };

            var initialValues = new Dictionary<string, Pair<uint, uint>>
            {
                { "A", (1U, 0U) },
                { "B", (1U, 10U) },
            };

            var modularAssertions = new Dictionary<string, Func<Zen<Pair<uint, uint>>, Zen<BigInteger>, Zen<bool>>>
            {
                { "A", ReachabilityAssertionTime },
                { "B", ReachabilityAssertionTime },
            };

            var monolithicAssertions = new Dictionary<string, Func<Zen<Pair<uint, uint>>, Zen<bool>>>
            {
                { "A", ReachabilityAssertionStable },
                { "B", ReachabilityAssertionStable },
            };

            var annotations = new Dictionary<string, Func<Zen<Pair<uint, uint>>, Zen<BigInteger>, Zen<bool>>>
            {
                // NOTE: if we change the annotations from Item1() == 1 to Item1() <= 1,
                // the assertions will fail but the annotations still hold
                { "A", (route, time) => And(route.Item1() == 1, Implies(route.Item1() == 1, route.Item2() == 0)) },
                { "B", (route, time) => And(route.Item1() == 1, Implies(And(route.Item1() == 1, time > new BigInteger(0)), route.Item2() < 10))},
            };

            return new Network<Pair<uint, uint>>(nodes, neighbors, Transfer, Merge, initialValues, annotations, modularAssertions, monolithicAssertions);

        }

        /// <summary>
        /// The transfer function for the simple path length network.
        /// </summary>
        public static Zen<Pair<uint, uint>> Transfer(Zen<Pair<uint, uint>> route)
        {
            var hops = route.Item2();
            return Pair(route.Item1(), route.Item2() + 1);
        }

        /// <summary>
        /// The merge function for the simple path length network.
        /// </summary>
        public static Zen<Pair<uint, uint>> Merge(Zen<Pair<uint, uint>> r1, Zen<Pair<uint, uint>> r2)
        {
            (Zen<uint> r1First, Zen<uint> r1Second) = (r1.Item1(), r1.Item2());
            (Zen<uint> r2First, Zen<uint> r2Second) = (r2.Item1(), r2.Item2());
            var cmp = If(r1Second < r2Second, r1, r2);
            return If(r1First < r2First, r1, If(r1First == r2First, cmp, r2));
        }

        /// <summary>
        /// Final assertion we want to check with respect to the network with time.
        /// </summary>
        public static Zen<bool> ReachabilityAssertionTime(Zen<Pair<uint, uint>> r, Zen<BigInteger> time)
        {
            return Implies(time > new BigInteger(10), r.Item2() < 10);
        }

        /// <summary>
        /// Final assertion we want to check for the stable paths encoding that removes time.
        /// </summary>
        public static Zen<bool> ReachabilityAssertionStable(Zen<Pair<uint, uint>> r)
        {
            return r.Item2() < 10;
        }
    }
}
