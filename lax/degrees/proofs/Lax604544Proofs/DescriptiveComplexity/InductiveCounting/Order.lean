/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.NatCard
import Lax604544Proofs.DescriptiveComplexity.OrderWalk
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Registers as counters and as loop positions

The registers of `DescriptiveComplexity.InductiveCounting.Cfg` hold values in `WithBot V`, read in
two ways: as a *count*, through `DescriptiveComplexity.orank` (so `⊥` is `0` and each
cover adds one), and as a *loop position*, through
`DescriptiveComplexity.InductiveCounting.predSet` (the set of nodes already scanned). This file
collects the arithmetic of the two readings: how a cover moves a loop past one
more node, how the count of a set restricted to the scanned part grows, and
when a counter still has room to be incremented.
-/

namespace Lax604544Proofs.DescriptiveComplexity

namespace InductiveCounting

instance instFiniteWithBot {V : Type} [Finite V] : Finite (WithBot V) :=
  inferInstanceAs (Finite (Option V))

/-! ### Covers in a finite linear order -/

section Covers

end Covers

/-! ### Counts -/

section Counts

end Counts

/-! ### Loop positions -/

section Positions

end Positions

/-! ### Counting the scanned part of a set -/

section Counting

end Counting

end InductiveCounting

end Lax604544Proofs.DescriptiveComplexity


