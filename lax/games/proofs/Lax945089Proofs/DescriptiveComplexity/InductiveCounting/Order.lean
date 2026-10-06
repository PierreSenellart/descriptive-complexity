/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.NatCard
import Lax945089Proofs.DescriptiveComplexity.OrderWalk
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax945089Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax945089Proofs.DescriptiveComplexity

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

namespace Lax945089Proofs.DescriptiveComplexity

namespace InductiveCounting

instance instFiniteWithBot {V : Type} [Finite V] : Finite (WithBot V) :=
  inferInstanceAs (Finite (Option V))

/-! ### Covers in a finite linear order -/

section Covers

end Covers

/-! ### Counts -/

section Counts

variable {A : Type} [LinearOrder A] [Finite A] {V : Type} [LinearOrder V] [Finite V]

omit [Finite V] in
@[simp] theorem orank_bot : Lax895169.BitPredicate.orank (⊥ : WithBot V) = 0 := orank_eq_zero (fun _ => bot_le)

end Counts

/-! ### Loop positions -/

section Positions

end Positions

/-! ### Counting the scanned part of a set -/

section Counting

end Counting

end InductiveCounting

end Lax945089Proofs.DescriptiveComplexity


