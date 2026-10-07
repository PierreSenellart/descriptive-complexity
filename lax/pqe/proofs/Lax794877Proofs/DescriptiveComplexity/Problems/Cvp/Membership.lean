/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Interpretation
import Lax794877Proofs.DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Lax794877Proofs.DescriptiveComplexity.FixedPoint
import Lax794877Proofs.DescriptiveComplexity.OrderWalk
import Lax794877Proofs.DescriptiveComplexity.OrderedComposition
import Lax794877Proofs.DescriptiveComplexity.RelComposition
import Lax794877Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax794877Proofs.DescriptiveComplexity.SecondOrderLift
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.CircuitValue (CircuitAccepts GateVal)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax535992.CircuitValue (circIsAnd circIsFalse circIsNot circIsOr circIsTrue circLeft circOut circRight circuit)
end FirstOrder.Language

/-!
# CVP is in polynomial time

Membership is written in FO(LFP) and not in the Horn fragment, and the choice
is the point of the file: the semantics of `DescriptiveComplexity.CVP` *is* a
least fixed point (`DescriptiveComplexity.GateVal`), so the rule system
`DescriptiveComplexity.Cvp.cvpRules` is the ten gate rules transcribed, one per line
of the inductive definition, and the output sentence is the one first-order
statement the Horn fragment could not make head-on: “some output gate is in the
true rail”. A Horn program accepts when its least model satisfies its *goal*
clauses, i.e., when something is **not** derived, so the same definition in the
fragment would have to be written on the false rail and would need the circuit
to be well-formed for the two rails to be complementary. Reading the value at
an unrestricted first-order output formula avoids the detour, and
`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME` – Immerman–Vardi – turns it
back into membership in the class.

The `≡` between the rule system's least model and the inductive semantics is
proved in both directions in the usual way: the inductive predicate is closed
under the rules (`DescriptiveComplexity.Cvp.derives_of_gateVal`), and it is a
prefixpoint, so it contains the least one
(`DescriptiveComplexity.Cvp.gateVal_of_derives`, by
`DescriptiveComplexity.lfpAssign_least_of_closed`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

namespace Cvp

open FirstOrder

open Language Structure

/-! ### The block, the vocabulary of the rules, and their guards -/

/-- The two rails of the induction: one unary relation variable per truth
value, `true` carrying the gates that evaluate to `1`. Indexing the block by
`Bool` rather than by `Fin 2` is what lets `ρ true` and `ρ false` elaborate;
the block is reducible so that a numeral elaborates at `Fin (arity i)`. -/
@[reducible] def valBlock : Lax904597.SecondOrder.SOBlock where
  ι := Bool
  arity := fun _ => 1

/-! ### The rules

One rule per constructor of `DescriptiveComplexity.GateVal`, with the gate as
variable `0` and its two arguments as variables `1` and `2`. -/

/-! ### The output sentence: some output gate is in the true rail -/

/-! ### The least model of the rules is the inductive semantics -/

section Model

/-! ### The value of the definition -/

end Model

/-! ### Definability and membership -/

end Cvp

end Lax794877Proofs.DescriptiveComplexity


