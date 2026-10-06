/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.SecondOrderPull
import Lax280166Proofs.DescriptiveComplexity.SecondOrderLift
import Lax280166Proofs.DescriptiveComplexity.OrderedComposition
import Mathlib.Tactic.FinCases
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

namespace Lax280166Proofs.DescriptiveComplexity.PiSODefinable
end Lax280166Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax280166Proofs.DescriptiveComplexity.SOBlock
end Lax280166Proofs.DescriptiveComplexity.SOBlock

namespace Lax280166Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax280166Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax280166Proofs.DescriptiveComplexity

/-!
# Closure of second-order definability under ordered FO reductions

If `P ≤ᶠᵒ[≤] Q` and `Q` is `Σₖ₊₁`- (resp. `Πₖ₊₁`-) definable, then so is `P`
(`DescriptiveComplexity.SigmaSODefinable.of_orderedReduction`,
`DescriptiveComplexity.PiSODefinable.of_orderedReduction`).

Pulling the defining sentence back through the interpretation
(`DescriptiveComplexity.SecondOrderPull`) yields a sentence over the *ordered*
expansion `L.sum Language.order` – correct for every linear order on the
input, by order-invariance of the reduction. The order is then eliminated by
re-quantifying it inside the first second-order block:

* the first block is extended with one binary relation variable, the order
  (`DescriptiveComplexity.SOBlock.withOrder`);
* the sentence is transported along the language morphism
  `DescriptiveComplexity.orderElimLHom` mapping the order symbol to the new variable;
* it is guarded by the first-order sentence `DescriptiveComplexity.linearGuard` stating
  that the variable is a linear order – as a conjunct if the block is
  existential (`Σₖ₊₁`), as a premise if it is universal (`Πₖ₊₁`).

Correctness of the guard uses `DescriptiveComplexity.linearOrderOfGuard` to promote a
guarded relation variable to an actual `LinearOrder` instance, and the
order-invariance clause of `OrderedFOReduction.correct` to connect different
choices of the order. This requires at least one second-order block to
piggyback on, whence the level `k + 1`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Adding an order variable to a block -/

/-- The block `B` extended with one extra binary relation variable, used to
re-quantify the order of an ordered reduction. -/
def SOBlock.withOrder (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Unit ⊕ B.ι
  arity := Sum.elim (fun _ => 2) B.arity

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax280166Proofs.DescriptiveComplexity.SOBlock (withOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order variable of the extended block. -/
def SOBlock.orderSym (B : Lax904597.SecondOrder.SOBlock) : B.withOrder.lang.Relations 2 :=
  ⟨Sum.inl (), rfl⟩

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax280166Proofs.DescriptiveComplexity.SOBlock (orderSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-- The assignment of the original block variables underlying an assignment
of the extended block. -/
def SOBlock.restPart (B : Lax904597.SecondOrder.SOBlock) (ρ : B.withOrder.Assignment A) : B.Assignment A :=
  fun i => ρ (Sum.inr i)

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax280166Proofs.DescriptiveComplexity.SOBlock (restPart)

end Lax904597.SecondOrder.SOBlock

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-- The assignment of the extended block determined by a binary relation (for
the order variable) and an assignment of the original block. -/
def SOBlock.joinOrder (B : Lax904597.SecondOrder.SOBlock) (R : (Fin 2 → A) → Prop) (ρ : B.Assignment A) :
    B.withOrder.Assignment A :=
  fun p => match p with
    | Sum.inl _ => R
    | Sum.inr i => ρ i

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax280166Proofs.DescriptiveComplexity.SOBlock (joinOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-! ### The linear-order guard -/

section Guard

end Guard

/-! ### Promoting a guarded order variable to a linear order -/

/-! ### Eliminating the order symbol -/

/-! ### Order elimination, as a statement about sentences

The two theorems below are the order-elimination construction on its own,
separated from the reduction that usually produces the sentence: a problem
defined – over the *ordered* expansion, so with the order visible to the
sentence – by a `Σₖ₊₁` sentence *for some* linear order, or by a `Πₖ₊₁`
sentence *for every* linear order, is definable at that level over the bare
vocabulary. The closure theorems of the next section are the case where the
sentence comes from pulling a definition back through an ordered reduction,
where order-invariance makes “for some” and “for every” agree.

Stated this way the construction also applies where no single order-invariant
problem is in sight – to each half of a `DescriptiveComplexity.DPDefinable`
definition separately, say, whose two halves are *not* individually
order-invariant. -/

section OrderPull

end OrderPull

/-! ### Closure of the definability levels under ordered FO reductions -/

section Closure

end Closure

end Lax280166Proofs.DescriptiveComplexity


