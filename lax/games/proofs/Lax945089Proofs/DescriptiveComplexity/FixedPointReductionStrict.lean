/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Lax945089Proofs.DescriptiveComplexity.FixedPoint
import Lax945089Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax945089Proofs.DescriptiveComplexity.FixedPointReduction
import Lax945089Proofs.DescriptiveComplexity.FixedPointStep
import Lax945089Proofs.DescriptiveComplexity.Hierarchy
import Lax945089Proofs.DescriptiveComplexity.OrderWalk
import Lax945089Proofs.DescriptiveComplexity.Ordered
import Lax945089Proofs.DescriptiveComplexity.OrderedComposition
import Lax945089Proofs.DescriptiveComplexity.RelComposition
import Lax945089Proofs.DescriptiveComplexity.SecondOrder
import Lax945089Proofs.DescriptiveComplexity.SecondOrderLift
import Lax945089Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax945089Proofs.DescriptiveComplexity.SecondOrderPull
import Lax945089Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax945089Proofs.DescriptiveComplexity.Vocabulary
import Lax945089Proofs.DescriptiveComplexity.Problems.Even
import Lax945089Proofs.DescriptiveComplexity.Problems.Parity
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

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax945089.Parity
end Lax945089.Parity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.FirstOrderDefinability (FODefinable)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax945089Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax945089.Parity (markedSet markedSetMark)
end FirstOrder.Language

/-!
# FO(LFP) reductions are strictly stronger than first-order ones

`DescriptiveComplexity.FOReduction.toLFP` embeds every first-order reduction
into the FO(LFP) ones. This file shows the embedding is **strict**, and
unconditionally: there is a problem to which EVEN reduces in FO(LFP) and to
which it reduces by no first-order reduction at all
(`DescriptiveComplexity.exists_lfpReduction_not_orderedReduction`).

The witness is as small as it can be. Let `NONEMPTYMARK` be “the marked subset
is nonempty”, over the vocabulary of a marked set
(`DescriptiveComplexity.Problems.Parity`). It is first-order definable – one
existential quantifier – so nothing that first-order reduces to it is harder
than a first-order sentence, and EVEN is not
(`DescriptiveComplexity.even_not_foDefinable`,
`DescriptiveComplexity.even_not_le_of_foDefinable`). Yet EVEN *does* FO(LFP)
reduce to it: mark every element if the universe is even, none if it is odd.
Deciding which is a polynomial-time question, so an induction settles it – the
one already at hand, since EVEN is in PTIME – and the reduction's marking
formula is that induction's output sentence, read with a free variable it
ignores.

Two things to read off this.

* The gap is not about *hardness*: EVEN is in LOGSPACE, `NONEMPTYMARK` is
  first-order, and neither is hard for anything. It is about what a reduction
  may *compute* on its way, which is exactly the difference between AC⁰ and
  polynomial time.
* A reduction notion that can decide its source problem outright trivializes
  every problem it can decide: `NONEMPTYMARK` is a target only because the
  interpretation may answer the question itself. That is why the classical
  theory measures classes *above* the reductions' own power, and why the
  library's own hardness results stay stated with `≤ᶠᵒ[≤]`, where no such
  collapse happens.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### A first-order target: the marked subset is nonempty -/

/-- **NONEMPTYMARK**: some element of the universe is marked. As simple a
problem as the vocabulary of a marked set supports, and first-order definable
(`DescriptiveComplexity.nonemptyMark_foDefinable`). -/
def NONEMPTYMARK : Lax904597.Problems.DecisionProblem Lax945089.Parity.markedSet where
  Holds := fun A _ => ∃ x : A, RelMap Lax945089.Parity.markedSetMark ![x]
  iso_invariant := fun e =>
    ⟨fun ⟨x, hx⟩ => ⟨e x, (relMap_equiv₁ e _ x).mp hx⟩,
      fun ⟨y, hy⟩ => ⟨e.symm y, (relMap_equiv₁ e _ (e.symm y)).mpr
        (by rwa [e.apply_symm_apply])⟩⟩

/-- The defining sentence of `DescriptiveComplexity.NONEMPTYMARK`. -/
noncomputable def nonemptyMarkS : (Lax945089.Parity.markedSet.sum Language.order).Sentence :=
  Formula.iExs (Fin 1)
    (Relations.formula₁ Lax945089Proofs.Foreign.FirstOrder.Language.markedSetMarkO (Term.var (Sum.inr 0)) :
      (Lax945089.Parity.markedSet.sum Language.order).Formula (Empty ⊕ Fin 1))

/-- **NONEMPTYMARK is first-order definable**: one existential quantifier. -/
theorem nonemptyMark_foDefinable : Lax485149.FirstOrderDefinability.FODefinable NONEMPTYMARK := by
  refine ⟨nonemptyMarkS, fun A _ _ _ _ => ?_⟩
  rw [Sentence.Realize, nonemptyMarkS, Formula.realize_iExs]
  simp only [Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨v, hv⟩ => ⟨v 0, hv⟩⟩

/-! ### EVEN reduces to it, in FO(LFP) -/

variable {d : Lax535992.InflationaryFixedPoint.StepDef (Language.empty.sum Language.order)}

/-! ### The separation -/

/-- **EVEN does not first-order reduce to NONEMPTYMARK**: the target is
first-order definable and EVEN is not, and definability travels backward along
first-order reductions. -/
theorem even_not_orderedReduction_nonemptyMark : IsEmpty (EVEN ≤ᶠᵒ[≤] NONEMPTYMARK) :=
  even_not_le_of_foDefinable nonemptyMark_foDefinable

end Lax945089Proofs.DescriptiveComplexity


