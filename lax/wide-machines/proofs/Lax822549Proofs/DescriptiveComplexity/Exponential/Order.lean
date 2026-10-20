/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Exponential.Expansion
import Lax822549Proofs.DescriptiveComplexity.OrderWalk
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax822549Proofs.DescriptiveComplexity.ExpExpansion
end Lax822549Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The order on an expanded universe

An exponential expansion's sentences see the order of the structure they expand
(`DescriptiveComplexity.ExpExpansion`). To compose an expansion with anything
that reads *its* order – which is what a complete problem for an exponential
class needs – that order must in turn be **definable by a first-order sentence
over the base**. It is, and this file builds it: the analogue, one level up, of
`DescriptiveComplexity.tagTupleOrder` and
`DescriptiveComplexity.FOInterpretation.ordExtend`.

## The order

Points of the expanded universe are tagged block assignments. Order them by
tag first – statically, by an arbitrary linear order on the finite tag type –
and then by reading an assignment as a **binary number**: `ρ` is below `σ` when,
at the least atom where they differ, `σ` holds and `ρ` does not.

“Atom” here means a relation variable of the block together with a tuple of
elements. Arities differ from variable to variable, so the atoms are indexed by
a dependent sum; this file avoids it by **padding** every tuple to the block's
maximal arity (`DescriptiveComplexity.blockArityBound`), which turns the index
type into a plain product `B.ι × (Fin D → A)` – exactly the shape
`DescriptiveComplexity.tagTupleOrder` already orders. Padding loses nothing:
an assignment is determined by the atoms it makes true
(`DescriptiveComplexity.SOBlock.atomSet_injective`), since every tuple of the
relevant arity is the prefix of some padded tuple.

## Layers

1. `DescriptiveComplexity.setLinearOrder` – the binary-number order on the
   subsets of any finite linearly ordered index type, obtained from Mathlib's
   `Pi.Lex` on functions to `Bool`, so that transitivity and totality are
   inherited rather than proved.
2. `DescriptiveComplexity.SOBlock.atomSet` – an assignment read as such a
   subset, and its injectivity.
3. `DescriptiveComplexity.ExpExpansion.mapLinearOrder` – the two put together
   with the tag, and transported to the subtype `X.Map A`.

The defining *formula* and its realization lemma live in
`DescriptiveComplexity.Exponential.OrdFormula`; this file is the semantics it
is proved against.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The binary-number order on subsets of a finite linear order -/

section SetOrder

variable {I : Type}

open Classical in
/-- The key ordering subsets of `I`: the characteristic function, read
lexicographically with `False < True`. -/
private noncomputable def setKey (S : I → Prop) : Lex (I → Bool) :=
  toLex fun i => decide (S i)

open Classical in
private theorem setKey_injective : Function.Injective (setKey (I := I)) := by
  intro S T h
  funext i
  exact propext (decide_eq_decide.mp (congrFun (toLex.injective h) i))

variable (I) in
/-- **The binary-number order on subsets** of a finite linearly ordered index
type: one subset is below another when, at the least index where they differ,
the second contains it and the first does not. Lifted from `Pi.Lex`, so the
linear-order axioms come for free. -/
@[instance_reducible]
noncomputable def setLinearOrder [LinearOrder I] [Finite I] : LinearOrder (I → Prop) :=
  LinearOrder.lift' setKey setKey_injective

/-- **What the order says**, unfolded. -/
theorem setLinearOrder_lt_iff [LinearOrder I] [Finite I] (S T : I → Prop) :
    (setLinearOrder I).lt S T ↔ ∃ i, (∀ j, j < i → (S j ↔ T j)) ∧ ¬S i ∧ T i := by
  classical
  have he : ∀ (U V : I → Prop) (i : I), (decide (U i) = decide (V i)) ↔ (U i ↔ V i) :=
    fun _ _ _ => decide_eq_decide
  have hb : ∀ (U V : I → Prop) (i : I), (decide (U i) < decide (V i)) ↔ (¬U i ∧ V i) := by
    intro U V i
    by_cases hu : U i <;> by_cases hv : V i <;> simp [hu, hv]
  have hlt : (setLinearOrder I).lt S T ↔ setKey S < setKey T := Iff.rfl
  rw [hlt]
  constructor
  · rintro ⟨i, hag, hi⟩
    exact ⟨i, fun j hj => (he S T j).mp (hag j hj), (hb S T i).mp hi⟩
  · rintro ⟨i, hag, hi⟩
    exact ⟨i, fun j hj => (he S T j).mpr (hag j hj), (hb S T i).mpr hi⟩

end SetOrder

/-! ### An assignment read as a set of padded atoms -/

namespace SOBlock

end SOBlock

/-! ### The order on the points of an expansion -/

namespace ExpExpansion

end ExpExpansion

end Lax822549Proofs.DescriptiveComplexity


