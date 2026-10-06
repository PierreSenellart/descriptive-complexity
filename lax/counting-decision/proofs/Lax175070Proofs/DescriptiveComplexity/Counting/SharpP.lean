/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Counting
import Lax175070Proofs.DescriptiveComplexity.SecondOrderOrdered
import Mathlib.SetTheory.Cardinal.Finite
import Lax175070.CountDefinability
import Lax175070.SelectedSat
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax175070Proofs.DescriptiveComplexity.CountingProblem
end Lax175070Proofs.DescriptiveComplexity.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity.SOBlock
end Lax175070Proofs.DescriptiveComplexity.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity.SharpPDefinable
end Lax175070Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable witnessCount)
end Lax175070Proofs.DescriptiveComplexity

/-!
# Counting the witnesses of a second-order block: `#P`-definability

Fagin's theorem reads NP as the problems defined by a sentence `∃X̄. φ` with `φ`
first-order. The counting analog, due to Saluja, Subrahmanyam and Thakur
([1995][saluja1995descriptive]), reads `#P` as the functions *counting the
witnesses* of such a sentence, over ordered structures: the number of
assignments of the block `X̄` under which the first-order kernel `φ` holds.
This is also the prenex normal form `ΣX̄. φ` of the logic ΣQSO(FO) of Arenas,
Muñoz and Riveros ([2020][arenas2020descriptive]), who show that every formula
of that logic can be brought to it.

This file sets up that notion:

* `DescriptiveComplexity.witnessCount B φ A` is the number of assignments of the block
  `B` on `A` satisfying the kernel `φ`;
* `DescriptiveComplexity.SharpPDefinable C` states that the counting problem `C` is
  the witness count of some kernel *over the ordered expansion*, whatever the
  linear order of the instance. The order is a parameter here and not a guessed
  relation as in `DescriptiveComplexity.SigmaSODefinable`: guessing it would multiply
  every count by the number of linear orders;
* `DescriptiveComplexity.CountingProblem.ofKernel B φ` is the witness-counting problem
  of an order-free kernel, the counting version of the decision problem the
  kernel defines.

The closure theorem, `DescriptiveComplexity.SharpPDefinable.of_orderedParsimonious`,
pulls a kernel back through a parsimonious reduction. The decision-side
pullback of `DescriptiveComplexity.SecondOrderPull` only needs each assignment of the
pulled block to come from one of the original block; counting needs the
correspondence to be a bijection (`DescriptiveComplexity.SOBlock.pullAssignEquiv`),
which it is because the interpreted universe is all of `Tag × A^d`.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Counting witnesses -/

section Witness

variable {L : Language.{0, 0}}

/-- Transport of block assignments along an equivalence, as an equivalence. -/
def SOBlock.mapAssignEquiv (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A') :
    B.Assignment A ≃ B.Assignment A' where
  toFun := B.mapAssign e
  invFun := B.mapAssign e.symm
  left_inv ρ := by
    funext i x
    simp [SOBlock.mapAssign]
  right_inv ρ := by
    funext i x
    simp [SOBlock.mapAssign]

end Witness

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (mapAssignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Witness

variable {L : Language.{0, 0}}

/-- The witness count is isomorphism-invariant. -/
theorem witnessCount_iso (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) {A A' : Type}
    [L.Structure A] [L.Structure A'] (e : A ≃[L] A') :
    Lax366625.WitnessCounting.witnessCount B φ A = Lax366625.WitnessCounting.witnessCount B φ A' :=
  Nat.card_congr (Equiv.subtypeEquiv (B.mapAssignEquiv e.toEquiv) fun ρ =>
    @StrongHomClass.realize_sentence (L.sum B.lang) A A'
      (@sumStructure L B.lang A _ (B.structure ρ))
      (@sumStructure L B.lang A' _ (B.structure (B.mapAssign e.toEquiv ρ))) _ _ _
      (B.extendEquiv e ρ) φ)

/-- Block assignments on a finite universe are finitely many. -/
instance SOBlock.finite_assignment (B : Lax904597.SecondOrder.SOBlock) (A : Type) [Finite A] :
    Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))

end Witness

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (finite_assignment)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Witness

variable {L : Language.{0, 0}}

/-- On a finite structure, the witness count is positive exactly when there is
a witness. -/
theorem witnessCount_pos_iff (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [inst : L.Structure A] [Finite A] :
    0 < Lax366625.WitnessCounting.witnessCount B φ A ↔ ∃ ρ : B.Assignment A,
      @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ)) φ := by
  rw [Lax366625.WitnessCounting.witnessCount, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨ρ, hρ⟩, _⟩ => ⟨ρ, hρ⟩, fun ⟨ρ, hρ⟩ => ⟨⟨⟨ρ, hρ⟩⟩, inferInstance⟩⟩

end Witness

/-! ### Pulling a witness count back through an interpretation -/

section Pull

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ} {A : Type}

/-- **Pulling a witness count back through an interpretation**: the witnesses
of a kernel in the interpreted structure are, bijectively, the witnesses of the
pulled kernel, over the pulled block, in the base structure. -/
theorem witnessCount_map [L₂.IsRelational] (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (B : Lax904597.SecondOrder.SOBlock)
    (φ : (L₂.sum B.lang).Sentence) (A : Type) [instA : L₁.Structure A] :
    Lax366625.WitnessCounting.witnessCount B φ (I.Map A) =
      Lax366625.WitnessCounting.witnessCount (B.pull Tag d) ((I.extendSO B).pullSentence φ) A := by
  refine Nat.card_congr (Equiv.subtypeEquiv (B.pullAssignEquiv Tag d A) fun ρ => ?_)
  let := (B.pull Tag d).structure (B.pullAssign ρ)
  exact (@StrongHomClass.realize_sentence (L₂.sum B.lang) ((I.extendSO B).Map A) (I.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure (I.extendSO B) A)
      (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) _ _ _
      (I.extendSOEquiv B A ρ) φ).symm.trans
    ((I.extendSO B).realize_pullSentence φ A).symm

end Pull

/-! ### `#P`-definability -/

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

theorem sharpPDefinable_congr {C C' : Lax366625.CountingProblems.CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (hC : Lax366625.WitnessCounting.SharpPDefinable C) :
    Lax366625.WitnessCounting.SharpPDefinable C' := by
  obtain ⟨B, φ, hφ⟩ := hC
  exact ⟨B, φ, fun A _ _ _ _ => (h A).symm.trans (hφ A)⟩

variable {L' : Language.{0, 0}} [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}
  {D : Lax366625.CountingProblems.CountingProblem L'}

/-- **`#P`-definability is closed under ordered parsimonious reductions.** -/
theorem SharpPDefinable.of_orderedParsimonious (f : C ≤ᵖ[≤] D) (h : Lax366625.WitnessCounting.SharpPDefinable D) :
    Lax366625.WitnessCounting.SharpPDefinable C := by
  obtain ⟨B, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, (f.toInterpretation.ordExtend.extendSO B).pullSentence φ, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have : Finite (f.toInterpretation.Map A) := f.toInterpretation.map_finite A
  have : Nonempty (f.toInterpretation.Map A) := f.toInterpretation.map_nonempty A
  rw [f.correct A, hφ (f.toInterpretation.Map A),
    ← witnessCount_map f.toInterpretation.ordExtend B φ A]
  exact (witnessCount_iso B φ (f.toInterpretation.ordExtendLEquiv A)).symm

end Definable

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax175070Proofs.DescriptiveComplexity.SharpPDefinable (of_orderedParsimonious)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

variable {L' : Language.{0, 0}} [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}
  {D : Lax366625.CountingProblems.CountingProblem L'}

end Definable

/-! ### The witness-counting problem of an order-free kernel -/

section OfKernel

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The counting problem of an existential second-order sentence: the number of
witnesses of the block `B` for the first-order kernel `φ`. It is the counting
version of the decision problem `∃B. φ`, which is its support
(`DescriptiveComplexity.CountingProblem.ofKernel_support_iff`). -/
noncomputable def CountingProblem.ofKernel (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) :
    Lax366625.CountingProblems.CountingProblem L where
  Count := fun A inst => @Lax366625.WitnessCounting.witnessCount L B φ A inst
  iso_invariant := fun e => witnessCount_iso B φ e

end OfKernel

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax175070Proofs.DescriptiveComplexity.CountingProblem (ofKernel)

end Lax366625.CountingProblems.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section OfKernel

variable {L : Language.{0, 0}} [L.IsRelational]

theorem CountingProblem.ofKernel_apply (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [L.Structure A] : CountingProblem.ofKernel B φ A = Lax366625.WitnessCounting.witnessCount B φ A :=
  rfl

end OfKernel

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax175070Proofs.DescriptiveComplexity.CountingProblem (ofKernel_apply)

end Lax366625.CountingProblems.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section OfKernel

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The support of a witness-counting problem is the problem its sentence
defines. -/
theorem CountingProblem.ofKernel_support_iff (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence)
    (A : Type) [L.Structure A] [Finite A] :
    (CountingProblem.ofKernel B φ).support A ↔ Lax904597.SecondOrder.SORealize L A [B] φ true :=
  witnessCount_pos_iff B φ A

end OfKernel

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax175070Proofs.DescriptiveComplexity.CountingProblem (ofKernel_support_iff)

end Lax366625.CountingProblems.CountingProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section OfKernel

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The lift of an order-free kernel to the ordered expansion. -/
def orderFreeKernel (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  (LHom.sumMap LHom.sumInl (LHom.id B.lang)).onSentence φ

/-- The witness-counting problem of an order-free kernel is `#P`-definable: its
kernel simply ignores the order. -/
theorem sharpPDefinable_ofKernel (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) :
    Lax366625.WitnessCounting.SharpPDefinable (CountingProblem.ofKernel B φ) := by
  refine ⟨B, orderFreeKernel B φ, fun A instA _ _ _ => ?_⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun ρ => ?_)
  let := B.structure ρ
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
      (LHom.id B.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  exact (LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
    (LHom.id B.lang)) φ).symm

end OfKernel

end Lax175070Proofs.DescriptiveComplexity


