/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Reduction

/-!
# Restricting a counting problem to a definable class of instances

#2SAT, #HORN-SAT or #Monotone-2SAT count the models of a CNF formula *of a
certain shape*, and are `0` on every other formula. That is #SAT restricted
to a first-order definable class of instances
(`DescriptiveComplexity.CountingProblem.restrict`), and two facts carry over
from the unrestricted problem: membership in `#P`, by one more conjunct in
the kernel (`DescriptiveComplexity.SharpPDefinable.restrict`), and one-call
hardness, by any one-call reduction whose outputs all lie in the class
(`DescriptiveComplexity.OneCallReduction.restrict`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

open Classical in
/-- **A counting problem restricted to the instances satisfying a sentence**:
the count on those, `0` on the others. -/
noncomputable def CountingProblem.restrict (C : CountingProblem L) (P : L.Sentence) :
    CountingProblem L where
  Count := fun A inst => if @Sentence.Realize L A inst P then C A else 0
  iso_invariant := fun {A B} _ _ e => by
    rw [StrongHomClass.realize_sentence e P, C.iso_invariant e]

theorem CountingProblem.restrict_of_realize (C : CountingProblem L) (P : L.Sentence) (A : Type)
    [L.Structure A] (h : A ⊨ P) : C.restrict P A = C A :=
  ite_eq_left h

theorem CountingProblem.restrict_of_not_realize (C : CountingProblem L) (P : L.Sentence)
    (A : Type) [L.Structure A] (h : ¬A ⊨ P) : C.restrict P A = 0 :=
  ite_eq_right h

/-- The sentence `P`, read over the vocabulary of a counting kernel. -/
def kernelLift (B : SOBlock) (P : L.Sentence) : ((L.sum Language.order).sum B.lang).Sentence :=
  LHom.sumInl.onSentence (LHom.sumInl.onSentence P)

omit [L.IsRelational] in
theorem realize_kernelLift (B : SOBlock) (P : L.Sentence) (A : Type) [L.Structure A]
    [LinearOrder A] (ρ : B.Assignment A) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (kernelLift B P)) ↔ A ⊨ P := by
  let := B.structure ρ
  rw [kernelLift, LHom.realize_onSentence, LHom.realize_onSentence]

/-- **Restriction keeps `#P`-definability**: the restricting sentence is one
more conjunct of the kernel. -/
theorem SharpPDefinable.restrict {C : CountingProblem L} (hC : SharpPDefinable C)
    (P : L.Sentence) : SharpPDefinable (C.restrict P) := by
  obtain ⟨B, φ, hφ⟩ := hC
  refine ⟨B, φ ⊓ kernelLift B P, fun A _ _ _ _ => ?_⟩
  have hk : ∀ ρ : B.Assignment A,
      (@Sentence.Realize _ A (@sumStructure _ _ A _ (B.structure ρ)) (φ ⊓ kernelLift B P)) ↔
        (@Sentence.Realize _ A (@sumStructure _ _ A _ (B.structure ρ)) φ) ∧ A ⊨ P :=
    fun ρ => by
      let := B.structure ρ
      exact Formula.realize_inf.trans (and_congr Iff.rfl (realize_kernelLift B P A ρ))
  by_cases hP : A ⊨ P
  · rw [C.restrict_of_realize P A hP, hφ A]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun ρ => ((hk ρ).trans (and_iff_left hP)).symm)
  · rw [C.restrict_of_not_realize P A hP]
    refine (Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨ρ, hρ⟩ => hP ((hk ρ).mp hρ).2⟩)).symm

/-- **A one-call reduction whose outputs all satisfy `P` is a one-call
reduction into the restriction to `P`.** -/
noncomputable def OneCallReduction.restrict {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ᶜ[≤] D) (P : L'.Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      f.toRelInterpretation.MapRel A ⊨ P) : C ≤ᶜ[≤] D.restrict P :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    post := f.post
    correct := fun A _ _ _ _ => by
      rw [D.restrict_of_realize P _ (h A)]
      exact f.correct A }

end DescriptiveComplexity
