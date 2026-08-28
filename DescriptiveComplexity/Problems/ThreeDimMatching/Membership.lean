/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import DescriptiveComplexity.SecondOrder

/-!
# 3-dimensional matching is existential second-order definable

The membership half of its NP-completeness
(`DescriptiveComplexity.threeDimMatching_sigmaSODefinable`): a matching *is* a
relation, so a single existential block guesses it – ternary, the first of the
catalog – and the kernel spells out the seven conditions of
`DescriptiveComplexity.IsMatchingOn`: that the guessed triples are available ones
inside the three classes, that every marked element is covered, and that no
two triples share a coordinate.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition: the matching, a
ternary relation. -/
fo_block tdmGuessBlock over Language.tripleSys ts into tdmSOLang with t where
  /-- The guessed matching. -/
  matching : 3

/-- The guessed matching, as an atom. -/
private def matF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  fo%[x, y, z] tMatchingSym(x, y, z)

/-- The available triples, as an atom. -/
private def tripF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  fo%[x, y, z] tTripSym(x, y, z)

/-- Kernel conjunct: the guessed triples are available ones, inside the three
classes. -/
private noncomputable def tdmSubClause : tdmSOLang.Sentence :=
  fo% ∀ x y z,
    matF⟨x, y, z⟩ → ((tripF⟨x, y, z⟩ ∧ tXElSym(x)) ∧ tYElSym(y)) ∧ tZElSym(z)

/-- Kernel conjunct: every element of the first class is covered. -/
private noncomputable def tdmCovXClause : tdmSOLang.Sentence :=
  fo% ∀ x, tXElSym(x) → ∃ y z, matF⟨x, y, z⟩

/-- Kernel conjunct: every element of the second class is covered. -/
private noncomputable def tdmCovYClause : tdmSOLang.Sentence :=
  fo% ∀ y, tYElSym(y) → ∃ x z, matF⟨x, y, z⟩

/-- Kernel conjunct: every element of the third class is covered. -/
private noncomputable def tdmCovZClause : tdmSOLang.Sentence :=
  fo% ∀ z, tZElSym(z) → ∃ x y, matF⟨x, y, z⟩

/-- Kernel conjunct: two triples sharing their first coordinate coincide. -/
private noncomputable def tdmUniqXClause : tdmSOLang.Sentence :=
  fo% ∀ x y z y' z', matF⟨x, y, z⟩ ∧ matF⟨x, y', z'⟩ → y ≐ y' ∧ z ≐ z'

/-- Kernel conjunct: two triples sharing their second coordinate coincide. -/
private noncomputable def tdmUniqYClause : tdmSOLang.Sentence :=
  fo% ∀ x y z x' z', matF⟨x, y, z⟩ ∧ matF⟨x', y, z'⟩ → x ≐ x' ∧ z ≐ z'

/-- Kernel conjunct: two triples sharing their third coordinate coincide. -/
private noncomputable def tdmUniqZClause : tdmSOLang.Sentence :=
  fo% ∀ x y z x' y', matF⟨x, y, z⟩ ∧ matF⟨x', y', z⟩ → x ≐ x' ∧ y ≐ y'

/-- The first-order kernel of the `Σ₁` definition: the guessed relation is a
matching. -/
noncomputable def tdmKernel : tdmSOLang.Sentence :=
  tdmSubClause ⊓ (tdmCovXClause ⊓ (tdmCovYClause ⊓ (tdmCovZClause ⊓
    (tdmUniqXClause ⊓ (tdmUniqYClause ⊓ tdmUniqZClause)))))

section Realize

variable {A : Type} [Language.tripleSys.Structure A]

/-- Realization of the kernel under an assignment of the guessed matching. -/
private theorem realize_tdmKernel (ρ : tdmGuessBlock.Assignment A) :
    (@Sentence.Realize tdmSOLang A
        (@sumStructure _ _ A _ (tdmGuessBlock.structure ρ)) tdmKernel) ↔
      IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip
        (fun x y z => ρ .matching ![x, y, z]) := by
  let := tdmGuessBlock.structure ρ
  have hsub : ∀ w : Fin 3 → A, RelMap (L := tdmSOLang) (M := A) tMatchingSym w ↔ ρ .matching w :=
    fun _ => Iff.rfl
  rw [tdmKernel, IsMatchingOn]
  simp only [tdmSubClause, tdmCovXClause, tdmCovYClause, tdmCovZClause, tdmUniqXClause,
    tdmUniqYClause, tdmUniqZClause, matF, tripF, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp, Formula.realize_equal,
    Formula.realize_rel₁, realize_rel₃, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x y z hm => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h y hy => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h z hz => ?_, fun h i hi => ?_⟩
          (and_congr ⟨fun h x y z y' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
            (and_congr ⟨fun h x y z x' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
              ⟨fun h x y z x' y' h₁ h₂ => ?_, fun h i hi => ?_⟩)))))
  · have h' := h ![x, y, z] hm
    exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩
  · have h' := h (i 0) (i 1) (i 2) hi
    exact ⟨⟨⟨h'.1, h'.2.1⟩, h'.2.2.1⟩, h'.2.2.2⟩
  · obtain ⟨w, hw⟩ := h (fun _ => x) hx
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨y, z, hyz⟩ := h (i 0) hi
    exact ⟨![y, z], hyz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => y) hy
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, z, hxz⟩ := h (i 0) hi
    exact ⟨![x, z], hxz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => z) hz
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, y, hxy⟩ := h (i 0) hi
    exact ⟨![x, y], hxy⟩
  · exact h ![x, y, z, y', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', y'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2

end Realize

/-- **3-dimensional matching is `Σ₁`-definable**: existentially guess the
matching – a ternary relation – then check first-order that it is one. Since
NP is defined as `Σ₁`-definability, this is the membership half of its
NP-completeness. -/
theorem threeDimMatching_sigmaSODefinable : SigmaSODefinable 1 ThreeDimMatching := by
  refine ⟨[tdmGuessBlock], rfl, tdmKernel, ?_⟩
  intro A _ _ _
  rw [show ThreeDimMatching.Holds A = HasThreeDimMatching A from rfl, HasThreeDimMatching,
    and_iff_right ‹Finite A›]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨fun i => match i with | .matching => fun w : Fin 3 → A => M (w 0) (w 1) (w 2),
      (realize_tdmKernel _).mpr hM⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨_, (realize_tdmKernel ρ).mp hρ⟩

end SigmaOne

end DescriptiveComplexity
