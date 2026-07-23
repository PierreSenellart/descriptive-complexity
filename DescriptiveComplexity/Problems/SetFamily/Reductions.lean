/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.Defs

/-!
# Set Cover and Hitting Set are transposes of each other

The inter-reduction inside the set family, the counterpart of the
complementation reductions of
`DescriptiveComplexity.Problems.CliqueFamily.Reductions`: the two problems are the
same condition read in the two directions of the incidence relation, so a
single interpretation of tag `Unit` and dimension 1
(`DescriptiveComplexity.transposeInterp`) – exchange the two unary marks, transpose
the incidence relation, keep the threshold – reduces each of them to the
other (`DescriptiveComplexity.setCover_fo_reduction_hittingSet` and
`DescriptiveComplexity.hittingSet_fo_reduction_setCover`), quantifier-free.

Set Packing has no such partner: its condition is not the transpose of
another problem of the family, and its hardness comes from graphs directly
(`DescriptiveComplexity.Problems.SetFamily.FromGraphs`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Set Cover and Hitting Set are transposes of each other -/

/-- The transposing interpretation: ground elements and sets of the family
exchange their marks, incidence is read backwards, the threshold is kept. -/
def transposeInterp :
    FOInterpretation Language.setSystem Language.setSystem Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun _ => ssFam.formula₁ (Term.var (0, 0))
    | _, .fam => fun _ => ssElem.formula₁ (Term.var (0, 0))
    | _, .mem => fun _ => ssMem.formula₂ (Term.var (1, 0)) (Term.var (0, 0))
    | _, .marked => fun _ => ssMarked.formula₁ (Term.var (0, 0))

/-- The transposing interpretation is quantifier-free. -/
theorem transposeInterp_isQuantifierFree : transposeInterp.IsQuantifierFree := by
  intro n R t
  cases R <;> exact (IsAtomic.rel _ _).isQF

section TransposeCharacterizations

variable {A : Type} [Language.setSystem.Structure A]

@[simp]
theorem transpose_elem (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssElem ![((), w)] ↔ RelMap ssFam ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_fam (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssFam ![((), w)] ↔ RelMap ssElem ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_mem (w₁ w₂ : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssMem ![((), w₁), ((), w₂)] ↔
      RelMap ssMem ![w₂ 0, w₁ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₂]

@[simp]
theorem transpose_marked (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssMarked ![((), w)] ↔ RelMap ssMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

end TransposeCharacterizations

section TransposeCorrectness

variable (A : Type) [Language.setSystem.Structure A]

private theorem transpose_hElem :
    ∀ b : transposeInterp.Map A,
      SSElem b ↔ SSFam (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_elem w

private theorem transpose_hFam :
    ∀ b : transposeInterp.Map A,
      SSFam b ↔ SSElem (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_fam w

private theorem transpose_hMem :
    ∀ b b' : transposeInterp.Map A,
      SSMem b b' ↔ SSMem (transposeInterp.mapEquivSelf A b')
        (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact transpose_mem w w'

private theorem transpose_hMarked :
    ∀ b : transposeInterp.Map A,
      SSMarked b ↔ SSMarked (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_marked w

/-- Correctness of the transposition, hitting-set-to-set-cover direction: a
hitting set of a set system is a cover of its transpose. -/
theorem hasSmallHittingSet_iff_map :
    HasSmallHittingSet A ↔ HasSmallSetCover (transposeInterp.Map A) :=
  and_congr ((transposeInterp.mapEquivSelf A).finite_iff).symm
    (CoversOn.equiv_iff (transposeInterp.mapEquivSelf A) (transpose_hElem A)
      (transpose_hFam A) (transpose_hMem A) (transpose_hMarked A)).symm

/-- Correctness of the transposition, set-cover-to-hitting-set direction: a
cover of a set system is a hitting set of its transpose. -/
theorem hasSmallSetCover_iff_map :
    HasSmallSetCover A ↔ HasSmallHittingSet (transposeInterp.Map A) :=
  and_congr ((transposeInterp.mapEquivSelf A).finite_iff).symm
    (CoversOn.equiv_iff (transposeInterp.mapEquivSelf A) (transpose_hFam A)
      (transpose_hElem A) (fun b b' => transpose_hMem A b' b)
      (transpose_hMarked A)).symm

end TransposeCorrectness

/-- **Set Cover FO-reduces to Hitting Set**, by transposing the incidence
relation. -/
def setCover_fo_reduction_hittingSet : SetCover ≤ᶠᵒ HittingSet where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ := hasSmallSetCover_iff_map A

/-- **Hitting Set FO-reduces to Set Cover**, by transposing the incidence
relation. -/
def hittingSet_fo_reduction_setCover : HittingSet ≤ᶠᵒ SetCover where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ := hasSmallHittingSet_iff_map A
end DescriptiveComplexity
