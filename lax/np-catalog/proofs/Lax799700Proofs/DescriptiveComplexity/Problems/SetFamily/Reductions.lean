/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
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
# Set Cover and Hitting Set are transposes of each other

The inter-reduction inside the set family, the counterpart of the
complementation reductions of
`Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions`: the two problems are the
same condition read in the two directions of the incidence relation, so a
single interpretation of tag `Unit` and dimension 1
(`Lax799700Proofs.DescriptiveComplexity.transposeInterp`) – exchange the two unary marks, transpose
the incidence relation, keep the threshold – reduces each of them to the
other (`Lax799700Proofs.DescriptiveComplexity.setCover_fo_reduction_hittingSet` and
`Lax799700Proofs.DescriptiveComplexity.hittingSet_fo_reduction_setCover`), quantifier-free.

Set Packing has no such partner: its condition is not the transpose of
another problem of the family, and its hardness comes from graphs directly
(`Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.FromGraphs`).
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Set Cover and Hitting Set are transposes of each other -/

/-- The transposing interpretation: ground elements and sets of the family
exchange their marks, incidence is read backwards, the threshold is kept. -/
def transposeInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.SetFamily.setSystem Lax799700.SetFamily.setSystem Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssFam (FirstOrder.Language.Term.var (0, 0))
    | _, .fam => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssElem (FirstOrder.Language.Term.var (0, 0))
    | _, .mem => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.SetFamily.ssMem (FirstOrder.Language.Term.var (1, 0)) (FirstOrder.Language.Term.var (0, 0))
    | _, .marked => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssMarked (FirstOrder.Language.Term.var (0, 0))

section TransposeCharacterizations

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A]

@[simp]
theorem transpose_elem (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssElem ![((), w)] ↔ RelMap Lax799700.SetFamily.ssFam ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_fam (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssFam ![((), w)] ↔ RelMap Lax799700.SetFamily.ssElem ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_mem (w₁ w₂ : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssMem ![((), w₁), ((), w₂)] ↔
      RelMap Lax799700.SetFamily.ssMem ![w₂ 0, w₁ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₂]

@[simp]
theorem transpose_marked (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssMarked ![((), w)] ↔ RelMap Lax799700.SetFamily.ssMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

end TransposeCharacterizations

section TransposeCorrectness

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A]

private theorem transpose_hElem :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSElem b ↔ Lax799700.SetFamily.SSFam (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_elem w

private theorem transpose_hFam :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSFam b ↔ Lax799700.SetFamily.SSElem (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_fam w

private theorem transpose_hMem :
    ∀ b b' : transposeInterp.Map A,
      Lax799700.SetFamily.SSMem b b' ↔ Lax799700.SetFamily.SSMem (transposeInterp.mapEquivSelf A b')
        (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact transpose_mem w w'

private theorem transpose_hMarked :
    ∀ b : transposeInterp.Map A,
      Lax799700.SetFamily.SSMarked b ↔ Lax799700.SetFamily.SSMarked (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_marked w

/-- Correctness of the transposition, hitting-set-to-set-cover direction: a
hitting set of a set system is a cover of its transpose. -/
theorem hasSmallHittingSet_iff_map :
    Lax799700.SetFamily.HasSmallHittingSet A ↔ Lax799700.SetFamily.HasSmallSetCover (transposeInterp.Map A) :=
  and_congr ((transposeInterp.mapEquivSelf A).finite_iff).symm
    (CoversOn.equiv_iff (transposeInterp.mapEquivSelf A) (transpose_hElem A)
      (transpose_hFam A) (transpose_hMem A) (transpose_hMarked A)).symm

/-- Correctness of the transposition, set-cover-to-hitting-set direction: a
cover of a set system is a hitting set of its transpose. -/
theorem hasSmallSetCover_iff_map :
    Lax799700.SetFamily.HasSmallSetCover A ↔ Lax799700.SetFamily.HasSmallHittingSet (transposeInterp.Map A) :=
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
  correct A _ _ _ := hasSmallSetCover_iff_map A

/-- **Hitting Set FO-reduces to Set Cover**, by transposing the incidence
relation. -/
def hittingSet_fo_reduction_setCover : HittingSet ≤ᶠᵒ SetCover where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := hasSmallHittingSet_iff_map A

end Lax799700Proofs.DescriptiveComplexity


