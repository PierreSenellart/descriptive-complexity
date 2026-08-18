/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RelExp

/-!
# The expansion, relativized to the marked part

The doubled universe of `DescriptiveComplexity.Problems.Wide.Double` is never a
singleton, which is what the machine needs, but it is no longer the instance.
`DescriptiveComplexity.Draw.relExp` repairs that on the expansion's side: every
sentence of the expansion is renamed and relativized to the mark, and every
block assignment is required to be **supported** – to hold only of marked tuples
– so that a point of the relativized expansion over the doubled universe is a
point of the original expansion over the instance.

One tag is added. `FirstOrder.Language.ExpExpansion` requires its domain
sentence to be satisfiable at *every* structure, including ones with no marked
part at all, where a relativized sentence has nothing to be about; the tag
`none` is the point that exists exactly there, and over a doubled universe – one
that always has a marked part – it contributes nothing.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Two sentences about a structure with no marked part -/

section Fallback

variable (L : Language.{0, 0}) [L.IsRelational] (B : SOBlock)

/-- **No element is marked**, as a sentence. -/
noncomputable def noOldSentence : (((newLang L).sum Language.order).sum B.lang).Sentence :=
  Formula.iAlls (Fin 1) (∼(Relations.formula₁ (oldGuard (L := L) B) (Term.var (Sum.inr 0))))

open Classical in
/-- **Every relation variable of the block is empty**, as a sentence. -/
noncomputable def emptyBlocksSentence :
    (((newLang L).sum Language.order).sum B.lang).Sentence :=
  letI := Fintype.ofFinite B.ι
  listInf ((Finset.univ : Finset B.ι).toList.map fun i =>
    Formula.iAlls (Fin (B.arity i))
      (∼(Relations.formula (blkSym L B i) fun k => Term.var (Sum.inr k))))

variable {L B}
variable {M : Type} [(newLang L).Structure M] [LinearOrder M]

omit [L.IsRelational] in
theorem realize_noOldSentence (ρ : B.Assignment M) :
    @Sentence.Realize _ M (B.structure₁ ρ) (noOldSentence L B) ↔
      ∀ x : M, ¬RelMap (oldNewSym L) ![x] := by
  letI := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [noOldSentence]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

omit [L.IsRelational] in
theorem realize_emptyBlocksSentence (ρ : B.Assignment M) :
    @Sentence.Realize _ M (B.structure₁ ρ) (emptyBlocksSentence L B) ↔
      ∀ (i : B.ι) (w : Fin (B.arity i) → M), ¬ρ i w := by
  classical
  letI := Fintype.ofFinite B.ι
  letI := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [emptyBlocksSentence]
  simp only [Sentence.Realize, realize_listInf, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro h i w hw
    have hi := h _ i rfl
    rw [Formula.realize_iAlls] at hi
    exact (Formula.realize_not.mp (hi w)) (by
      rw [Formula.realize_rel]
      exact hw)
  · rintro h ψ i rfl
    rw [Formula.realize_iAlls]
    intro w
    rw [Formula.realize_not, Formula.realize_rel]
    exact h i _

end Fallback

/-! ### The relativized expansion -/

section RelExpansion

variable {L : Language.{0, 0}} [L.IsRelational]

open Classical in
/-- **The expansion, relativized to the marked part**: the same block and the
same expanded vocabulary, every sentence renamed and relativized, every
assignment required to be supported, and one extra tag for the structures with
no marked part. -/
noncomputable def relExp (X : ExpExpansion L) : ExpExpansion (newLang L) where
  Tag := Option X.Tag
  B := X.B
  E := X.E
  dom t :=
    match t with
    | some t =>
      relativizeTo (oldGuard (L := L) X.B) ((newBlockLHom X.B).onSentence (X.dom t)) ⊓
        suppSentence L X.B
    | none => noOldSentence L X.B ⊓ emptyBlocksSentence L X.B
  relSentence {n} r τ :=
    if h : ∃ σ : Fin n → X.Tag, ∀ i, τ i = some (σ i) then
      relativizeTo (oldGuard (L := L) (X.B.replicate n))
        ((newBlockLHom (X.B.replicate n)).onSentence (X.relSentence r h.choose))
    else ⊥
  dom_nonempty := by
    classical
    intro M _ _ _ _
    by_cases hne : Nonempty (MarkPart L M)
    · obtain ⟨t, ρ₀, h⟩ := X.dom_nonempty (MarkPart L M)
      refine ⟨some t, extAssignM X.B ρ₀, ?_⟩
      letI := X.B.structure₁ (L := (newLang L).sum Language.order) (extAssignM X.B ρ₀)
      refine Formula.realize_inf.mpr ⟨?_, ?_⟩
      · exact (realize_relOldMark X.B ρ₀ (X.dom t)).mpr h
      · exact (realize_suppSentence X.B (extAssignM X.B ρ₀)).mpr
          (supported_extAssignM X.B ρ₀)
    · refine ⟨none, (fun _ _ => False), ?_⟩
      letI := X.B.structure₁ (L := (newLang L).sum Language.order)
        (show X.B.Assignment M from fun _ _ => False)
      refine Formula.realize_inf.mpr ⟨?_, ?_⟩
      · exact (realize_noOldSentence (fun _ _ => False)).mpr fun x hx =>
          hne ⟨MarkPart.mk x hx⟩
      · exact (realize_emptyBlocksSentence (fun _ _ => False)).mpr fun _ _ h => h

end RelExpansion

end Draw

end DescriptiveComplexity
