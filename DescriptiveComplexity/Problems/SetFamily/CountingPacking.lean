/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.FromGraphs
import DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Set Packing

The counting version of `DescriptiveComplexity.SetPacking`: the number of pairwise
disjoint subfamilies with exactly as many sets as the marked set
(`DescriptiveComplexity.PackingOfSize`). It is parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpSetPacking_sharpP_parsimoniousComplete`).

Membership is the generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), the order-free part being
“the subfamily is a packing”. Hardness is the edge-incidence interpretation of
`DescriptiveComplexity.Problems.SetFamily.FromGraphs` unchanged: the sets of the
interpreted system are the vertices, one each, so its packings of a size are
the independent sets of that size, bijectively
(`DescriptiveComplexity.packEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Language.setSystem.Structure A]

/-- The subfamily `G` is a packing with exactly as many sets as the marked set,
in a finite set system. -/
def PackingOfSize (G : A → Prop) : Prop :=
  Finite A ∧ (∀ s, G s → SSFam s) ∧
    (∀ s s', G s → G s' → s ≠ s' → ∀ x : A, SSElem x → ¬(SSMem x s ∧ SSMem x s')) ∧
    {s | G s}.ncard = {x : A | SSMarked x}.ncard

variable {A} {B : Type} [Language.setSystem.Structure B]

/-- Packings of the threshold size transport along an isomorphism. -/
theorem PackingOfSize.map (e : A ≃[Language.setSystem] B) {G : A → Prop}
    (h : PackingOfSize A G) : PackingOfSize B fun b => G (e.toEquiv.symm b) := by
  obtain ⟨hfin, hfam, hdisj, hcard⟩ := h
  have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply
  refine ⟨Finite.of_equiv A e.toEquiv, fun s hs => ?_, fun s s' hs hs' hne x hx hmem => ?_, ?_⟩
  · have h := (relMap_equiv₁ e ssFam (e.toEquiv.symm s)).mp (hfam _ hs)
    rw [hsymm] at h
    exact h
  · refine hdisj _ _ hs hs' (fun h => hne (e.toEquiv.symm.injective h)) (e.toEquiv.symm x)
      ((relMap_equiv₁ e ssElem (e.toEquiv.symm x)).mpr ?_)
      ⟨(relMap_equiv₂ e ssMem (e.toEquiv.symm x) (e.toEquiv.symm s)).mpr ?_,
        (relMap_equiv₂ e ssMem (e.toEquiv.symm x) (e.toEquiv.symm s')).mpr ?_⟩
    · rw [hsymm]
      exact hx
    · rw [hsymm, hsymm]
      exact hmem.1
    · rw [hsymm, hsymm]
      exact hmem.2
  · exact ((ncard_setOf_symm e.toEquiv G).symm.trans hcard).trans
      (ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e ssMarked a)

end Solutions

/-- **#Set Packing**: the number of pairwise disjoint subfamilies with exactly
as many sets as the marked set. -/
noncomputable def SharpSetPacking : CountingProblem Language.setSystem where
  Count := fun A inst => Nat.card {G : A → Prop // @PackingOfSize A inst G}
  iso_invariant := fun {A B} _ _ e => by
    refine Nat.card_congr
      { toFun := fun G => ⟨fun b => G.1 (e.toEquiv.symm b), G.2.map e⟩
        invFun := fun T => ⟨fun a => T.1 (e.toEquiv a), ?_⟩
        left_inv := fun G => Subtype.ext (funext fun a => by simp)
        right_inv := fun T => Subtype.ext (funext fun b => by simp) }
    have h := T.2.map e.symm
    exact h

theorem sharpSetPacking_apply (A : Type) [Language.setSystem.Structure A] :
    SharpSetPacking A = Nat.card {G : A → Prop // PackingOfSize A G} :=
  rfl

/-- **The support of #Set Packing is Set Packing**: a packing at least as large
as the marked set contains one of exactly that size.
Registered in the Lax archive as
[`Lax280166.SetPackingComplete.sharpSetPacking_support_iff`](https://laxarchive.org/lax-280166/Lax280166.SetPackingComplete.html#s-Lax280166.SetPackingComplete.sharpSetPacking_support_iff). -/
theorem sharpSetPacking_support_iff (A : Type) [Language.setSystem.Structure A] [Finite A] :
    SharpSetPacking.support A ↔ SetPacking A := by
  rw [CountingProblem.support_iff, sharpSetPacking_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨G, hfin, hfam, hdisj, hcard⟩, -⟩
    exact ⟨hfin, G, hfam, hdisj, hcard.ge⟩
  · rintro ⟨hfin, G, hfam, hdisj, hcard⟩
    obtain ⟨T, hTG, hT⟩ := Set.exists_subset_card_eq hcard
    exact ⟨⟨⟨fun s => s ∈ T, hfin, fun s hs => hfam s (hTG hs),
      fun s s' hs hs' => hdisj s s' (hTG hs) (hTG hs'), hT⟩⟩, inferInstance⟩

/-! ### Membership -/

/-- The block of the counting definition of Set Packing: the packing
itself. -/
fo_block packSelBlock over Language.setSystem ss into packSelLang with ps where
  /-- The packing. -/
  sel : 1

instance : Subsingleton packSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Set Packing: the guessed subfamily consists of
sets of the family, pairwise disjoint. -/
noncomputable def packSelKernel : packSelLang.Sentence :=
  fo% (∀ s, psSelSym(s) → psFamSym(s)) ∧
    ∀ s t x, ((psSelSym(s) ∧ psSelSym(t)) ∧ ¬ s ≐ t) ∧ psElemSym(x) →
      ¬ (psMemSym(x, s) ∧ psMemSym(x, t))

/-- Realization of the order-free kernel of #Set Packing. -/
theorem realize_packSelKernel {A : Type} [Language.setSystem.Structure A]
    (ρ : packSelBlock.Assignment A) :
    (@Sentence.Realize packSelLang A
        (@sumStructure _ _ A _ (packSelBlock.structure ρ)) packSelKernel) ↔
      (∀ s : A, (ρ .sel fun _ => s) → SSFam s) ∧
        ∀ s s' : A, (ρ .sel fun _ => s) → (ρ .sel fun _ => s') → s ≠ s' →
          ∀ x : A, SSElem x → ¬(SSMem x s ∧ SSMem x s') := by
  let := packSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := packSelLang) (M := A) psSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [packSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  refine and_congr ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩
    ⟨fun h s s' hs hs' hne x hx => h ![s, s', x] ⟨⟨⟨hs, hs'⟩, hne⟩, hx⟩,
      fun h i hi => h (i 0) (i 1) hi.1.1.1 hi.1.1.2 hi.1.2 (i 2) hi.2⟩

/-- **#Set Packing is in `#P`.** -/
theorem sharpSetPacking_mem_sharpP : SharpSetPacking ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpSetPacking packSelBlock ssMarked .sel rfl packSelKernel
    (fun A _ G => (∀ s : A, G s → SSFam s) ∧
      ∀ s s' : A, G s → G s' → s ≠ s' → ∀ x : A, SSElem x → ¬(SSMem x s ∧ SSMem x s'))
    (fun _ _ ρ => realize_packSelKernel ρ)
    fun _ _ hfin => Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => (and_iff_right hfin).trans and_assoc.symm)

/-! ### Hardness -/

section Hardness

variable {A : Type} [Language.markedGraph.Structure A]

/-- The vertex-sets of an independent set of the threshold size are a packing
of the threshold size. -/
theorem packingOfSize_vertexFamily {S : A → Prop} (h : IndepOfSize A S) :
    PackingOfSize (edgeIncidenceInterp.Map A) (vertexFamily S) := by
  obtain ⟨hfin, hS, hcard⟩ := h
  have := hfin
  refine ⟨edgeIncidenceInterp.map_finite A, ?_, ?_,
    (ncard_vertexFamily S).trans (hcard.trans (ncard_marked A).symm)⟩
  · rintro s ⟨v, -, rfl⟩
    exact (edgeIncidence_fam ![v, v]).mpr (by simp)
  · rintro s s' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ hne x hx ⟨hmu, hmv⟩
    have huv : u ≠ v := fun h => hne (by rw [h])
    rcases (exists_elem_mem_both_iff huv).mp ⟨x, hx, hmu, hmv⟩ with h | h
    · exact hS u v hu hv huv h
    · exact hS v u hv hu huv.symm h

/-- A packing of the interpreted system consists of vertex-sets. -/
theorem packing_diag {G : edgeIncidenceInterp.Map A → Prop}
    (h : PackingOfSize (edgeIncidenceInterp.Map A) G) :
    ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
  rintro ⟨⟨⟩, w⟩ hw
  exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
    ⟨rfl, ((edgeIncidence_fam w).mp (h.2.1 _ hw)).symm⟩⟩

/-- The vertices of a packing of the threshold size are an independent set of
the threshold size. -/
theorem indepOfSize_of_packing {G : edgeIncidenceInterp.Map A → Prop}
    (h : PackingOfSize (edgeIncidenceInterp.Map A) G) :
    IndepOfSize A fun v => G (diagPt v) := by
  have hdiag := packing_diag h
  obtain ⟨hfin, -, hdisj, hcard⟩ := h
  refine ⟨Finite.of_injective _ (diagPt_injective (A := A)), fun u v hu hv huv hadj => ?_,
    (ncard_diag_eq _ G hdiag fun _ => Iff.rfl).symm.trans (hcard.trans (ncard_marked A))⟩
  obtain ⟨x, hx, hmu, hmv⟩ := (exists_elem_mem_both_iff huv).mpr (Or.inl hadj)
  exact hdisj _ _ hu hv (fun h => huv (diagPt_injective h)) x hx ⟨hmu, hmv⟩

variable (A) in
/-- **The packings of the threshold size of the edge-incidence system are the
independent sets of the threshold size**, bijectively. -/
def packEquiv :
    {S : A → Prop // IndepOfSize A S} ≃
      {G : edgeIncidenceInterp.Map A → Prop //
        PackingOfSize (edgeIncidenceInterp.Map A) G} where
  toFun S := ⟨vertexFamily S.1, packingOfSize_vertexFamily S.2⟩
  invFun G := ⟨fun v => G.1 (diagPt v), indepOfSize_of_packing G.2⟩
  left_inv S := Subtype.ext (funext fun v => propext
    ⟨fun ⟨_, hv', heq⟩ => diagPt_injective heq ▸ hv', fun hv => ⟨v, hv, rfl⟩⟩)
  right_inv G := Subtype.ext (funext fun p => propext
    ⟨by
      rintro ⟨v, hv, rfl⟩
      exact hv,
    fun hp => by
      obtain ⟨v, rfl⟩ := packing_diag G.2 p hp
      exact ⟨v, hp, rfl⟩⟩)

end Hardness

/-- **#Independent Set reduces parsimoniously to #Set Packing**, by the
edge-incidence interpretation. -/
noncomputable def sharpIndependentSet_parsimonious_sharpSetPacking :
    SharpIndependentSet ≤ᵖ SharpSetPacking where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ _ := Nat.card_congr (packEquiv A)

/-- #Set Packing is parsimoniously `#P`-hard. -/
theorem sharpSetPacking_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpSetPacking :=
  SharpP.parsimoniousHard_of_parsimonious sharpIndependentSet_parsimonious_sharpSetPacking
    sharpIndependentSet_sharpP_parsimoniousHard

/-- **#Set Packing is parsimoniously `#P`-complete**, counting the packings of
exactly the threshold size.
Registered in the Lax archive as
[`Lax280166.SetPackingComplete.sharpSetPacking_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.SetPackingComplete.html#s-Lax280166.SetPackingComplete.sharpSetPacking_sharpP_parsimoniousComplete). -/
theorem sharpSetPacking_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpSetPacking :=
  ⟨sharpSetPacking_mem_sharpP, sharpSetPacking_sharpP_parsimoniousHard⟩

/-- `SharpSetPacking` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpSetPacking_sharpP_complete : SharpP.Complete SharpSetPacking :=
  complete_sharpP_of_parsimoniousComplete sharpSetPacking_sharpP_parsimoniousComplete

end DescriptiveComplexity
