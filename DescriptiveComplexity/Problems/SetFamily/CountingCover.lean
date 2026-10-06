/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.CountingPacking
import DescriptiveComplexity.Problems.SetFamily.Reductions
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Set Cover and #Hitting Set

The counting versions of `DescriptiveComplexity.SetCover` and
`DescriptiveComplexity.HittingSet`, each counting the solutions of *exactly* the
threshold size:

* `DescriptiveComplexity.SharpSetCover`: the covering subfamilies with as many sets
  as the marked set;
* `DescriptiveComplexity.SharpHittingSet`: the hitting sets with as many elements as
  the marked set.

Both are parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpSetCover_sharpP_parsimoniousComplete`,
`DescriptiveComplexity.sharpHittingSet_sharpP_parsimoniousComplete`). Membership of
#Set Cover is the generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`); its hardness is the
edge-incidence interpretation unchanged, from #Vertex Cover, the sets of the
interpreted system being the vertices, one each
(`DescriptiveComplexity.coverEquiv`). #Hitting Set is #Set Cover transposed, in both
directions.

**The support is not the decision problem.** A cover smaller than the threshold
extends to one of exactly that size only while unused sets remain: with a
threshold above the size of the family, Set Cover may hold and the count be
`0`. The support of these counts is “some cover has exactly the threshold
size” (`DescriptiveComplexity.sharpSetCover_support_iff`), which implies Set Cover
(`DescriptiveComplexity.setCover_of_sharpSetCover_support`) and is not implied by it.
This is unlike #Vertex Cover, where the family is the whole universe.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A B : Type}

/-- The subfamily `G` of the `Fp`-sets covers every `Ep`-element and has
exactly as many members as the `Kp`-marked set. -/
def CoverFamOfSizeOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop)
    (G : A → Prop) : Prop :=
  (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard = {x | Kp x}.ncard

/-- The covers of the threshold size transport along an equivalence commuting
with the four predicates. -/
def coverFamOfSizeEquiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop} (hE : ∀ b, EB b ↔ EA (u b))
    (hF : ∀ b, FB b ↔ FA (u b)) (hM : ∀ b b', MB b b' ↔ MA (u b) (u b'))
    (hK : ∀ b, KB b ↔ KA (u b)) :
    {G : B → Prop // Finite B ∧ CoverFamOfSizeOn EB FB MB KB G} ≃
      {G : A → Prop // Finite A ∧ CoverFamOfSizeOn EA FA MA KA G} where
  toFun G := ⟨fun a => G.1 (u.symm a), u.finite_iff.mp G.2.1, fun s hs => by
      have h := (hF (u.symm s)).mp (G.2.2.1 _ hs)
      simpa using h, fun x hx => by
      obtain ⟨s, hs, hm⟩ := G.2.2.2.1 (u.symm x) ((hE _).mpr (by simpa using hx))
      have h := (hM _ _).mp hm
      exact ⟨u s, by simpa using hs, by simpa using h⟩,
    (ncard_setOf_symm u G.1).symm.trans (G.2.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    fun s hs => (hF s).mpr (T.2.2.1 _ hs), fun x hx => by
      obtain ⟨s, hs, hm⟩ := T.2.2.2.1 (u x) ((hE x).mp hx)
      exact ⟨u.symm s, by simpa using hs, (hM _ _).mpr (by simpa using hm)⟩,
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv G := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

end Generic

/-! ### The two counting problems -/

section Problems

variable (A : Type) [Language.setSystem.Structure A]

/-- The subfamily `G` is a cover with exactly as many sets as the marked set,
in a finite set system. -/
def SetCoverOfSize (G : A → Prop) : Prop :=
  Finite A ∧ CoverFamOfSizeOn (fun x : A => SSElem x) (fun s => SSFam s)
    (fun x s => SSMem x s) (fun x => SSMarked x) G

/-- The set `H` of ground elements is a hitting set with exactly as many
elements as the marked set, in a finite set system. -/
def HittingSetOfSize (H : A → Prop) : Prop :=
  Finite A ∧ CoverFamOfSizeOn (fun s : A => SSFam s) (fun x => SSElem x)
    (fun s x => SSMem x s) (fun x => SSMarked x) H

end Problems

/-- **#Set Cover**: the number of covering subfamilies with exactly as many
sets as the marked set. -/
noncomputable def SharpSetCover : CountingProblem Language.setSystem where
  Count := fun A inst => Nat.card {G : A → Prop // @SetCoverOfSize A inst G}
  iso_invariant := fun e => Nat.card_congr
    (coverFamOfSizeEquiv e.toEquiv (fun a => relMap_equiv₁ e ssElem a)
      (fun a => relMap_equiv₁ e ssFam a) (fun a a' => relMap_equiv₂ e ssMem a a')
      fun a => relMap_equiv₁ e ssMarked a)

/-- **#Hitting Set**: the number of hitting sets with exactly as many elements
as the marked set. -/
noncomputable def SharpHittingSet : CountingProblem Language.setSystem where
  Count := fun A inst => Nat.card {H : A → Prop // @HittingSetOfSize A inst H}
  iso_invariant := fun e => Nat.card_congr
    (coverFamOfSizeEquiv e.toEquiv (fun a => relMap_equiv₁ e ssFam a)
      (fun a => relMap_equiv₁ e ssElem a) (fun a a' => relMap_equiv₂ e ssMem a' a)
      fun a => relMap_equiv₁ e ssMarked a)

section Apply

variable (A : Type) [Language.setSystem.Structure A]

theorem sharpSetCover_apply :
    SharpSetCover A = Nat.card {G : A → Prop // SetCoverOfSize A G} :=
  rfl

theorem sharpHittingSet_apply :
    SharpHittingSet A = Nat.card {H : A → Prop // HittingSetOfSize A H} :=
  rfl

/-- The support of #Set Cover: some cover has exactly the threshold size. -/
theorem sharpSetCover_support_iff [Finite A] :
    SharpSetCover.support A ↔ ∃ G : A → Prop, SetCoverOfSize A G := by
  rw [CountingProblem.support_iff, sharpSetCover_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨G⟩, _⟩ => ⟨G.1, G.2⟩, fun ⟨G, hG⟩ => ⟨⟨⟨G, hG⟩⟩, inferInstance⟩⟩

/-- The support of #Hitting Set: some hitting set has exactly the threshold
size. -/
theorem sharpHittingSet_support_iff [Finite A] :
    SharpHittingSet.support A ↔ ∃ H : A → Prop, HittingSetOfSize A H := by
  rw [CountingProblem.support_iff, sharpHittingSet_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨H⟩, _⟩ => ⟨H.1, H.2⟩, fun ⟨H, hH⟩ => ⟨⟨⟨H, hH⟩⟩, inferInstance⟩⟩

/-- The support of #Set Cover implies Set Cover; the converse fails when the
threshold exceeds the size of the family. -/
theorem setCover_of_sharpSetCover_support [Finite A] (h : SharpSetCover.support A) :
    SetCover A := by
  obtain ⟨G, hfin, hfam, hcov, hcard⟩ := (sharpSetCover_support_iff A).mp h
  exact ⟨hfin, G, hfam, hcov, hcard.le⟩

/-- The support of #Hitting Set implies Hitting Set. -/
theorem hittingSet_of_sharpHittingSet_support [Finite A] (h : SharpHittingSet.support A) :
    HittingSet A := by
  obtain ⟨H, hfin, helem, hhit, hcard⟩ := (sharpHittingSet_support_iff A).mp h
  exact ⟨hfin, H, helem, hhit, hcard.le⟩

/-! ### Transposition, for counting -/

private theorem transpose_elem_iff :
    ∀ b : transposeInterp.Map A,
      SSElem b ↔ SSFam (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_elem w

private theorem transpose_fam_iff :
    ∀ b : transposeInterp.Map A,
      SSFam b ↔ SSElem (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_fam w

private theorem transpose_mem_iff :
    ∀ b b' : transposeInterp.Map A,
      SSMem b b' ↔ SSMem (transposeInterp.mapEquivSelf A b')
        (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact transpose_mem w w'

private theorem transpose_marked_iff :
    ∀ b : transposeInterp.Map A,
      SSMarked b ↔ SSMarked (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_marked w

/-- The hitting sets of the transposed system are the covers. -/
theorem sharpHittingSet_transpose_map :
    SharpHittingSet (transposeInterp.Map A) = SharpSetCover A :=
  Nat.card_congr (coverFamOfSizeEquiv (transposeInterp.mapEquivSelf A)
    (transpose_fam_iff A) (transpose_elem_iff A) (fun b b' => transpose_mem_iff A b' b)
    (transpose_marked_iff A))

/-- The covers of the transposed system are the hitting sets. -/
theorem sharpSetCover_transpose_map :
    SharpSetCover (transposeInterp.Map A) = SharpHittingSet A :=
  Nat.card_congr (coverFamOfSizeEquiv (transposeInterp.mapEquivSelf A)
    (transpose_elem_iff A) (transpose_fam_iff A) (fun b b' => transpose_mem_iff A b b')
    (transpose_marked_iff A))

end Apply

/-! ### Membership -/

/-- The block of the counting definition of Set Cover: the cover itself. -/
fo_block coverSelBlock over Language.setSystem ss into coverSelLang with cv where
  /-- The cover. -/
  sel : 1

instance : Subsingleton coverSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Set Cover: the guessed subfamily consists of sets
of the family and covers every ground element. -/
noncomputable def coverSelKernel : coverSelLang.Sentence :=
  fo% (∀ s, cvSelSym(s) → cvFamSym(s)) ∧
    ∀ x, cvElemSym(x) → ∃ s, cvSelSym(s) ∧ cvMemSym(x, s)

/-- Realization of the order-free kernel of #Set Cover. -/
theorem realize_coverSelKernel {A : Type} [Language.setSystem.Structure A]
    (ρ : coverSelBlock.Assignment A) :
    (@Sentence.Realize coverSelLang A
        (@sumStructure _ _ A _ (coverSelBlock.structure ρ)) coverSelKernel) ↔
      (∀ s : A, (ρ .sel fun _ => s) → SSFam s) ∧
        ∀ x : A, SSElem x → ∃ s : A, (ρ .sel fun _ => s) ∧ SSMem x s := by
  let := coverSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := coverSelLang) (M := A) cvSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [coverSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  refine and_congr ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩
    ⟨fun h x hx => ?_, fun h i hi => ?_⟩
  · obtain ⟨s, hs⟩ := h (fun _ => x) hx
    exact ⟨s 0, hs⟩
  · obtain ⟨s, hs⟩ := h (i 0) hi
    exact ⟨fun _ => s, hs⟩

/-- **#Set Cover is in `#P`.** -/
theorem sharpSetCover_mem_sharpP : SharpSetCover ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpSetCover coverSelBlock ssMarked .sel rfl coverSelKernel
    (fun A _ G => (∀ s : A, G s → SSFam s) ∧ ∀ x : A, SSElem x → ∃ s : A, G s ∧ SSMem x s)
    (fun _ _ ρ => realize_coverSelKernel ρ)
    fun _ _ hfin => Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => (and_iff_right hfin).trans and_assoc.symm)

/-! ### Hardness of #Set Cover -/

section Hardness

variable {A : Type} [Language.markedGraph.Structure A]

/-- The vertex-sets of a vertex cover of the threshold size are a cover of the
threshold size. -/
theorem setCoverOfSize_vertexFamily {C : A → Prop} (h : CoverOfSize A C) :
    SetCoverOfSize (edgeIncidenceInterp.Map A) (vertexFamily C) := by
  obtain ⟨hfin, hcov, hcard⟩ := h
  have := hfin
  refine ⟨edgeIncidenceInterp.map_finite A, ?_, ?_,
    (ncard_vertexFamily C).trans (hcard.trans (ncard_marked A).symm)⟩
  · rintro s ⟨v, -, rfl⟩
    exact (edgeIncidence_fam ![v, v]).mpr (by simp)
  · rintro ⟨⟨⟩, w⟩ hx
    obtain ⟨hadj, hne⟩ := (edgeIncidence_elem w).mp hx
    rcases hcov (w 0) (w 1) hne hadj with h0 | h1
    · exact ⟨diagPt (w 0), ⟨w 0, h0, rfl⟩,
        (edgeIncidence_mem w ![w 0, w 0]).mpr ⟨by simp, Or.inl (by simp)⟩⟩
    · exact ⟨diagPt (w 1), ⟨w 1, h1, rfl⟩,
        (edgeIncidence_mem w ![w 1, w 1]).mpr ⟨by simp, Or.inr (by simp)⟩⟩

/-- A cover of the interpreted system consists of vertex-sets. -/
theorem setCover_diag {G : edgeIncidenceInterp.Map A → Prop}
    (h : SetCoverOfSize (edgeIncidenceInterp.Map A) G) :
    ∀ p : edgeIncidenceInterp.Map A, G p → ∃ v, p = diagPt v := by
  rintro ⟨⟨⟩, w⟩ hw
  exact ⟨w 0, (eq_diagPt_iff () w (w 0)).mpr
    ⟨rfl, ((edgeIncidence_fam w).mp (h.2.1 _ hw)).symm⟩⟩

/-- The vertices of a cover of the threshold size are a vertex cover of the
threshold size. -/
theorem coverOfSize_of_setCover {G : edgeIncidenceInterp.Map A → Prop}
    (h : SetCoverOfSize (edgeIncidenceInterp.Map A) G) :
    CoverOfSize A fun v => G (diagPt v) := by
  have hdiag := setCover_diag h
  obtain ⟨hfin, -, hcov, hcard⟩ := h
  refine ⟨Finite.of_injective _ (diagPt_injective (A := A)), fun x y hxy hadj => ?_,
    (ncard_diag_eq _ G hdiag fun _ => Iff.rfl).symm.trans (hcard.trans (ncard_marked A))⟩
  obtain ⟨s, hsG, hsMem⟩ := hcov ((), ![x, y])
    ((edgeIncidence_elem ![x, y]).mpr ⟨hadj, hxy⟩)
  obtain ⟨v, rfl⟩ := hdiag s hsG
  obtain ⟨-, hend⟩ := (edgeIncidence_mem ![x, y] ![v, v]).mp hsMem
  rcases hend with h | h
  · exact Or.inl (by simpa [show v = x by simpa using h] using hsG)
  · exact Or.inr (by simpa [show v = y by simpa using h] using hsG)

variable (A) in
/-- **The covers of the threshold size of the edge-incidence system are the
vertex covers of the threshold size**, bijectively. -/
def coverEquiv :
    {C : A → Prop // CoverOfSize A C} ≃
      {G : edgeIncidenceInterp.Map A → Prop //
        SetCoverOfSize (edgeIncidenceInterp.Map A) G} where
  toFun C := ⟨vertexFamily C.1, setCoverOfSize_vertexFamily C.2⟩
  invFun G := ⟨fun v => G.1 (diagPt v), coverOfSize_of_setCover G.2⟩
  left_inv C := Subtype.ext (funext fun v => propext
    ⟨fun ⟨_, hv', heq⟩ => diagPt_injective heq ▸ hv', fun hv => ⟨v, hv, rfl⟩⟩)
  right_inv G := Subtype.ext (funext fun p => propext
    ⟨by
      rintro ⟨v, hv, rfl⟩
      exact hv,
    fun hp => by
      obtain ⟨v, rfl⟩ := setCover_diag G.2 p hp
      exact ⟨v, hp, rfl⟩⟩)

end Hardness

/-! ### The reductions and the completeness theorems -/

/-- **#Vertex Cover reduces parsimoniously to #Set Cover**, by the
edge-incidence interpretation. -/
noncomputable def sharpVertexCover_parsimonious_sharpSetCover :
    SharpVertexCover ≤ᵖ SharpSetCover where
  Tag := Unit
  dim := 2
  toInterpretation := edgeIncidenceInterp
  correct A _ _ _ := Nat.card_congr (coverEquiv A)

/-- **#Set Cover reduces parsimoniously to #Hitting Set**, by transposition. -/
noncomputable def sharpSetCover_parsimonious_sharpHittingSet :
    SharpSetCover ≤ᵖ SharpHittingSet where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := (sharpHittingSet_transpose_map A).symm

/-- **#Hitting Set reduces parsimoniously to #Set Cover**, by transposition. -/
noncomputable def sharpHittingSet_parsimonious_sharpSetCover :
    SharpHittingSet ≤ᵖ SharpSetCover where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := (sharpSetCover_transpose_map A).symm

/-- #Set Cover is parsimoniously `#P`-hard. -/
theorem sharpSetCover_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpSetCover :=
  SharpP.parsimoniousHard_of_parsimonious sharpVertexCover_parsimonious_sharpSetCover
    sharpVertexCover_sharpP_parsimoniousHard

/-- **#Set Cover is parsimoniously `#P`-complete**, counting the covers of
exactly the threshold size. -/
theorem sharpSetCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpSetCover :=
  ⟨sharpSetCover_mem_sharpP, sharpSetCover_sharpP_parsimoniousHard⟩

/-- `SharpSetCover` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpSetCover_sharpP_complete : SharpP.Complete SharpSetCover :=
  complete_sharpP_of_parsimoniousComplete sharpSetCover_sharpP_parsimoniousComplete

/-- **#Hitting Set is in `#P`.** -/
theorem sharpHittingSet_mem_sharpP : SharpHittingSet ∈ SharpP :=
  SharpP.mem_of_parsimonious sharpHittingSet_parsimonious_sharpSetCover
    sharpSetCover_mem_sharpP

/-- #Hitting Set is parsimoniously `#P`-hard. -/
theorem sharpHittingSet_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpHittingSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpSetCover_parsimonious_sharpHittingSet
    sharpSetCover_sharpP_parsimoniousHard

/-- **#Hitting Set is parsimoniously `#P`-complete**, counting the hitting sets
of exactly the threshold size. -/
theorem sharpHittingSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpHittingSet :=
  ⟨sharpHittingSet_mem_sharpP, sharpHittingSet_sharpP_parsimoniousHard⟩

/-- `SharpHittingSet` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpHittingSet_sharpP_complete : SharpP.Complete SharpHittingSet :=
  complete_sharpP_of_parsimoniousComplete sharpHittingSet_sharpP_parsimoniousComplete

end DescriptiveComplexity
