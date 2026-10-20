/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
import DescriptiveComplexity.Problems.CliqueFamily.Reductions
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Independent Set and #Vertex Cover

The counting versions of the two other problems of the clique family, each
counting the solutions of *exactly* the threshold size:

* `DescriptiveComplexity.SharpIndependentSet`: the independent sets with as many
  vertices as the marked set;
* `DescriptiveComplexity.SharpVertexCover`: the vertex covers with as many vertices
  as the marked set.

Both are parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpIndependentSet_sharpP_parsimoniousComplete`,
`DescriptiveComplexity.sharpVertexCover_sharpP_parsimoniousComplete`), and nothing has
to be built for it: the two interpretations of
`DescriptiveComplexity.Problems.CliqueFamily.Reductions` are parsimonious as they
stand. Complementing the edges turns the cliques of a size into the
independent sets of that size, the same sets; complementing the marked set
turns the vertex covers of the threshold size into the independent sets of the
complementary size, by complementation
(`DescriptiveComplexity.coverComplEquiv`). Membership in `#P` travels backward along
the same reductions, down to the monotone bijection of #Clique.

Counting the covers of size *at most* the threshold would be a different
problem. The support of the exact count is Vertex Cover all the same, a cover
smaller than the threshold extending to one of exactly that size
(`DescriptiveComplexity.sharpVertexCover_support_iff`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic properties -/

section Generic

variable {A B : Type}

/-- The set `S` is pairwise `Adjp`-related off the diagonal and has exactly as
many elements as the `Kp`-marked set. -/
def CliqueOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧ {x | S x}.ncard = {x | Kp x}.ncard

/-- The set `C` meets every off-diagonal `Adjp`-edge and has exactly as many
elements as the `Kp`-marked set. -/
def CoverOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (C : A → Prop) : Prop :=
  (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ∧ {x | C x}.ncard = {x | Kp x}.ncard

/-- A clique at least as large as the marked set contains one of exactly that
size. -/
theorem exists_cliqueOfSizeOn_iff (Adjp : A → A → Prop) (Kp : A → Prop) :
    (∃ S, CliqueOfSizeOn Adjp Kp S) ↔ CliqueOn Adjp Kp := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    exact ⟨S, hS, hcard.ge⟩
  · rintro ⟨S, hS, hcard⟩
    obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq hcard
    exact ⟨fun x => x ∈ T, fun x y hx hy hxy => hS x y (hTS hx) (hTS hy) hxy, hT⟩

/-- The sets of the threshold size transport along an equivalence commuting
with the adjacency predicates off the diagonal and with the marks. -/
def cliqueOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', b ≠ b' → (AdjB b b' ↔ AdjA (u b) (u b'))) (hK : ∀ b, KB b ↔ KA (u b)) :
    {S : B → Prop // Finite B ∧ CliqueOfSizeOn AdjB KB S} ≃
      {S : A → Prop // Finite A ∧ CliqueOfSizeOn AdjA KA S} where
  toFun S := ⟨fun a => S.1 (u.symm a), u.finite_iff.mp S.2.1, fun x y hx hy hxy => by
      have h := (hadj (u.symm x) (u.symm y) fun h => hxy (u.symm.injective h)).mp
        (S.2.2.1 _ _ hx hy fun h => hxy (u.symm.injective h))
      simpa using h,
    (ncard_setOf_symm u S.1).symm.trans (S.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    fun b b' hb hb' hne => (hadj b b' hne).mpr (T.2.2.1 _ _ hb hb' (u.injective.ne hne)),
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv S := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

/-- On a finite universe, two sets have the same size iff their complements
do. -/
theorem ncard_not_eq_iff [Finite A] (s t : A → Prop) :
    {x | ¬s x}.ncard = {x | ¬t x}.ncard ↔ {x | s x}.ncard = {x | t x}.ncard := by
  have h₁ : {x | ¬s x}.ncard ≤ {x | ¬t x}.ncard ↔ {x | t x}.ncard ≤ {x | s x}.ncard :=
    ncard_compl_le_ncard_compl_iff {x | s x} {x | t x}
  have h₂ : {x | ¬t x}.ncard ≤ {x | ¬s x}.ncard ↔ {x | s x}.ncard ≤ {x | t x}.ncard :=
    ncard_compl_le_ncard_compl_iff {x | t x} {x | s x}
  rw [le_antisymm_iff, le_antisymm_iff, h₁, h₂, and_comm]

/-- **The covers of the threshold size are the complements of the independent
sets of the complementary size.** -/
def coverComplEquiv (Adjp : A → A → Prop) (Kp : A → Prop) :
    {C : A → Prop // Finite A ∧ CoverOfSizeOn Adjp Kp C} ≃
      {S : A → Prop //
        Finite A ∧ CliqueOfSizeOn (fun x y => ¬Adjp x y) (fun x => ¬Kp x) S} where
  toFun C := ⟨fun x => ¬C.1 x, C.2.1,
    fun x y hx hy hxy hadj => (C.2.2.1 x y hxy hadj).elim hx hy, by
      have := C.2.1
      exact (ncard_not_eq_iff C.1 Kp).mpr C.2.2.2⟩
  invFun S := ⟨fun x => ¬S.1 x, S.2.1, fun x y hxy hadj => by
      by_contra h
      exact S.2.2.1 x y (not_not.mp (not_or.mp h).1) (not_not.mp (not_or.mp h).2) hxy hadj, by
      have := S.2.1
      exact (ncard_not_eq_iff (fun x => ¬S.1 x) Kp).mp (by simpa using S.2.2.2)⟩
  left_inv C := Subtype.ext (funext fun x => propext not_not)
  right_inv S := Subtype.ext (funext fun x => propext not_not)

end Generic

/-! ### The two counting problems -/

section Problems

variable (A : Type) [Language.markedGraph.Structure A]

/-- The set `S` is an independent set with exactly as many vertices as the
marked set, in a finite marked graph. -/
def IndepOfSize (S : A → Prop) : Prop :=
  Finite A ∧ CliqueOfSizeOn (fun x y : A => ¬MGAdj x y) (fun x => MGMarked x) S

/-- The set `C` is a vertex cover with exactly as many vertices as the marked
set, in a finite marked graph. -/
def CoverOfSize (C : A → Prop) : Prop :=
  Finite A ∧ CoverOfSizeOn (fun x y : A => MGAdj x y) (fun x => MGMarked x) C

end Problems

/-- **#Independent Set**: the number of independent sets with exactly as many
vertices as the marked set. -/
noncomputable def SharpIndependentSet : CountingProblem Language.markedGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @IndepOfSize A inst S}
  iso_invariant := fun e => Nat.card_congr
    (cliqueOfSizeEquiv e.toEquiv (fun a a' _ => not_congr (relMap_equiv₂ e mgAdj a a'))
      fun a => relMap_equiv₁ e mgMarked a)

/-- **#Vertex Cover**: the number of vertex covers with exactly as many
vertices as the marked set. -/
noncomputable def SharpVertexCover : CountingProblem Language.markedGraph where
  Count := fun A inst => Nat.card {C : A → Prop // @CoverOfSize A inst C}
  iso_invariant := fun e =>
    (Nat.card_congr (coverComplEquiv _ _)).trans
      ((Nat.card_congr (cliqueOfSizeEquiv e.toEquiv
          (fun a a' _ => not_congr (relMap_equiv₂ e mgAdj a a'))
          fun a => not_congr (relMap_equiv₁ e mgMarked a))).trans
        (Nat.card_congr (coverComplEquiv _ _)).symm)

section Apply

variable (A : Type) [Language.markedGraph.Structure A]

theorem sharpIndependentSet_apply :
    SharpIndependentSet A = Nat.card {S : A → Prop // IndepOfSize A S} :=
  rfl

theorem sharpVertexCover_apply :
    SharpVertexCover A = Nat.card {C : A → Prop // CoverOfSize A C} :=
  rfl

/-- **The support of #Independent Set is Independent Set.**
Registered in the Lax archive as
[`Lax280166.IndependentSetComplete.sharpIndependentSet_support_iff`](https://laxarchive.org/lax-280166/Lax280166.IndependentSetComplete.html#s-Lax280166.IndependentSetComplete.sharpIndependentSet_support_iff). -/
theorem sharpIndependentSet_support_iff [Finite A] :
    SharpIndependentSet.support A ↔ IndependentSet A := by
  rw [CountingProblem.support_iff, sharpIndependentSet_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨S, hfin, hS⟩, -⟩
    exact ⟨hfin, (exists_cliqueOfSizeOn_iff _ _).mp ⟨S, hS⟩⟩
  · rintro ⟨hfin, h⟩
    obtain ⟨S, hS⟩ := (exists_cliqueOfSizeOn_iff _ _).mpr h
    exact ⟨⟨⟨S, hfin, hS⟩⟩, inferInstance⟩

/-- **The support of #Vertex Cover is Vertex Cover**: a cover at most as large
as the marked set extends to one of exactly that size.
Registered in the Lax archive as
[`Lax280166.VertexCoverComplete.sharpVertexCover_support_iff`](https://laxarchive.org/lax-280166/Lax280166.VertexCoverComplete.html#s-Lax280166.VertexCoverComplete.sharpVertexCover_support_iff). -/
theorem sharpVertexCover_support_iff [Finite A] :
    SharpVertexCover.support A ↔ VertexCover A := by
  rw [CountingProblem.support_iff, sharpVertexCover_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨C, hfin, hcov, hcard⟩, -⟩
    exact ⟨hfin, C, hcov, hcard.le⟩
  · rintro ⟨hfin, hcov⟩
    obtain ⟨S, hS⟩ := (exists_cliqueOfSizeOn_iff _ _).mpr
      ((coverOn_iff_indepOn_not _ _).mp hcov)
    exact ⟨⟨(coverComplEquiv _ _).symm ⟨S, hfin, hS⟩⟩, inferInstance⟩

/-! ### The interpretations, for counting -/

private theorem complEdge_adj_iff :
    ∀ b b' : complEdgeInterp.Map A,
      MGAdj b b' ↔
        (complEdgeInterp.mapEquivSelf A b ≠ complEdgeInterp.mapEquivSelf A b' ∧
          ¬MGAdj (complEdgeInterp.mapEquivSelf A b) (complEdgeInterp.mapEquivSelf A b')) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complEdge_adj w w'

private theorem complEdge_marked_iff :
    ∀ b : complEdgeInterp.Map A,
      MGMarked b ↔ MGMarked (complEdgeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complEdge_marked w

private theorem complMark_adj_iff :
    ∀ b b' : complMarkInterp.Map A,
      MGAdj b b' ↔
        MGAdj (complMarkInterp.mapEquivSelf A b) (complMarkInterp.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complMark_adj w w'

private theorem complMark_marked_iff :
    ∀ b : complMarkInterp.Map A,
      MGMarked b ↔ ¬MGMarked (complMarkInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complMark_marked w

/-- The cliques of the complement graph are the independent sets. -/
theorem sharpClique_complEdge_map :
    SharpClique (complEdgeInterp.Map A) = SharpIndependentSet A :=
  Nat.card_congr (cliqueOfSizeEquiv (complEdgeInterp.mapEquivSelf A)
    (fun b b' hne => (complEdge_adj_iff A b b').trans
      (and_iff_right ((complEdgeInterp.mapEquivSelf A).injective.ne hne)))
    (complEdge_marked_iff A))

/-- The independent sets of the complement graph are the cliques. -/
theorem sharpIndependentSet_complEdge_map :
    SharpIndependentSet (complEdgeInterp.Map A) = SharpClique A :=
  Nat.card_congr (cliqueOfSizeEquiv (complEdgeInterp.mapEquivSelf A)
    (fun b b' hne => (not_congr ((complEdge_adj_iff A b b').trans
      (and_iff_right ((complEdgeInterp.mapEquivSelf A).injective.ne hne)))).trans not_not)
    (complEdge_marked_iff A))

/-- The independent sets of the threshold size, the marked set being
complemented, are the complements of the vertex covers of the threshold
size. -/
theorem sharpIndependentSet_complMark_map :
    SharpIndependentSet (complMarkInterp.Map A) = SharpVertexCover A :=
  (Nat.card_congr (cliqueOfSizeEquiv (complMarkInterp.mapEquivSelf A)
    (fun b b' _ => not_congr (complMark_adj_iff A b b')) (complMark_marked_iff A))).trans
    (Nat.card_congr (coverComplEquiv _ _)).symm

/-- The vertex covers of the threshold size, the marked set being complemented,
are the complements of the independent sets of the threshold size. -/
theorem sharpVertexCover_complMark_map :
    SharpVertexCover (complMarkInterp.Map A) = SharpIndependentSet A :=
  (Nat.card_congr (coverComplEquiv _ _)).trans
    (Nat.card_congr (cliqueOfSizeEquiv (complMarkInterp.mapEquivSelf A)
      (fun b b' _ => not_congr (complMark_adj_iff A b b'))
      fun b => (not_congr (complMark_marked_iff A b)).trans not_not))

end Apply

/-! ### The reductions and the completeness theorems -/

/-- **#Independent Set reduces parsimoniously to #Clique**, by complementing
the edges. -/
noncomputable def sharpIndependentSet_parsimonious_sharpClique :
    SharpIndependentSet ≤ᵖ SharpClique where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ _ := (sharpClique_complEdge_map A).symm

/-- **#Clique reduces parsimoniously to #Independent Set**, by complementing
the edges. -/
noncomputable def sharpClique_parsimonious_sharpIndependentSet :
    SharpClique ≤ᵖ SharpIndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ _ := (sharpIndependentSet_complEdge_map A).symm

/-- **#Vertex Cover reduces parsimoniously to #Independent Set**, by
complementing the marked set. -/
noncomputable def sharpVertexCover_parsimonious_sharpIndependentSet :
    SharpVertexCover ≤ᵖ SharpIndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ _ := (sharpIndependentSet_complMark_map A).symm

/-- **#Independent Set reduces parsimoniously to #Vertex Cover**, by
complementing the marked set. -/
noncomputable def sharpIndependentSet_parsimonious_sharpVertexCover :
    SharpIndependentSet ≤ᵖ SharpVertexCover where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ _ := (sharpVertexCover_complMark_map A).symm

/-- **#Independent Set is in `#P`.** -/
theorem sharpIndependentSet_mem_sharpP : SharpIndependentSet ∈ SharpP :=
  SharpP.mem_of_parsimonious sharpIndependentSet_parsimonious_sharpClique
    sharpClique_mem_sharpP

/-- #Independent Set is parsimoniously `#P`-hard. -/
theorem sharpIndependentSet_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpIndependentSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpClique_parsimonious_sharpIndependentSet
    sharpClique_sharpP_parsimoniousHard

/-- **#Independent Set is parsimoniously `#P`-complete**, counting the
independent sets of exactly the threshold size.
Registered in the Lax archive as
[`Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.IndependentSetComplete.html#s-Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete). -/
theorem sharpIndependentSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpIndependentSet :=
  ⟨sharpIndependentSet_mem_sharpP, sharpIndependentSet_sharpP_parsimoniousHard⟩

/-- `SharpIndependentSet` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpIndependentSet_sharpP_complete : SharpP.Complete SharpIndependentSet :=
  complete_sharpP_of_parsimoniousComplete sharpIndependentSet_sharpP_parsimoniousComplete

/-- **#Vertex Cover is in `#P`.** -/
theorem sharpVertexCover_mem_sharpP : SharpVertexCover ∈ SharpP :=
  SharpP.mem_of_parsimonious sharpVertexCover_parsimonious_sharpIndependentSet
    sharpIndependentSet_mem_sharpP

/-- #Vertex Cover is parsimoniously `#P`-hard. -/
theorem sharpVertexCover_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpVertexCover :=
  SharpP.parsimoniousHard_of_parsimonious sharpIndependentSet_parsimonious_sharpVertexCover
    sharpIndependentSet_sharpP_parsimoniousHard

/-- **#Vertex Cover is parsimoniously `#P`-complete**, counting the vertex
covers of exactly the threshold size.
Registered in the Lax archive as
[`Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.VertexCoverComplete.html#s-Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete). -/
theorem sharpVertexCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpVertexCover :=
  ⟨sharpVertexCover_mem_sharpP, sharpVertexCover_sharpP_parsimoniousHard⟩

/-- `SharpVertexCover` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpVertexCover_sharpP_complete : SharpP.Complete SharpVertexCover :=
  complete_sharpP_of_parsimoniousComplete sharpVertexCover_sharpP_parsimoniousComplete

end DescriptiveComplexity
