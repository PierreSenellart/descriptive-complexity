/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Defs

/-!
# Reductions between Clique, Independent Set and Vertex Cover

The classical reductions inside the clique family, as quantifier-free
first-order reductions on marked graphs (all of tag `Unit` and dimension 1):

* `DescriptiveComplexity.indSet_fo_reduction_clique` and
  `DescriptiveComplexity.clique_fo_reduction_indSet`: complementing the edges (off the
  diagonal) exchanges cliques and independent sets, keeping the marked set;
* `DescriptiveComplexity.vertexCover_fo_reduction_indSet` and
  `DescriptiveComplexity.indSet_fo_reduction_vertexCover`: complementing the *marked
  set* exchanges vertex covers and independent sets, keeping the edges – a
  set is a vertex cover iff its complement is independent, and (on a finite
  universe) it is at most as large as the marked set iff its complement is at
  least as large as the complement of the marked set;
* composites `DescriptiveComplexity.vertexCover_fo_reduction_clique` and
  `DescriptiveComplexity.clique_fo_reduction_vertexCover`.

The counting step of the vertex-cover reductions
(`DescriptiveComplexity.coverOn_iff_indepOn_not`) is the only place where finiteness is
used; it enters through the finiteness conjunct of the problems themselves.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Complementation lemmas for the generic properties -/

section Complement

variable {A : Type}

/-- A clique is an independent set of the complement graph (loops removed). -/
theorem cliqueOn_iff_indepOn_compl (Adjp : A → A → Prop) (Kp : A → Prop) :
    CliqueOn Adjp Kp ↔ IndepOn (fun x y => x ≠ y ∧ ¬Adjp x y) Kp := by
  rw [IndepOn]
  refine cliqueOn_congr (fun x y hxy => ?_) fun x => Iff.rfl
  constructor
  · exact fun h ⟨_, hn⟩ => hn h
  · intro h
    by_contra hn
    exact h ⟨hxy, hn⟩

/-- An independent set is a clique of the complement graph (loops removed). -/
theorem indepOn_iff_cliqueOn_compl (Adjp : A → A → Prop) (Kp : A → Prop) :
    IndepOn Adjp Kp ↔ CliqueOn (fun x y => x ≠ y ∧ ¬Adjp x y) Kp := by
  rw [IndepOn]
  exact cliqueOn_congr (fun x y hxy => (iff_of_eq (by simp [hxy])).symm) fun x => Iff.rfl

/-- On a finite universe, a vertex cover at most as large as the marked set
exists iff an independent set at least as large as the *complement* of the
marked set does: complementation exchanges the two. -/
theorem coverOn_iff_indepOn_not [Finite A] (Adjp : A → A → Prop) (Kp : A → Prop) :
    CoverOn Adjp Kp ↔ IndepOn Adjp fun x => ¬Kp x := by
  classical
  have := Fintype.ofFinite A
  constructor
  · rintro ⟨C, hcov, ⟨e⟩⟩
    refine ⟨fun x => ¬C x, fun x y hx hy hxy hadj => (hcov x y hxy hadj).elim hx hy, ?_⟩
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    exact Nat.sub_le_sub_left (Fintype.card_le_of_embedding e) _
  · rintro ⟨S, hind, ⟨e⟩⟩
    refine ⟨fun x => ¬S x, fun x y hxy hadj => ?_, ?_⟩
    · rcases Classical.em (S x) with hx | hx
      · rcases Classical.em (S y) with hy | hy
        · exact absurd hadj (hind x y hx hy hxy)
        · exact Or.inr hy
      · exact Or.inl hx
    · refine Function.Embedding.nonempty_of_card_le ?_
      have h1 := Fintype.card_le_of_embedding e
      rw [Fintype.card_subtype_compl] at h1 ⊢
      omega

/-- On a finite universe, an independent set at least as large as the marked
set exists iff a vertex cover at most as large as the *complement* of the
marked set does. -/
theorem indepOn_iff_coverOn_not [Finite A] (Adjp : A → A → Prop) (Kp : A → Prop) :
    IndepOn Adjp Kp ↔ CoverOn Adjp fun x => ¬Kp x := by
  rw [coverOn_iff_indepOn_not]
  exact indepOn_congr (fun x y hxy => Iff.rfl) fun x => (not_not).symm

end Complement

/-! ### The two interpretations -/

/-- The edge-complementing interpretation: adjacency becomes off-diagonal
non-adjacency, marks are kept. -/
def complEdgeInterp :
    FOInterpretation Language.markedGraph Language.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ =>
        ∼(Term.equal (Term.var (0, 0)) (Term.var (1, 0))) ⊓
          ∼(mgAdj.formula₂ (Term.var (0, 0)) (Term.var (1, 0)))
    | _, .marked => fun _ => mgMarked.formula₁ (Term.var (0, 0))

/-- The mark-complementing interpretation: adjacency is kept, marks are
complemented. -/
def complMarkInterp :
    FOInterpretation Language.markedGraph Language.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ => mgAdj.formula₂ (Term.var (0, 0)) (Term.var (1, 0))
    | _, .marked => fun _ => ∼(mgMarked.formula₁ (Term.var (0, 0)))

/-- Both interpretations are quantifier-free. -/
theorem complEdgeInterp_isQuantifierFree : complEdgeInterp.IsQuantifierFree := by
  intro n R t
  cases R with
  | adj =>
    exact ((IsAtomic.equal _ _).isQF.imp isQF_bot).inf ((IsAtomic.rel _ _).isQF.imp isQF_bot)
  | marked => exact (IsAtomic.rel _ _).isQF

@[inherit_doc complEdgeInterp_isQuantifierFree]
theorem complMarkInterp_isQuantifierFree : complMarkInterp.IsQuantifierFree := by
  intro n R t
  cases R with
  | adj => exact (IsAtomic.rel _ _).isQF
  | marked => exact (IsAtomic.rel _ _).isQF.imp isQF_bot

/-! ### Characterizations of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.markedGraph.Structure A]

@[simp]
theorem complEdge_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) mgAdj ![((), w₁), ((), w₂)] ↔
      w₁ 0 ≠ w₂ 0 ∧ ¬RelMap mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₂]

@[simp]
theorem complEdge_marked (w : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) mgMarked ![((), w)] ↔ RelMap mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₁]

@[simp]
theorem complMark_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := complMarkInterp.Map A) mgAdj ![((), w₁), ((), w₂)] ↔
      RelMap mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complMarkInterp, Formula.realize_rel₂]

@[simp]
theorem complMark_marked (w : Fin 1 → A) :
    RelMap (M := complMarkInterp.Map A) mgMarked ![((), w)] ↔ ¬RelMap mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complMarkInterp, Formula.realize_rel₁]

end Characterizations

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.markedGraph.Structure A]

private theorem complEdge_hadj :
    ∀ b b' : complEdgeInterp.Map A,
      MGAdj b b' ↔
        (complEdgeInterp.mapEquivSelf A b ≠ complEdgeInterp.mapEquivSelf A b' ∧
          ¬MGAdj (complEdgeInterp.mapEquivSelf A b) (complEdgeInterp.mapEquivSelf A b')) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complEdge_adj w w'

private theorem complEdge_hK :
    ∀ b : complEdgeInterp.Map A,
      MGMarked b ↔ MGMarked (complEdgeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complEdge_marked w

private theorem complMark_hadj :
    ∀ b b' : complMarkInterp.Map A,
      MGAdj b b' ↔
        MGAdj (complMarkInterp.mapEquivSelf A b) (complMarkInterp.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complMark_adj w w'

private theorem complMark_hK :
    ∀ b : complMarkInterp.Map A,
      MGMarked b ↔ ¬MGMarked (complMarkInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complMark_marked w

/-- Correctness of the edge complementation, independent-set-to-clique
direction. -/
theorem hasLargeIndependentSet_iff_map :
    HasLargeIndependentSet A ↔ HasLargeClique (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [indepOn_iff_cliqueOn_compl]
  exact (CliqueOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_hadj A)
    (complEdge_hK A)).symm

/-- Correctness of the edge complementation, clique-to-independent-set
direction. -/
theorem hasLargeClique_iff_map :
    HasLargeClique A ↔ HasLargeIndependentSet (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [cliqueOn_iff_indepOn_compl]
  exact (IndepOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_hadj A)
    (complEdge_hK A)).symm

/-- Correctness of the mark complementation, vertex-cover-to-independent-set
direction. -/
theorem hasSmallVertexCover_iff_map :
    HasSmallVertexCover A ↔ HasLargeIndependentSet (complMarkInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hcov⟩
    haveI := hfin
    refine ⟨(complMarkInterp.mapEquivSelf A).finite_iff.mpr hfin, ?_⟩
    rw [coverOn_iff_indepOn_not] at hcov
    exact (IndepOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mpr hcov
  · rintro ⟨hfin, hind⟩
    have hA : Finite A := (complMarkInterp.mapEquivSelf A).finite_iff.mp hfin
    haveI := hA
    refine ⟨hA, ?_⟩
    rw [coverOn_iff_indepOn_not]
    exact (IndepOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mp hind

/-- Correctness of the mark complementation, independent-set-to-vertex-cover
direction. -/
theorem hasLargeIndependentSet_iff_cover_map :
    HasLargeIndependentSet A ↔ HasSmallVertexCover (complMarkInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hind⟩
    haveI := hfin
    refine ⟨(complMarkInterp.mapEquivSelf A).finite_iff.mpr hfin, ?_⟩
    rw [indepOn_iff_coverOn_not] at hind
    exact (CoverOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mpr hind
  · rintro ⟨hfin, hcov⟩
    have hA : Finite A := (complMarkInterp.mapEquivSelf A).finite_iff.mp hfin
    haveI := hA
    refine ⟨hA, ?_⟩
    rw [indepOn_iff_coverOn_not]
    exact (CoverOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mp hcov

end Correctness

/-! ### The reductions -/

/-- **Independent Set FO-reduces to Clique**, by complementing the edges. -/
def indSet_fo_reduction_clique : IndependentSet ≤ᶠᵒ Clique where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ := hasLargeIndependentSet_iff_map A

/-- **Clique FO-reduces to Independent Set**, by complementing the edges. -/
def clique_fo_reduction_indSet : Clique ≤ᶠᵒ IndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ := hasLargeClique_iff_map A

/-- **Vertex Cover FO-reduces to Independent Set**, by complementing the
marked set. -/
def vertexCover_fo_reduction_indSet : VertexCover ≤ᶠᵒ IndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ := hasSmallVertexCover_iff_map A

/-- **Independent Set FO-reduces to Vertex Cover**, by complementing the
marked set. -/
def indSet_fo_reduction_vertexCover : IndependentSet ≤ᶠᵒ VertexCover where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ := hasLargeIndependentSet_iff_cover_map A

end DescriptiveComplexity
