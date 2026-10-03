/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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
# Reductions between Clique, Independent Set and Vertex Cover

The classical reductions inside the clique family, as quantifier-free
first-order reductions on marked graphs (all of tag `Unit` and dimension 1):

* `Lax799700Proofs.DescriptiveComplexity.indSet_fo_reduction_clique` and
  `Lax799700Proofs.DescriptiveComplexity.clique_fo_reduction_indSet`: complementing the edges (off the
  diagonal) exchanges cliques and independent sets, keeping the marked set;
* `Lax799700Proofs.DescriptiveComplexity.vertexCover_fo_reduction_indSet` and
  `Lax799700Proofs.DescriptiveComplexity.indSet_fo_reduction_vertexCover`: complementing the *marked
  set* exchanges vertex covers and independent sets, keeping the edges – a
  set is a vertex cover iff its complement is independent, and (on a finite
  universe) it is at most as large as the marked set iff its complement is at
  least as large as the complement of the marked set;
* composites `Lax799700Proofs.DescriptiveComplexity.vertexCover_fo_reduction_clique` and
  `Lax799700Proofs.DescriptiveComplexity.clique_fo_reduction_vertexCover`.

The counting step of the vertex-cover reductions
(`Lax799700Proofs.DescriptiveComplexity.coverOn_iff_indepOn_not`) is the only place where finiteness is
used; it enters through the finiteness conjunct of the problems themselves. That
step is pure unary-representation arithmetic – complementing a marked set
subtracts its decoded number from the size of the universe, hence reverses
comparisons – and is discharged by
`Lax799700Proofs.DescriptiveComplexity.ncard_compl_le_ncard_compl_iff` and
`Lax799700Proofs.DescriptiveComplexity.ncard_compl_le_iff` of `Lax799700Proofs.DescriptiveComplexity.Numbers.Unary`.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Complementation lemmas for the generic properties -/

section Complement

variable {A : Type}

/-- A clique is an independent set of the complement graph (loops removed). -/
theorem cliqueOn_iff_indepOn_compl (Adjp : A → A → Prop) (Kp : A → Prop) :
    Lax799700.CliqueFamily.CliqueOn Adjp Kp ↔ Lax799700.CliqueFamily.IndepOn (fun x y => x ≠ y ∧ ¬Adjp x y) Kp := by
  rw [Lax799700.CliqueFamily.IndepOn]
  refine cliqueOn_congr (fun x y hxy => ?_) fun x => Iff.rfl
  constructor
  · exact fun h ⟨_, hn⟩ => hn h
  · intro h
    by_contra hn
    exact h ⟨hxy, hn⟩

/-- An independent set is a clique of the complement graph (loops removed). -/
theorem indepOn_iff_cliqueOn_compl (Adjp : A → A → Prop) (Kp : A → Prop) :
    Lax799700.CliqueFamily.IndepOn Adjp Kp ↔ Lax799700.CliqueFamily.CliqueOn (fun x y => x ≠ y ∧ ¬Adjp x y) Kp := by
  rw [Lax799700.CliqueFamily.IndepOn]
  exact cliqueOn_congr (fun x y hxy => (iff_of_eq (by simp [hxy])).symm) fun x => Iff.rfl

/-- On a finite universe, a vertex cover at most as large as the marked set
exists iff an independent set at least as large as the *complement* of the
marked set does: complementation exchanges the two. -/
theorem coverOn_iff_indepOn_not [Finite A] (Adjp : A → A → Prop) (Kp : A → Prop) :
    Lax799700.CliqueFamily.CoverOn Adjp Kp ↔ Lax799700.CliqueFamily.IndepOn Adjp fun x => ¬Kp x := by
  constructor
  · rintro ⟨C, hcov, hcard⟩
    exact ⟨fun x => ¬C x, fun x y hx hy hxy hadj => (hcov x y hxy hadj).elim hx hy,
      (ncard_compl_le_ncard_compl_iff {x | Kp x} {x | C x}).mpr hcard⟩
  · rintro ⟨S, hind, hcard⟩
    refine ⟨fun x => ¬S x, fun x y hxy hadj => ?_,
      (ncard_compl_le_iff {x | S x} {x | Kp x}).mpr hcard⟩
    rcases Classical.em (S x) with hx | hx
    · rcases Classical.em (S y) with hy | hy
      · exact absurd hadj (hind x y hx hy hxy)
      · exact Or.inr hy
    · exact Or.inl hx

/-- On a finite universe, an independent set at least as large as the marked
set exists iff a vertex cover at most as large as the *complement* of the
marked set does. -/
theorem indepOn_iff_coverOn_not [Finite A] (Adjp : A → A → Prop) (Kp : A → Prop) :
    Lax799700.CliqueFamily.IndepOn Adjp Kp ↔ Lax799700.CliqueFamily.CoverOn Adjp fun x => ¬Kp x := by
  rw [coverOn_iff_indepOn_not]
  exact indepOn_congr (fun x y hxy => Iff.rfl) fun x => (not_not).symm

end Complement

/-! ### The two interpretations -/

/-- The edge-complementing interpretation: adjacency becomes off-diagonal
non-adjacency, marks are kept. -/
def complEdgeInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.CliqueFamily.markedGraph Lax799700.CliqueFamily.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ => FirstOrder.Language.BoundedFormula.not
                                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))) ⊓
                              FirstOrder.Language.BoundedFormula.not
                                (FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0))
                                  (FirstOrder.Language.Term.var (1, 0)))
    | _, .marked => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0))

/-- The mark-complementing interpretation: adjacency is kept, marks are
complemented. -/
def complMarkInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.CliqueFamily.markedGraph Lax799700.CliqueFamily.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .marked => fun _ => FirstOrder.Language.BoundedFormula.not
                                 (FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0)))

/-! ### Characterizations of the interpreted relations -/

section Characterizations

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

@[simp]
theorem complEdge_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) Lax799700.CliqueFamily.mgAdj ![((), w₁), ((), w₂)] ↔
      w₁ 0 ≠ w₂ 0 ∧ ¬RelMap Lax799700.CliqueFamily.mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₂]

@[simp]
theorem complEdge_marked (w : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) Lax799700.CliqueFamily.mgMarked ![((), w)] ↔ RelMap Lax799700.CliqueFamily.mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₁]

@[simp]
theorem complMark_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := complMarkInterp.Map A) Lax799700.CliqueFamily.mgAdj ![((), w₁), ((), w₂)] ↔
      RelMap Lax799700.CliqueFamily.mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complMarkInterp, Formula.realize_rel₂]

@[simp]
theorem complMark_marked (w : Fin 1 → A) :
    RelMap (M := complMarkInterp.Map A) Lax799700.CliqueFamily.mgMarked ![((), w)] ↔ ¬RelMap Lax799700.CliqueFamily.mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complMarkInterp, Formula.realize_rel₁]

end Characterizations

/-! ### Correctness -/

section Correctness

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

private theorem complEdge_hadj :
    ∀ b b' : complEdgeInterp.Map A,
      Lax799700.CliqueFamily.MGAdj b b' ↔
        (complEdgeInterp.mapEquivSelf A b ≠ complEdgeInterp.mapEquivSelf A b' ∧
          ¬Lax799700.CliqueFamily.MGAdj (complEdgeInterp.mapEquivSelf A b) (complEdgeInterp.mapEquivSelf A b')) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complEdge_adj w w'

private theorem complEdge_hK :
    ∀ b : complEdgeInterp.Map A,
      Lax799700.CliqueFamily.MGMarked b ↔ Lax799700.CliqueFamily.MGMarked (complEdgeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complEdge_marked w

private theorem complMark_hadj :
    ∀ b b' : complMarkInterp.Map A,
      Lax799700.CliqueFamily.MGAdj b b' ↔
        Lax799700.CliqueFamily.MGAdj (complMarkInterp.mapEquivSelf A b) (complMarkInterp.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complMark_adj w w'

private theorem complMark_hK :
    ∀ b : complMarkInterp.Map A,
      Lax799700.CliqueFamily.MGMarked b ↔ ¬Lax799700.CliqueFamily.MGMarked (complMarkInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complMark_marked w

/-- Correctness of the edge complementation, independent-set-to-clique
direction. -/
theorem hasLargeIndependentSet_iff_map :
    Lax799700.CliqueFamily.HasLargeIndependentSet A ↔ Lax799700.CliqueFamily.HasLargeClique (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [indepOn_iff_cliqueOn_compl]
  exact (CliqueOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_hadj A)
    (complEdge_hK A)).symm

/-- Correctness of the edge complementation, clique-to-independent-set
direction. -/
theorem hasLargeClique_iff_map :
    Lax799700.CliqueFamily.HasLargeClique A ↔ Lax799700.CliqueFamily.HasLargeIndependentSet (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [cliqueOn_iff_indepOn_compl]
  exact (IndepOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_hadj A)
    (complEdge_hK A)).symm

/-- Correctness of the mark complementation, vertex-cover-to-independent-set
direction. -/
theorem hasSmallVertexCover_iff_map :
    Lax799700.CliqueFamily.HasSmallVertexCover A ↔ Lax799700.CliqueFamily.HasLargeIndependentSet (complMarkInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hcov⟩
    have := hfin
    refine ⟨(complMarkInterp.mapEquivSelf A).finite_iff.mpr hfin, ?_⟩
    rw [coverOn_iff_indepOn_not] at hcov
    exact (IndepOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mpr hcov
  · rintro ⟨hfin, hind⟩
    have hA : Finite A := (complMarkInterp.mapEquivSelf A).finite_iff.mp hfin
    have := hA
    refine ⟨hA, ?_⟩
    rw [coverOn_iff_indepOn_not]
    exact (IndepOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mp hind

/-- Correctness of the mark complementation, independent-set-to-vertex-cover
direction. -/
theorem hasLargeIndependentSet_iff_cover_map :
    Lax799700.CliqueFamily.HasLargeIndependentSet A ↔ Lax799700.CliqueFamily.HasSmallVertexCover (complMarkInterp.Map A) := by
  constructor
  · rintro ⟨hfin, hind⟩
    have := hfin
    refine ⟨(complMarkInterp.mapEquivSelf A).finite_iff.mpr hfin, ?_⟩
    rw [indepOn_iff_coverOn_not] at hind
    exact (CoverOn.equiv_iff (complMarkInterp.mapEquivSelf A) (complMark_hadj A)
      (complMark_hK A)).mpr hind
  · rintro ⟨hfin, hcov⟩
    have hA : Finite A := (complMarkInterp.mapEquivSelf A).finite_iff.mp hfin
    have := hA
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
  correct A _ _ _ := hasLargeIndependentSet_iff_map A

/-- **Clique FO-reduces to Independent Set**, by complementing the edges. -/
def clique_fo_reduction_indSet : Clique ≤ᶠᵒ IndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ _ := hasLargeClique_iff_map A

/-- **Vertex Cover FO-reduces to Independent Set**, by complementing the
marked set. -/
def vertexCover_fo_reduction_indSet : VertexCover ≤ᶠᵒ IndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ _ := hasSmallVertexCover_iff_map A

/-- **Independent Set FO-reduces to Vertex Cover**, by complementing the
marked set. -/
def indSet_fo_reduction_vertexCover : IndependentSet ≤ᶠᵒ VertexCover where
  Tag := Unit
  dim := 1
  toInterpretation := complMarkInterp
  correct A _ _ _ := hasLargeIndependentSet_iff_cover_map A

end Lax799700Proofs.DescriptiveComplexity


