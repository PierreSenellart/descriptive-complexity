/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions
import Lax280166Proofs.DescriptiveComplexity.Counting.Subtractive
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CliqueOfSizeOn CoverOfSize CoverOfSizeOn IndepOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (CliqueOn MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

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

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic properties -/

section Generic

variable {A B : Type}

/-- A clique at least as large as the marked set contains one of exactly that
size. -/
theorem exists_cliqueOfSizeOn_iff (Adjp : A → A → Prop) (Kp : A → Prop) :
    (∃ S, Lax280166.CountingCliques.CliqueOfSizeOn Adjp Kp S) ↔ Lax799700.CliqueFamily.CliqueOn Adjp Kp := by
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
    {S : B → Prop // Finite B ∧ Lax280166.CountingCliques.CliqueOfSizeOn AdjB KB S} ≃
      {S : A → Prop // Finite A ∧ Lax280166.CountingCliques.CliqueOfSizeOn AdjA KA S} where
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
    {C : A → Prop // Finite A ∧ Lax280166.CountingCliques.CoverOfSizeOn Adjp Kp C} ≃
      {S : A → Prop //
        Finite A ∧ Lax280166.CountingCliques.CliqueOfSizeOn (fun x y => ¬Adjp x y) (fun x => ¬Kp x) S} where
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

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Problems

/-- **#Independent Set**: the number of independent sets with exactly as many
vertices as the marked set. -/
noncomputable def SharpIndependentSet : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax280166.CountingCliques.IndepOfSize A inst S}
  iso_invariant := fun e => Nat.card_congr
    (cliqueOfSizeEquiv e.toEquiv (fun a a' _ => not_congr (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a a'))
      fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

/-- **#Vertex Cover**: the number of vertex covers with exactly as many
vertices as the marked set. -/
noncomputable def SharpVertexCover : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {C : A → Prop // @Lax280166.CountingCliques.CoverOfSize A inst C}
  iso_invariant := fun e =>
    (Nat.card_congr (coverComplEquiv _ _)).trans
      ((Nat.card_congr (cliqueOfSizeEquiv e.toEquiv
          (fun a a' _ => not_congr (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a a'))
          fun a => not_congr (relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a))).trans
        (Nat.card_congr (coverComplEquiv _ _)).symm)

section Apply

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

theorem sharpIndependentSet_apply :
    SharpIndependentSet A = Nat.card {S : A → Prop // Lax280166.CountingCliques.IndepOfSize A S} :=
  rfl

theorem sharpVertexCover_apply :
    SharpVertexCover A = Nat.card {C : A → Prop // Lax280166.CountingCliques.CoverOfSize A C} :=
  rfl

/-- **The support of #Independent Set is Independent Set.** -/
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
as the marked set extends to one of exactly that size. -/
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
      Lax799700.CliqueFamily.MGAdj b b' ↔
        (complEdgeInterp.mapEquivSelf A b ≠ complEdgeInterp.mapEquivSelf A b' ∧
          ¬Lax799700.CliqueFamily.MGAdj (complEdgeInterp.mapEquivSelf A b) (complEdgeInterp.mapEquivSelf A b')) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complEdge_adj w w'

private theorem complEdge_marked_iff :
    ∀ b : complEdgeInterp.Map A,
      Lax799700.CliqueFamily.MGMarked b ↔ Lax799700.CliqueFamily.MGMarked (complEdgeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact complEdge_marked w

private theorem complMark_adj_iff :
    ∀ b b' : complMarkInterp.Map A,
      Lax799700.CliqueFamily.MGAdj b b' ↔
        Lax799700.CliqueFamily.MGAdj (complMarkInterp.mapEquivSelf A b) (complMarkInterp.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact complMark_adj w w'

private theorem complMark_marked_iff :
    ∀ b : complMarkInterp.Map A,
      Lax799700.CliqueFamily.MGMarked b ↔ ¬Lax799700.CliqueFamily.MGMarked (complMarkInterp.mapEquivSelf A b) := by
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
independent sets of exactly the threshold size. -/
theorem sharpIndependentSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpIndependentSet :=
  ⟨sharpIndependentSet_mem_sharpP, sharpIndependentSet_sharpP_parsimoniousHard⟩

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
covers of exactly the threshold size. -/
theorem sharpVertexCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpVertexCover :=
  ⟨sharpVertexCover_mem_sharpP, sharpVertexCover_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


