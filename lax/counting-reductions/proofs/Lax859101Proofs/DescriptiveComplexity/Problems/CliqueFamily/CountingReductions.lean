/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
import Lax859101Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions
import Lax859101Proofs.DescriptiveComplexity.Counting.Subtractive
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (CliqueOn MGAdj MGMarked)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CliqueOfSizeOn CoverOfSize CoverOfSizeOn IndepOfSize)
end Lax859101Proofs.DescriptiveComplexity

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

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic properties -/

section Generic

variable {A B : Type}

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

section Apply

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

theorem sharpIndependentSet_apply :
    SharpIndependentSet A = Nat.card {S : A → Prop // Lax280166.CountingCliques.IndepOfSize A S} :=
  rfl

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

/-- The independent sets of the complement graph are the cliques. -/
theorem sharpIndependentSet_complEdge_map :
    SharpIndependentSet (complEdgeInterp.Map A) = SharpClique A :=
  Nat.card_congr (cliqueOfSizeEquiv (complEdgeInterp.mapEquivSelf A)
    (fun b b' hne => (not_congr ((complEdge_adj_iff A b b').trans
      (and_iff_right ((complEdgeInterp.mapEquivSelf A).injective.ne hne)))).trans not_not)
    (complEdge_marked_iff A))

end Apply

/-! ### The reductions and the completeness theorems -/

/-- **#Clique reduces parsimoniously to #Independent Set**, by complementing
the edges. -/
noncomputable def sharpClique_parsimonious_sharpIndependentSet :
    SharpClique ≤ᵖ SharpIndependentSet where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ _ := (sharpIndependentSet_complEdge_map A).symm

/-- #Independent Set is parsimoniously `#P`-hard. -/
theorem sharpIndependentSet_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpIndependentSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpClique_parsimonious_sharpIndependentSet
    sharpClique_sharpP_parsimoniousHard

end Lax859101Proofs.DescriptiveComplexity


