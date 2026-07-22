/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Defs
import DescriptiveComplexity.Problems.CliqueFamily.Reductions
import DescriptiveComplexity.Problems.CliqueFamily.Membership
import DescriptiveComplexity.Problems.CliqueFamily.FromSat
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Composition

/-!
# The clique family is NP-complete

Umbrella file for the problems Clique, Independent Set and Vertex Cover on
marked graphs (`DescriptiveComplexity.Clique`, `DescriptiveComplexity.IndependentSet`,
`DescriptiveComplexity.VertexCover`, defined in
`DescriptiveComplexity.Problems.CliqueFamily.Defs`), collecting the quantifier-free
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions` and their
composites – all three problems are FO-interreducible – and deriving the
NP-completeness of all three from

* `DescriptiveComplexity.clique_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.CliqueFamily.Membership`): membership of Clique,
  by guessing the clique and an injection of the marked set into it;
* `DescriptiveComplexity.sat_ordered_fo_reduction_clique : SAT ≤ᶠᵒ[≤] Clique`
  (`DescriptiveComplexity.Problems.CliqueFamily.FromSat`): hardness of Clique, from
  the Cook–Levin theorem (`DescriptiveComplexity.SAT_NP_complete`;
  [Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]);

with no machine model anywhere. Membership travels backward and hardness
forward along the quantifier-free inter-reductions, yielding
`DescriptiveComplexity.indSet_NP_complete` and
`DescriptiveComplexity.vertexCover_NP_complete`. As with any complexity-theoretic
statement, these results are about finite marked graphs only
(`ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- **Vertex Cover FO-reduces to Clique**, by composing the mark and edge
complementations. -/
noncomputable def vertexCover_fo_reduction_clique : VertexCover ≤ᶠᵒ Clique :=
  vertexCover_fo_reduction_indSet.trans indSet_fo_reduction_clique

/-- **Clique FO-reduces to Vertex Cover**, by composing the edge and mark
complementations. -/
noncomputable def clique_fo_reduction_vertexCover : Clique ≤ᶠᵒ VertexCover :=
  clique_fo_reduction_indSet.trans indSet_fo_reduction_vertexCover

/-! ### NP-completeness -/

/-- Clique is in NP: it is `Σ₁`-definable. -/
theorem clique_mem_NP : Clique ∈ NP :=
  clique_sigmaSODefinable

/-- Clique is NP-hard: SAT, which is NP-hard, reduces to it by an ordered FO
reduction. -/
theorem clique_NP_hard : NP.Hard Clique :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_clique sat_NP_hard

/-- **Clique is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem clique_NP_complete : NP.Complete Clique :=
  ⟨clique_mem_NP, clique_NP_hard⟩

/-- Independent Set is in NP: it FO-reduces to Clique, which is in NP. -/
theorem indSet_mem_NP : IndependentSet ∈ NP :=
  NP.mem_of_foReduction indSet_fo_reduction_clique clique_mem_NP

/-- Independent Set is NP-hard: Clique, which is NP-hard, reduces to it. -/
theorem indSet_NP_hard : NP.Hard IndependentSet :=
  NP.hard_of_foReduction clique_fo_reduction_indSet clique_NP_hard

/-- **Independent Set is NP-complete**. -/
theorem indSet_NP_complete : NP.Complete IndependentSet :=
  ⟨indSet_mem_NP, indSet_NP_hard⟩

/-- Vertex Cover is in NP: it FO-reduces to Independent Set, which is in
NP. -/
theorem vertexCover_mem_NP : VertexCover ∈ NP :=
  NP.mem_of_foReduction vertexCover_fo_reduction_indSet indSet_mem_NP

/-- Vertex Cover is NP-hard: Independent Set, which is NP-hard, reduces to
it. -/
theorem vertexCover_NP_hard : NP.Hard VertexCover :=
  NP.hard_of_foReduction indSet_fo_reduction_vertexCover indSet_NP_hard

/-- **Vertex Cover is NP-complete**. -/
theorem vertexCover_NP_complete : NP.Complete VertexCover :=
  ⟨vertexCover_mem_NP, vertexCover_NP_hard⟩

end DescriptiveComplexity
