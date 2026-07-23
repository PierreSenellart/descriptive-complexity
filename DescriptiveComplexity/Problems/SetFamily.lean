/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.Defs
import DescriptiveComplexity.Problems.SetFamily.Reductions
import DescriptiveComplexity.Problems.SetFamily.FromGraphs
import DescriptiveComplexity.Problems.SetFamily.Membership
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.Composition

/-!
# The set family is NP-complete

Umbrella file for the three problems on set systems – Set Cover, Hitting Set
and Set Packing (`DescriptiveComplexity.SetCover`, `DescriptiveComplexity.HittingSet`,
`DescriptiveComplexity.SetPacking`, defined in
`DescriptiveComplexity.Problems.SetFamily.Defs`) – collecting the quantifier-free
reductions of `DescriptiveComplexity.Problems.SetFamily.Reductions` (the transposition
relating Set Cover and Hitting Set) and
`DescriptiveComplexity.Problems.SetFamily.FromGraphs` (the edge-incidence reading of a
marked graph), and deriving NP-completeness from

* `DescriptiveComplexity.setCover_sigmaSODefinable` and
  `DescriptiveComplexity.setPacking_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.SetFamily.Membership`): membership, by guessing the
  subfamily and the injection witnessing the threshold;
* `DescriptiveComplexity.vertexCover_fo_reduction_setCover` and
  `DescriptiveComplexity.indSet_fo_reduction_setPacking`: hardness, from the
  NP-hardness of Vertex Cover and Independent Set
  (`DescriptiveComplexity.Problems.CliqueFamily`), and so ultimately from the
  Cook–Levin theorem, with no machine model anywhere.

Membership then travels backward and hardness forward along the transposition,
which relates Set Cover and Hitting Set in both directions, giving
`DescriptiveComplexity.hittingSet_NP_complete`. This is the set-system mirror of the
clique family: there, complementation relates the three graph problems and one
`Σ₁` definition serves them all; here the transposition relates two of them,
while Set Packing – whose threshold is a lower bound, like Clique's – carries
its own definition. As with any complexity-theoretic statement, these results
are about finite set systems only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- **Vertex Cover FO-reduces to Hitting Set**, by composing the
edge-incidence reading of a graph with the transposition of a set system. In
the composite, the vertices are the ground elements and the edges are the sets
to be hit – the textbook rendering of Vertex Cover as a hitting-set
problem. -/
noncomputable def vertexCover_fo_reduction_hittingSet : VertexCover ≤ᶠᵒ HittingSet :=
  vertexCover_fo_reduction_setCover.trans setCover_fo_reduction_hittingSet

/-! ### NP-completeness -/

/-- Set Cover is in NP: it is `Σ₁`-definable. -/
theorem setCover_mem_NP : SetCover ∈ NP :=
  setCover_sigmaSODefinable

/-- Set Cover is NP-hard: Vertex Cover, which is NP-hard, reduces to it by
the edge-incidence interpretation. -/
theorem setCover_NP_hard : NP.Hard SetCover :=
  NP.hard_of_foReduction vertexCover_fo_reduction_setCover vertexCover_NP_hard

/-- **Set Cover is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem setCover_NP_complete : NP.Complete SetCover :=
  ⟨setCover_mem_NP, setCover_NP_hard⟩

/-- Hitting Set is in NP: it FO-reduces to Set Cover, which is in NP. -/
theorem hittingSet_mem_NP : HittingSet ∈ NP :=
  NP.mem_of_foReduction hittingSet_fo_reduction_setCover setCover_mem_NP

/-- Hitting Set is NP-hard: Set Cover, which is NP-hard, reduces to it by
transposing the incidence relation. -/
theorem hittingSet_NP_hard : NP.Hard HittingSet :=
  NP.hard_of_foReduction setCover_fo_reduction_hittingSet setCover_NP_hard

/-- **Hitting Set is NP-complete**. -/
theorem hittingSet_NP_complete : NP.Complete HittingSet :=
  ⟨hittingSet_mem_NP, hittingSet_NP_hard⟩

/-- Set Packing is in NP: it is `Σ₁`-definable. -/
theorem setPacking_mem_NP : SetPacking ∈ NP :=
  setPacking_sigmaSODefinable

/-- Set Packing is NP-hard: Independent Set, which is NP-hard, reduces to it
by the edge-incidence interpretation. -/
theorem setPacking_NP_hard : NP.Hard SetPacking :=
  NP.hard_of_foReduction indSet_fo_reduction_setPacking indSet_NP_hard

/-- **Set Packing is NP-complete**. -/
theorem setPacking_NP_complete : NP.Complete SetPacking :=
  ⟨setPacking_mem_NP, setPacking_NP_hard⟩

end DescriptiveComplexity
