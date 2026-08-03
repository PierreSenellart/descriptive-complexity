/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DagIso.ToGraphIso
import DescriptiveComplexity.Problems.DagIso.FromGraphIso

/-!
# DAG Isomorphism is GI-complete

Putting the two halves together: DAG ISOMORPHISM
(`DescriptiveComplexity.DagIso`) is complete for the degree of Graph
Isomorphism (`DescriptiveComplexity.GI`), the first entry of that degree
besides Graph Isomorphism itself.

* **Membership** (`DescriptiveComplexity.dagIso_mem_GI`,
  `DescriptiveComplexity.Problems.DagIso.ToGraphIso`): forget the topological
  orders, after checking first-order that they are ones – the check the
  instances carry their acyclicity witness for.
* **Hardness** (`DescriptiveComplexity.dagIso_GI_hard`,
  `DescriptiveComplexity.Problems.DagIso.FromGraphIso`): subdivide every arc
  twice, so that the direction of an arc survives as the difference between
  the two subdivision levels.

Both reductions are order-free, as reductions between isomorphism problems have
to be: an interpretation commutes with isomorphisms, which is what makes the
forward half of each correctness proof available at all, and an order-invariant
reduction would only fix the *answer*, not the constructed structure up to
isomorphism.

Since the whole degree sits inside NP (`DescriptiveComplexity.GI_subset_NP`),
membership in NP comes for free
(`DescriptiveComplexity.dagIso_mem_NP`); no hardness for a *class* is claimed,
and none is expected – that is what makes the degree worth having.
-/

namespace DescriptiveComplexity

/-- DAG Isomorphism is hard for the GI degree: Graph Isomorphism, which is,
reduces to it. -/
theorem dagIso_GI_hard : GI.Hard DagIso :=
  GI.hard_of_foReduction graphIso_fo_reduction_dagIso graphIso_GI_complete.hard

/-- **DAG Isomorphism is GI-complete**: it reduces to Graph Isomorphism by
forgetting the carried topological orders, and Graph Isomorphism reduces to it
by subdividing every arc twice. -/
theorem dagIso_GI_complete : GI.Complete DagIso :=
  ⟨dagIso_mem_GI, dagIso_GI_hard⟩

/-- DAG Isomorphism is in NP, since the whole GI degree is. -/
theorem dagIso_mem_NP : DagIso ∈ NP :=
  GI_subset_NP dagIso_mem_GI

end DescriptiveComplexity
