/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.GraphIso.Hardness
import DescriptiveComplexity.Problems.DagIso

/-!
# The GI degree, collected

The degree is defined on `DescriptiveComplexity.GraphIso`, the undirected
problem the literature names GI. Its members therefore reach it through the
digraph-to-graph gadget of
`DescriptiveComplexity.Problems.GraphIso.Hardness`, which is why the
completeness theorems of the problems stated over the *directed* vocabulary are
collected here rather than beside their reductions.

Complete for the degree: Graph Isomorphism itself
(`DescriptiveComplexity.graphIso_GI_complete`), Digraph Isomorphism
(`DescriptiveComplexity.digraphIso_GI_complete`) and DAG Isomorphism
(`DescriptiveComplexity.dagIso_GI_complete`).
-/

namespace DescriptiveComplexity

/-- DAG Isomorphism belongs to the GI degree: forget the topological orders,
then turn the digraph into a simple graph. -/
theorem dagIso_mem_GI : DagIso ∈ GI :=
  ⟨(dagIso_fo_reduction_digraphIso.trans digraphIso_fo_reduction_graphIso).toOrdered⟩

/-- DAG Isomorphism is hard for the GI degree: Digraph Isomorphism, which is,
reduces to it. -/
theorem dagIso_GI_hard : GI.Hard DagIso :=
  GI.hard_of_foReduction digraphIso_fo_reduction_dagIso digraphIso_GI_complete.hard

/-- **DAG Isomorphism is GI-complete**: it reduces to Digraph Isomorphism by
forgetting the carried topological orders, and Digraph Isomorphism reduces to it
by subdividing every arc twice. -/
theorem dagIso_GI_complete : GI.Complete DagIso :=
  ⟨dagIso_mem_GI, dagIso_GI_hard⟩

end DescriptiveComplexity
