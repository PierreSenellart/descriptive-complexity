/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DagIso.ToDigraphIso
import DescriptiveComplexity.Problems.DagIso.FromDigraphIso

/-!
# DAG Isomorphism is GI-complete

Putting the two halves together: DAG ISOMORPHISM
(`DescriptiveComplexity.DagIso`) is complete for the degree of Graph
Isomorphism (`DescriptiveComplexity.GI`), the first entry of that degree
besides Digraph Isomorphism itself.

* **Membership** (`DescriptiveComplexity.dagIso_mem_GI`,
  `DescriptiveComplexity.Problems.DagIso.ToDigraphIso`): forget the topological
  orders, after checking first-order that they are ones – the check the
  instances carry their acyclicity witness for.
* **Hardness** (`DescriptiveComplexity.dagIso_GI_hard`,
  `DescriptiveComplexity.Problems.DagIso.FromDigraphIso`): subdivide every arc
  twice, so that the direction of an arc survives as the difference between
  the two subdivision levels.

Both reductions are order-free, as reductions between isomorphism problems have
to be: an interpretation commutes with isomorphisms, which is what makes the
forward half of each correctness proof available at all, and an order-invariant
reduction would only fix the *answer*, not the constructed structure up to
isomorphism.

Membership in NP comes from the same reduction as membership in the degree
(`DescriptiveComplexity.dagIso_mem_NP`); no hardness for a *class* is claimed,
and none is expected – that is what makes the degree worth having.
-/

namespace DescriptiveComplexity

/-- DAG Isomorphism is in NP: it reduces to Digraph Isomorphism, which is. -/
theorem dagIso_mem_NP : DagIso ∈ NP :=
  NP.mem_of_foReduction dagIso_fo_reduction_digraphIso digraphIso_mem_NP

end DescriptiveComplexity
