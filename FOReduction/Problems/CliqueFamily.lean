/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems.CliqueFamily.Defs
import FOReduction.Problems.CliqueFamily.Reductions
import FOReduction.Composition

/-!
# The clique family

Umbrella file for the problems Clique, Independent Set and Vertex Cover on
marked graphs (`FirstOrder.Clique`, `FirstOrder.IndependentSet`,
`FirstOrder.VertexCover`, defined in
`FOReduction.Problems.CliqueFamily.Defs`), collecting the quantifier-free
reductions of `FOReduction.Problems.CliqueFamily.Reductions` and their
composites: all three problems are FO-interreducible.
-/

namespace FirstOrder

/-- **Vertex Cover FO-reduces to Clique**, by composing the mark and edge
complementations. -/
noncomputable def vertexCover_fo_reduction_clique : VertexCover ≤ᶠᵒ Clique :=
  vertexCover_fo_reduction_indSet.trans indSet_fo_reduction_clique

/-- **Clique FO-reduces to Vertex Cover**, by composing the edge and mark
complementations. -/
noncomputable def clique_fo_reduction_vertexCover : Clique ≤ᶠᵒ VertexCover :=
  clique_fo_reduction_indSet.trans indSet_fo_reduction_vertexCover

end FirstOrder
