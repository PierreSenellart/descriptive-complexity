/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Defs
import DescriptiveComplexity.Problems.CliqueFamily.Reductions
import DescriptiveComplexity.Composition

/-!
# The clique family

Umbrella file for the problems Clique, Independent Set and Vertex Cover on
marked graphs (`DescriptiveComplexity.Clique`, `DescriptiveComplexity.IndependentSet`,
`DescriptiveComplexity.VertexCover`, defined in
`DescriptiveComplexity.Problems.CliqueFamily.Defs`), collecting the quantifier-free
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions` and their
composites: all three problems are FO-interreducible.
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

end DescriptiveComplexity
