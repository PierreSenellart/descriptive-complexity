/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Coloring.Defs
import DescriptiveComplexity.Problems.Coloring.Reductions
import DescriptiveComplexity.Problems.Coloring.Membership
import DescriptiveComplexity.Problems.ThreeColorability
import DescriptiveComplexity.Composition

/-!
# The coloring family is NP-complete

Umbrella file for `k`-colorability, Chromatic Number and Clique Cover
(`DescriptiveComplexity.KCol`, `DescriptiveComplexity.ChromaticNumber`,
`DescriptiveComplexity.CliqueCover`, defined in
`DescriptiveComplexity.Problems.Coloring.Defs`), collecting the reductions of
`DescriptiveComplexity.Problems.Coloring.Reductions` and deriving NP-completeness from

* the `Σ₁` definitions of `DescriptiveComplexity.Problems.Coloring.Membership` – color
  classes as `k` unary relations for the fixed-`k` problem, a coloring by the
  marked elements as one binary relation for the two threshold problems;
* the NP-hardness of 3-colorability
  (`DescriptiveComplexity.threeCol_NP_hard`), and so ultimately the Cook–Levin
  theorem, with no machine model anywhere: `KCol k` for `k ≥ 3` by padding,
  Chromatic Number by the ordered reduction marking three copies of the
  minimum, and Clique Cover by complementing the edges.

The chain is `3COL ≤ᶠᵒ[≤] ChromaticNumber ≤ᶠᵒ CliqueCover ≤ᶠᵒ ChromaticNumber`:
the last two problems are interreducible, so it does not matter which of them
carries the hardness. As with any complexity-theoretic statement, these
results are about finite structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### `k`-colorability -/

/-- `k`-colorability is in NP: it is `Σ₁`-definable. -/
theorem kCol_mem_NP (k : ℕ) : KCol k ∈ NP :=
  kCol_sigmaSODefinable k

/-- For `k ≥ 3`, `k`-colorability is NP-hard: 3-colorability, which is
NP-hard, reduces to it by padding. -/
theorem kCol_NP_hard {k : ℕ} (hk : 3 ≤ k) : NP.Hard (KCol k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := ⟨k - 3, by omega⟩
  exact NP.hard_of_foReduction (threeCol_fo_reduction_kCol m) threeCol_NP_hard

/-- **`k`-colorability is NP-complete for every `k ≥ 3`.** -/
theorem kCol_NP_complete {k : ℕ} (hk : 3 ≤ k) : NP.Complete (KCol k) :=
  ⟨kCol_mem_NP k, kCol_NP_hard hk⟩

/-! ### Chromatic Number and Clique Cover -/

/-- Chromatic Number is in NP: it is `Σ₁`-definable. -/
theorem chromaticNumber_mem_NP : ChromaticNumber ∈ NP :=
  chromaticNumber_sigmaSODefinable

/-- Chromatic Number is NP-hard: 3-colorability, which is NP-hard, reduces to
it by an ordered FO reduction. -/
theorem chromaticNumber_NP_hard : NP.Hard ChromaticNumber :=
  NP.hard_of_orderedReduction threeCol_ordered_fo_reduction_chromaticNumber threeCol_NP_hard

/-- **Chromatic Number is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem chromaticNumber_NP_complete : NP.Complete ChromaticNumber :=
  ⟨chromaticNumber_mem_NP, chromaticNumber_NP_hard⟩

/-- Clique Cover is in NP: it is `Σ₁`-definable. -/
theorem cliqueCover_mem_NP : CliqueCover ∈ NP :=
  cliqueCover_sigmaSODefinable

/-- Clique Cover is NP-hard: Chromatic Number, which is NP-hard, reduces to
it by complementing the edges. -/
theorem cliqueCover_NP_hard : NP.Hard CliqueCover :=
  NP.hard_of_foReduction chromaticNumber_fo_reduction_cliqueCover chromaticNumber_NP_hard

/-- **Clique Cover is NP-complete**. -/
theorem cliqueCover_NP_complete : NP.Complete CliqueCover :=
  ⟨cliqueCover_mem_NP, cliqueCover_NP_hard⟩

end DescriptiveComplexity
