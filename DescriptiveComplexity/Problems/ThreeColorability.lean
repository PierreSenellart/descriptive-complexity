/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.ThreeColorability.ToSat
import DescriptiveComplexity.Problems.ThreeColorability.FromSat

/-!
# 3-colorability is NP-complete

Umbrella file for the problem 3COL (`DescriptiveComplexity.ThreeCol`, defined in
`DescriptiveComplexity.Problems.ThreeColorability.Defs`), collecting its two
first-order reductions –

* `DescriptiveComplexity.threeCol_fo_reduction_sat : ThreeCol ≤ᶠᵒ SAT` (order-free,
  quantifier-free; `DescriptiveComplexity.Problems.ThreeColorability.ToSat`), and
* `DescriptiveComplexity.sat_ordered_fo_reduction_threeCol : SAT ≤ᶠᵒ[≤] ThreeCol`
  (ordered; `DescriptiveComplexity.Problems.ThreeColorability.FromSat`) –

and deriving its NP-completeness from the Cook–Levin theorem
(`DescriptiveComplexity.SAT_NP_complete`), with no machine model anywhere. As with any
complexity-theoretic statement, these results are about finite graphs only
(`ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- 3-colorability is in NP: it FO-reduces to SAT, which is in NP. -/
theorem threeCol_mem_NP : ThreeCol ∈ NP :=
  NP.mem_of_foReduction threeCol_fo_reduction_sat sat_mem_NP

/-- 3-colorability is NP-hard: SAT, which is NP-hard, reduces to it by an
ordered FO reduction. -/
theorem threeCol_NP_hard : NP.Hard ThreeCol :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_threeCol sat_NP_hard

/-- **3-colorability is NP-complete**, derived from the two first-order
reductions of this library and the Cook–Levin theorem. -/
theorem threeCol_NP_complete : NP.Complete ThreeCol :=
  ⟨threeCol_mem_NP, threeCol_NP_hard⟩

end DescriptiveComplexity
