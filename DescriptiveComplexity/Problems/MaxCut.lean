/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MaxCut.Defs
import DescriptiveComplexity.Problems.MaxCut.Membership
import DescriptiveComplexity.Problems.MaxCut.Reduction
import DescriptiveComplexity.Problems.NaeThreeSat

/-!
# Max Cut is NP-complete

Umbrella file for `DescriptiveComplexity.MaxCut`, Karp's MAX CUT
([Karp 1972][karp1972reducibility]) on the arc-marked vocabulary reused from
Feedback Arc Set, deriving NP-completeness from

* `DescriptiveComplexity.maxCut_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.MaxCut.Membership`): membership, by guessing one
  side of the cut and an injection of the marked pairs into the cut;
* `DescriptiveComplexity.MaxCutRed.nae3Sat_ordered_fo_reduction_maxCut`
  (`DescriptiveComplexity.Problems.MaxCut.Reduction`): hardness, from the NP-hardness
  of NAE-3SAT (`DescriptiveComplexity.Problems.NaeThreeSat`), and so ultimately from
  the Cook–Levin theorem, with no machine model anywhere.

No edge weights and no parallel edges are needed: the gadget graph is a plain
finite graph, its cut splits into three independently maximal families, and
the threshold is the `Set.ncard` of a marked binary relation. As with any
complexity-theoretic statement, these results are about finite structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Max Cut is in NP: it is `Σ₁`-definable. -/
theorem maxCut_mem_NP : MaxCut ∈ NP :=
  maxCut_sigmaSODefinable

/-- Max Cut is NP-hard: NAE-3SAT, which is NP-hard, ordered-FO-reduces to it
by the gadget graph of `DescriptiveComplexity.Problems.MaxCut.Interp`. -/
theorem maxCut_NP_hard : NP.Hard MaxCut :=
  NP.hard_of_orderedReduction MaxCutRed.nae3Sat_ordered_fo_reduction_maxCut nae3Sat_NP_hard

/-- **Max Cut is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem maxCut_NP_complete : NP.Complete MaxCut :=
  ⟨maxCut_mem_NP, maxCut_NP_hard⟩

end DescriptiveComplexity
