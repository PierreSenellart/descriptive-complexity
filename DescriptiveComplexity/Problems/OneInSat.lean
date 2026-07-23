/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Defs
import DescriptiveComplexity.Problems.OneInSat.Slots
import DescriptiveComplexity.Problems.OneInSat.Reduction
import DescriptiveComplexity.Problems.ThreeSat
import DescriptiveComplexity.Hierarchy

/-!
# 1-in-SAT is NP-complete

Umbrella file for `DescriptiveComplexity.OneInSAT`, exactly-one satisfiability,
deriving NP-completeness from

* `DescriptiveComplexity.oneInSat_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.OneInSat.Defs`): membership, by guessing the
  assignment and checking that every clause has a true literal – SAT's kernel –
  and no second one;
* `DescriptiveComplexity.OneInRed.threeSat_ordered_fo_reduction_oneInSat`
  (`DescriptiveComplexity.Problems.OneInSat.Reduction`): hardness, from the
  NP-hardness of 3SAT, and so ultimately from the Cook–Levin theorem, with no
  machine model anywhere.

The gadget normalizes every clause to three *slots*
(`DescriptiveComplexity.Problems.OneInSat.Slots`), which is what lets one uniform
construction handle clauses of width 0, 1, 2 and 3 at once.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- 1-in-SAT is in NP: it is `Σ₁`-definable. -/
theorem oneInSat_mem_NP : OneInSAT ∈ NP :=
  oneInSat_sigmaSODefinable

/-- 1-in-SAT is NP-hard: 3SAT, which is NP-hard, ordered-FO-reduces to it by
the three-slot gadget. -/
theorem oneInSat_NP_hard : NP.Hard OneInSAT :=
  NP.hard_of_orderedReduction OneInRed.threeSat_ordered_fo_reduction_oneInSat threeSat_NP_hard

/-- **1-in-SAT is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem oneInSat_NP_complete : NP.Complete OneInSAT :=
  ⟨oneInSat_mem_NP, oneInSat_NP_hard⟩

end DescriptiveComplexity
