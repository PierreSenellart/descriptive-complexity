/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DominatingSet.Defs
import DescriptiveComplexity.Problems.DominatingSet.Membership
import DescriptiveComplexity.Problems.DominatingSet.Reduction
import DescriptiveComplexity.Problems.SetFamily

/-!
# Dominating Set is NP-complete

Umbrella file for `DescriptiveComplexity.DominatingSet`, deriving NP-completeness from

* `DescriptiveComplexity.dominatingSet_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.DominatingSet.Membership`): membership, by guessing
  the dominating set and an injection of it into the marked set;
* `DescriptiveComplexity.DomRed.setCover_fo_reduction_dominatingSet`
  (`DescriptiveComplexity.Problems.DominatingSet.Reduction`): hardness, from the
  NP-hardness of Set Cover, and so ultimately from the Cook–Levin theorem.

The reduction is **order-free**, which is worth recording: domination
constrains every element of the universe, junk tuples included, and the two
degenerate cases (an element in no set, and no element at all) look at first
sight as if they needed a canonical extra vertex – i.e. an order. They do not:
both are first-order conditions, so gating on them is enough.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Dominating Set is in NP: it is `Σ₁`-definable. -/
theorem dominatingSet_mem_NP : DominatingSet ∈ NP :=
  dominatingSet_sigmaSODefinable

/-- Dominating Set is NP-hard: Set Cover, which is NP-hard, FO-reduces to it
by the incidence graph of the set system. -/
theorem dominatingSet_NP_hard : NP.Hard DominatingSet :=
  NP.hard_of_foReduction DomRed.setCover_fo_reduction_dominatingSet setCover_NP_hard

/-- **Dominating Set is NP-complete**, derived from the first-order reductions
of this library and the Cook–Levin theorem. -/
theorem dominatingSet_NP_complete : NP.Complete DominatingSet :=
  ⟨dominatingSet_mem_NP, dominatingSet_NP_hard⟩

end DescriptiveComplexity
