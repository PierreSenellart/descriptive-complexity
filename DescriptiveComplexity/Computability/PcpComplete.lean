/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard
import DescriptiveComplexity.Problems.Pcp.Hardness
import DescriptiveComplexity.Problems.Pcp.Membership

/-!
# Post's correspondence problem is RE-complete

The two halves meet: `DescriptiveComplexity.HALT` is RE-hard
(`DescriptiveComplexity.halt_RE_hard`, the machine bridge) and reduces to
`DescriptiveComplexity.PCP` by the computation-history dominoes
(`DescriptiveComplexity.halt_ordered_fo_reduction_pcp`), so `PCP` is RE-hard;
with membership (`DescriptiveComplexity.pcp_mem_RE`) it is RE-complete.

Undecidability of Post's problem
(`DescriptiveComplexity.pcp_not_computable`) follows with no computability
work of its own: RE-hardness makes the concrete instances a target of the
code model's halting problem, and first-order reductions are computable.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **PCP is RE-hard**: the halting problem is, and its computation-history
dominoes carry hardness forward. -/
theorem pcp_RE_hard : RE.Hard PCP :=
  RE.hard_of_orderedReduction halt_ordered_fo_reduction_pcp halt_RE_hard

/-- **PCP is RE-complete.**
Registered in the Lax archive as
[`Lax624099.PcpREComplete.pcp_RE_complete`](https://laxarchive.org/lax-624099/Lax624099.PcpREComplete.html#s-Lax624099.PcpREComplete.pcp_RE_complete). -/
theorem pcp_RE_complete : RE.Complete PCP :=
  ⟨pcp_mem_RE, pcp_RE_hard⟩

/-- **Post's correspondence problem is undecidable**: no numbering of its
instances has a computable characteristic function.
Registered in the Lax archive as
[`Lax624099.PcpUndecidable.pcp_not_computable`](https://laxarchive.org/lax-624099/Lax624099.PcpUndecidable.html#s-Lax624099.PcpUndecidable.pcp_not_computable). -/
theorem pcp_not_computable (V : FinVocab Language.pcp) :
    ¬ComputablePred (PCP.toPred V) :=
  not_computablePred_of_RE_hard pcp_RE_hard V

end DescriptiveComplexity
