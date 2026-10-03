/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltHard
import Lax624099Proofs.DescriptiveComplexity.Problems.Pcp.Hardness
import Lax624099Proofs.DescriptiveComplexity.Problems.Pcp.Membership
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax904597.Problems.DecisionProblem
export Lax624099.ConcreteInstances.DecisionProblem (toPred)
end Lax904597.Problems.DecisionProblem

/-!
# Post's correspondence problem is RE-complete

The two halves meet: `Lax624099Proofs.DescriptiveComplexity.HALT` is RE-hard
(`Lax624099Proofs.DescriptiveComplexity.halt_RE_hard`, the machine bridge) and reduces to
`Lax624099Proofs.DescriptiveComplexity.PCP` by the computation-history dominoes
(`Lax624099Proofs.DescriptiveComplexity.halt_ordered_fo_reduction_pcp`), so `PCP` is RE-hard;
with membership (`Lax624099Proofs.DescriptiveComplexity.pcp_mem_RE`) it is RE-complete.

Undecidability of Post's problem
(`Lax624099Proofs.DescriptiveComplexity.pcp_not_computable`) follows with no computability
work of its own: RE-hardness makes the concrete instances a target of the
code model's halting problem, and first-order reductions are computable.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **PCP is RE-hard**: the halting problem is, and its computation-history
dominoes carry hardness forward. -/
theorem pcp_RE_hard : RE.Hard PCP :=
  RE.hard_of_orderedReduction halt_ordered_fo_reduction_pcp halt_RE_hard

/-- **Post's correspondence problem is undecidable**: no numbering of its
instances has a computable characteristic function. -/
theorem pcp_not_computable (V : Lax624099.ConcreteInstances.FinVocab Lax624099.PostCorrespondence.pcp) :
    ¬ComputablePred (PCP.toPred V) :=
  not_computablePred_of_RE_hard pcp_RE_hard V

end Lax624099Proofs.DescriptiveComplexity


