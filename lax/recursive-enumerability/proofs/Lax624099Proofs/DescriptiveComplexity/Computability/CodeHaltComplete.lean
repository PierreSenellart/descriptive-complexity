/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Computability.CodeHalt
import Lax624099Proofs.DescriptiveComplexity.Problems.CodeHalt.Hardness
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
# RE is exactly recursive enumerability

The three readings of the one construction of
`Lax624099Proofs.DescriptiveComplexity.Problems.CodeHalt.Hardness`, the ordered first-order
reduction of any semi-decidable problem to `Lax624099Proofs.DescriptiveComplexity.CODEHALT`.

* **`Lax624099Proofs.DescriptiveComplexity.codehalt_RE_complete`** – `CODEHALT` is RE-complete:
  membership is `Lax624099Proofs.DescriptiveComplexity.codehalt_mem_RE`, and hardness is the
  reduction instantiated at `Lax624099Proofs.DescriptiveComplexity.FINSAT`, which is RE-hard
  already, and transported forward.
* **`Lax624099Proofs.DescriptiveComplexity.mem_RE_iff_rePred`** – a decision problem is in the
  logically defined class `Lax624099Proofs.DescriptiveComplexity.RE` exactly when its concrete
  instances form a recursively enumerable set. This is the RE analogue of the
  machine side of Fagin's theorem, with no machine model on either side: the
  forward half evaluates the `∃SO[new]` kernel on a searched-for witness
  (`Lax624099Proofs.DescriptiveComplexity.RE_subset_rePred`), the converse draws the
  semi-decision procedure inside the instance.
* **`Lax624099Proofs.DescriptiveComplexity.RE_ne_coRE`** – RE and co-RE differ. Were `CODEHALTᶜ`
  recursively enumerable, the equivalence above would make `CODEHALT.toPred` and its complement both
  `REPred`, hence computable by Post's theorem, against
  `Lax624099Proofs.DescriptiveComplexity.not_computablePred_codehalt`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **RE is exactly the recursively enumerable properties of finite
structures.** A problem is `∃SO[new]`-definable exactly when the set of its
concrete instances is semi-decidable in Mathlib's sense. -/
theorem mem_RE_iff_rePred {L : Language.{0, 0}} [L.IsRelational] (V : Lax624099.ConcreteInstances.FinVocab L)
    (P : Lax904597.Problems.DecisionProblem L) : P ∈ RE ↔ REPred (P.toPred V) :=
  ⟨fun hP => RE_subset_rePred V P hP,
    fun h => (orderedReduction_codehalt P h).elim fun f =>
      RE.mem_of_orderedReduction f codehalt_mem_RE⟩

/-- **RE is not closed under complement.** With the equivalence above, this is
Post's theorem applied to the undecidability of `CODEHALT`: a problem and its
complement both recursively enumerable would be decidable. -/
theorem RE_ne_coRE : RE ≠ coRE := by
  intro heq
  have h1 : CODEHALT ∈ RE := codehalt_mem_RE
  have h2 : CODEHALTᶜ ∈ RE := (mem_coRE_iff CODEHALT).mp (heq ▸ h1)
  refine not_computablePred_codehalt ?_
  exact ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨(mem_RE_iff_rePred Lax624099.ConcreteInstances.codeVocab CODEHALT).mp h1,
      (mem_RE_iff_rePred Lax624099.ConcreteInstances.codeVocab CODEHALTᶜ).mp h2⟩

end Lax624099Proofs.DescriptiveComplexity


