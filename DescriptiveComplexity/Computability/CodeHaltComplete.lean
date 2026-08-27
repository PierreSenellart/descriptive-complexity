/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Computability.CodeHalt
import DescriptiveComplexity.Problems.CodeHalt.Hardness

/-!
# RE is exactly recursive enumerability

The three readings of the one construction of
`DescriptiveComplexity.Problems.CodeHalt.Hardness`, the ordered first-order
reduction of any semi-decidable problem to `DescriptiveComplexity.CODEHALT`.

* **`DescriptiveComplexity.codehalt_RE_complete`** – `CODEHALT` is RE-complete:
  membership is `DescriptiveComplexity.codehalt_mem_RE`, and hardness is the
  reduction instantiated at `DescriptiveComplexity.FINSAT`, which is RE-hard
  already, and transported forward.
* **`DescriptiveComplexity.mem_RE_iff_rePred`** – a decision problem is in the
  logically defined class `DescriptiveComplexity.RE` exactly when its concrete
  instances form a recursively enumerable set. This is the RE analogue of the
  machine side of Fagin's theorem, with no machine model on either side: the
  forward half evaluates the `∃SO[new]` kernel on a searched-for witness
  (`DescriptiveComplexity.RE_subset_rePred`), the converse draws the
  semi-decision procedure inside the instance.
* **`DescriptiveComplexity.RE_ne_coRE`** – RE and co-RE differ. Were `CODEHALTᶜ`
  recursively enumerable, the equivalence above would make `CODEHALT.toPred` and its complement both
  `REPred`, hence computable by Post's theorem, against
  `DescriptiveComplexity.not_computablePred_codehalt`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **CODEHALT is RE-hard.** Finite satisfiability is RE-hard and recursively
enumerable, so it reduces to `CODEHALT` by the construction of
`DescriptiveComplexity.orderedReduction_codehalt`, and hardness travels
forward. -/
theorem codehalt_RE_hard : RE.Hard CODEHALT :=
  (orderedReduction_codehalt FINSAT finsat_rePred).elim fun f =>
    RE.hard_of_orderedReduction f finsat_RE_hard

/-- **CODEHALT is RE-complete.** -/
theorem codehalt_RE_complete : RE.Complete CODEHALT :=
  ⟨codehalt_mem_RE, codehalt_RE_hard⟩

/-- **RE is exactly the recursively enumerable properties of finite
structures.** A problem is `∃SO[new]`-definable exactly when the set of its
concrete instances is semi-decidable in Mathlib's sense. -/
theorem mem_RE_iff_rePred {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : P ∈ RE ↔ REPred (P.toPred V) :=
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
    ⟨(mem_RE_iff_rePred codeVocab CODEHALT).mp h1,
      (mem_RE_iff_rePred codeVocab CODEHALTᶜ).mp h2⟩

end DescriptiveComplexity
