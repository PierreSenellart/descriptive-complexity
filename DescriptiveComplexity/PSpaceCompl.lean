/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat
import DescriptiveComplexity.Problems.SuccinctReach

/-!
# `PSPACE = coPSPACE`

**The theorem**: polynomial space is closed under complement. In this library
PSPACE is *defined* by SO(TC) (`DescriptiveComplexity.PSPACE`), and the complement
of a walk is not a walk, so this is not the definitional duality that gives
`PiP k` from `SigmaP k`. It is assembled from three pieces:

* every SO(TC) definable problem reduces to SUCCINCT-REACH
  (`DescriptiveComplexity.succinctReach_hard_of_sotcDefinable`, the Tseitin
  discharge) and from there to QSAT
  (`DescriptiveComplexity.succinctReach_ordered_fo_reduction_qsat`, Savitch's
  recursive doubling);
* complementing an ordered reduction is free – the same interpretation
  (`DescriptiveComplexity.OrderedFOReduction.compl`);
* the complement of QSAT is SO(TC) definable
  (`DescriptiveComplexity.qsatCompl_sotcDefinable`), because the walk that decides
  QSAT is *deterministic* and computes the value of the formula, so reading its
  answer the other way round decides the complement.

That third piece is where the content sits, and it is the logical shadow of the
machine-theoretic reason PSPACE is closed under complement: a space-bounded
computation can be made deterministic (Savitch), and a deterministic decider is
complemented by flipping its answer. Savitch's recursive doubling is what
`DescriptiveComplexity.Problems.Qsat.Hardness` spends to turn the *nondeterministic*
walk of an arbitrary SO(TC) specification into the deterministic evaluation of a
quantified Boolean formula.
-/

namespace DescriptiveComplexity

open FirstOrder Language

variable {L : Language.{0, 0}}

/-! ### SO(TC) is closed under complement -/

/-- **SO(TC) is closed under complement**: the complement of an SO(TC) definable
problem is SO(TC) definable.

Reduce to QSAT – through SUCCINCT-REACH and Savitch's recursive doubling – and
read the deterministic evaluation walk of QSAT backwards. -/
theorem SOTCDefinable.compl [L.IsRelational] {P : DecisionProblem L} (h : SOTCDefinable P) :
    SOTCDefinable Pᶜ := by
  obtain ⟨f⟩ := succinctReach_hard_of_sotcDefinable P h
  exact qsatCompl_sotcDefinable.of_orderedReduction
    (f.trans succinctReach_ordered_fo_reduction_qsat).compl

/-- Complementation is a bijection of the SO(TC) definable problems. -/
theorem sotcDefinable_compl_iff [L.IsRelational] (P : DecisionProblem L) :
    SOTCDefinable Pᶜ ↔ SOTCDefinable P := by
  refine ⟨fun h => ?_, SOTCDefinable.compl⟩
  have h2 := h.compl
  rwa [DecisionProblem.compl_compl] at h2

/-! ### `PSPACE = coPSPACE` -/

/-- **`PSPACE = coPSPACE`**: polynomial space is closed under complement. -/
theorem PSPACE_eq_coPSPACE : PSPACE = coPSPACE := by
  refine ComplexityClass.ext (fun P => (sotcDefinable_compl_iff P).symm) fun P => ?_
  constructor
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sotcDefinable_compl_iff Q).mp hQ)
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sotcDefinable_compl_iff Q).mpr hQ)

/-- Membership in PSPACE is closed under complement. -/
theorem mem_PSPACE_compl_iff [L.IsRelational] (P : DecisionProblem L) : Pᶜ ∈ PSPACE ↔ P ∈ PSPACE :=
  sotcDefinable_compl_iff P

/-- **QSAT is coPSPACE-complete**, since PSPACE and coPSPACE coincide. -/
theorem QSAT_coPSPACE_complete : coPSPACE.Complete QSAT :=
  PSPACE_eq_coPSPACE ▸ qsat_PSPACE_complete

end DescriptiveComplexity
