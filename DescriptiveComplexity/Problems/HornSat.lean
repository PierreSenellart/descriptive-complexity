/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.HornSat.Defs
import DescriptiveComplexity.Problems.HornSat.Membership
import DescriptiveComplexity.Problems.HornSat.Unsat
import DescriptiveComplexity.Problems.HornSat.Definability
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.Problems.HornSat.Hardness

/-!
# HORN-SAT

Umbrella file for HORN-SAT, propositional satisfiability restricted to
formulas with at most one positive literal per clause: the canonical complete
problem for polynomial time.

* `DescriptiveComplexity.Problems.HornSat.Defs`: the problem
  `DescriptiveComplexity.HORNSAT`, over the SAT vocabulary with the Horn condition
  `DescriptiveComplexity.AtMostOnePositive` folded into the yes-instances;
* `DescriptiveComplexity.Problems.HornSat.Membership`: `HORNSAT ∈ NP`, the SAT kernel
  conjoined with the first-order Horn condition;
* `DescriptiveComplexity.Problems.HornSat.Hardness`: the *Horn discharge* – every
  SO-Horn definable problem (`DescriptiveComplexity.SigmaSOHornDefinable`) admits an
  ordered first-order reduction to HORN-SAT;
* `DescriptiveComplexity.Problems.HornSat.Unsat`: `HORNSAT ∈ coNP`, by a first-order
  checkable certificate of Horn *un*satisfiability (a derivation-closed set
  with its derivation order). HORN-SAT is thus in `NP ∩ coNP`, as a
  polynomial-time problem should be, and complementing the discharge gives the
  level-0 inclusions of the hierarchy;
* `DescriptiveComplexity.Problems.HornSat.Definability`: `HORNSAT ∈ PTIME`, the Horn
  program computing unit propagation – which with the discharge makes HORN-SAT
  **PTIME-complete**.

What the two halves add up to is stated at the end of this file:
`DescriptiveComplexity.hornSat_PTIME_hard` and `DescriptiveComplexity.PTIME_subset_NP`.

## What the hardness statement says, and what it does not

The discharge `DescriptiveComplexity.hornSat_hard_of_sigmaSOHornDefinable` is the exact
analogue, one level down, of the Cook–Levin discharge
`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`: it is the reason SAT is NP-hard
transposed to the Horn fragment, and it is meaningful *before* polynomial time
is defined – it says that HORN-SAT is at least as hard as everything the Horn
fragment can express. It is also markedly simpler, since a Horn program needs
no Tseitin gates.

One thing is deliberately *not* claimed: **Grädel's capture theorem against
machines is not formalized.** That SO-Horn captures polynomial time on ordered
structures ([Grädel 1992][gradel1992capturing]) has a direction – every
machine-polynomial-time problem is SO-Horn definable – that simulates a
machine, and so lies outside a machine-model-free library. So
`DescriptiveComplexity.PTIME` is *defined* as SO-Horn definability, exactly as NP is
defined as `Σ₁`-definability, and the identification with the
machine-theoretic class stays a citation.

Closure of level 0 under complement, by contrast, *is* a theorem. Since
HORN-SAT is PTIME-complete, `PiP 0 = SigmaP 0` is equivalent to a single crisp
question: **is Horn *un*satisfiability SO-Horn definable?** The certificate of
`DescriptiveComplexity.Problems.HornSat.Unsat` only puts it in NP, and the fragment
cannot do it head-on: a Horn program accepts when the least model of its rules
satisfies its goal clauses, so to accept the *unsatisfiable* instances one
would have to derive a contradiction from a universally quantified statement
about the least model – the negative information a goal clause cannot supply.
The route that works is the logic-to-logic equivalence SO-Horn = FO(LFP) of
`DescriptiveComplexity.FixedPointHorn`, a full logic being closed under negation by
construction; `DescriptiveComplexity.hornSat_compl_mem_PTIME` below is the resulting
answer, and `DescriptiveComplexity.piP_zero_eq` the resulting identity.
-/

namespace DescriptiveComplexity

/-- **HORN-SAT is PTIME-hard**, machine-free: every SO-Horn definable problem
admits an ordered first-order reduction to it. -/
theorem hornSat_PTIME_hard : PTIME.Hard HORNSAT :=
  (hard_PTIME_iff HORNSAT).mpr fun Q hQ => hornSat_hard_of_sigmaSOHornDefinable Q hQ

/-- **HORN-SAT is PTIME-complete.** Membership is
`DescriptiveComplexity.hornSat_mem_PTIME` – the Horn program that computes unit
propagation, assembling the unbounded body of an input clause along the order;
hardness is `DescriptiveComplexity.hornSat_PTIME_hard`, the Horn discharge. This is the
P-level analogue of the Cook–Levin theorem, and like it it is machine-free. -/
theorem HORNSAT_PTIME_complete : PTIME.Complete HORNSAT :=
  ⟨hornSat_mem_PTIME, hornSat_PTIME_hard⟩

/-- **PTIME ⊆ NP**, i.e. `SigmaP 0 ⊆ SigmaP 1`: every SO-Horn definable problem
reduces to HORN-SAT, which is in NP. This is the level-0 case of
`DescriptiveComplexity.sigmaP_subset_sigmaP_succ`; it lives here rather than with the
hierarchy because it goes through the Horn discharge, needing no separate
compilation of a Horn program into an existential second-order sentence. -/
theorem PTIME_subset_NP : PTIME ⊆ NP := by
  intro L P hP
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable P hP
  exact NP.mem_of_orderedReduction f hornSat_mem_NP

/-- **co-PTIME ⊆ coNP**, i.e. `PiP 0 ⊆ PiP 1`: the mirror of
`DescriptiveComplexity.PTIME_subset_NP` under complementation. -/
theorem coPTIME_subset_coNP : PiP 0 ⊆ PiP 1 := by
  intro L P hP
  rw [mem_piP_iff] at hP ⊢
  exact PTIME_subset_NP hP

/-- **PTIME ⊆ coNP**, i.e. `SigmaP 0 ⊆ PiP 1`: complementing the Horn
discharge sends an SO-Horn definable problem to the complement of HORN-SAT,
which is in NP by the unsatisfiability certificate
`DescriptiveComplexity.hornSat_compl_mem_NP`. -/
theorem PTIME_subset_coNP : PTIME ⊆ coNP := by
  intro L P hP
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable P hP
  exact (mem_piP_iff 1 P).mpr (NP.mem_of_orderedReduction f.compl hornSat_compl_mem_NP)

/-- **co-PTIME ⊆ NP**, i.e. `PiP 0 ⊆ SigmaP 1`: the mirror of
`DescriptiveComplexity.PTIME_subset_coNP`. -/
theorem coPTIME_subset_NP : PiP 0 ⊆ NP := by
  intro L P hP
  rw [mem_piP_iff] at hP
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable Pᶜ hP
  exact NP.mem_of_orderedReduction (f.compl.congrSource fun A _ _ => not_not)
    hornSat_compl_mem_NP

/-- `PiP 0 ⊆ PH`, the level-0 case of `DescriptiveComplexity.piP_subset_PH`. -/
theorem piP_zero_subset_PH : PiP 0 ⊆ PH :=
  fun _ _ hP => ⟨1, coPTIME_subset_NP hP⟩

/-- HORN-SAT is FO(LFP) definable, being SO-Horn definable. -/
theorem hornSat_lfpDefinable : LFPDefinable HORNSAT :=
  hornSat_sigmaSOHornDefinable.lfpDefinable

/-- **Horn unsatisfiability is FO(LFP) definable**: in the logic it is one
negation away from `DescriptiveComplexity.hornSat_lfpDefinable`. In the fragment there
is no such move – the statement below needs the full translation back. -/
theorem hornSat_compl_lfpDefinable : LFPDefinable HORNSATᶜ :=
  hornSat_lfpDefinable.compl

/-- **Horn unsatisfiability is SO-Horn definable** – the crisp question behind
`PiP 0 = SigmaP 0`, answered through the equivalence with FO(LFP): the
translation of `DescriptiveComplexity.FixedPointHorn` turns the negated unit
propagation back into a Horn program. -/
theorem hornSat_compl_mem_PTIME : HORNSATᶜ ∈ PTIME :=
  hornSat_sigmaSOHornDefinable.compl

end DescriptiveComplexity
