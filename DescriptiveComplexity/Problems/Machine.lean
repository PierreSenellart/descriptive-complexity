/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Problems.Machine.Walk
import DescriptiveComplexity.Problems.Machine.Membership
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.Problems.Machine.Tape
import DescriptiveComplexity.Problems.Machine.Hardness
import DescriptiveComplexity.Problems.Machine.Interp
import DescriptiveComplexity.Problems.Machine.Fixpoint
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.HornSat

/-!
# Machine acceptance is NP-complete

Umbrella file for `DescriptiveComplexity.NTMAccept`, the problem “does this
nondeterministic Turing machine accept its input within as many steps as there
are positions?”, with the machine carried by the instance.

The point of the problem is the bridge described in `MACHINE.md`: every class
in this library is a definition in logic and every completeness theorem is
discharged by a first-order reduction, so that these classes really are *the*
NP and *the* P was, until this file, a citation. `NTMAccept` closes that gap
from inside the framework:

* **membership** (`DescriptiveComplexity.ntmAccept_mem_NP`,
  `DescriptiveComplexity.Problems.Machine.Membership`) is Fagin's tableau argument – one
  existential block guesses the run, a first-order kernel checks it, and
  `DescriptiveComplexity.TMData.accepts_iff_exists_walk` turns an `ℕ`-indexed run into
  one indexed by the position elements, which is where the unary time bound is
  cashed in;
* **hardness** (`DescriptiveComplexity.ntmAccept_NP_hard`) is the reduction
  `SAT ≤ᶠᵒ[≤] NTMAccept`: a bespoke machine – guess an assignment in one sweep,
  check one clause per sweep, alternating direction – built *semantically* in
  `DescriptiveComplexity.Problems.Machine.Hardness` on the tape of
  `DescriptiveComplexity.Problems.Machine.Tape`, run by the phase machinery of
  `DescriptiveComplexity.Problems.Machine.Program`, and transcribed into defining
  formulas in `DescriptiveComplexity.Problems.Machine.Interp`.

Two consequences are worth naming. `DescriptiveComplexity.mem_NP_iff_le_ntmAccept` is
the machine characterization of the class: a problem is in NP – that is,
`Σ₁`-definable – exactly when it ordered-FO-reduces to machine acceptance.
And `DescriptiveComplexity.ntmAccept_reduces_to_sat` is the *textbook form* of the
Cook–Levin theorem – machine acceptance reduces to satisfiability – obtained
from the machine-free Tseitin discharge with no tableau-to-CNF encoding: the
membership proof already wrote the run as a `Σ₁` formula, and the generic
reduction to SAT applies to it like to any other.

As with any complexity-theoretic statement, these results are about finite
structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Machine acceptance is NP-hard: SAT reduces to it by building the machine
`M_φ` inside the instance. -/
theorem ntmAccept_NP_hard : NP.Hard NTMAccept :=
  NP.hard_of_orderedReduction SatTM.sat_ordered_fo_reduction_ntmAccept sat_NP_hard

/-- **Machine acceptance is NP-complete.** The classes of this library are
defined in logic; this theorem is the bridge saying its NP is the machine
one. -/
theorem ntmAccept_NP_complete : NP.Complete NTMAccept :=
  ⟨ntmAccept_mem_NP, ntmAccept_NP_hard⟩

/-- **The machine characterization of NP**: a problem is `Σ₁`-definable exactly
when it ordered-FO-reduces to machine acceptance. Forward through SAT – the
generic Tseitin discharge followed by the machine of a CNF formula – and
backward because membership travels along reductions. -/
theorem mem_NP_iff_le_ntmAccept {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ NP ↔ Nonempty (P ≤ᶠᵒ[≤] NTMAccept) := by
  constructor
  · intro hP
    obtain ⟨g⟩ := sat_hard_of_sigmaSODefinable P hP
    exact ⟨g.trans SatTM.sat_ordered_fo_reduction_ntmAccept⟩
  · rintro ⟨f⟩
    exact NP.mem_of_orderedReduction f ntmAccept_mem_NP

/-- **The textbook Cook–Levin theorem**: machine acceptance reduces to
satisfiability. No tableau-to-CNF encoding appears: the `Σ₁` definition of
acceptance feeds the machine-free Tseitin discharge. -/
theorem ntmAccept_reduces_to_sat : Nonempty (NTMAccept ≤ᶠᵒ[≤] SAT) :=
  sat_hard_of_sigmaSODefinable NTMAccept ntmAccept_sigmaSODefinable

/-! ### The deterministic problem

`DescriptiveComplexity.dtmAccept_mem_PTIME` – a deterministic run is a least fixed
point – is stage 2b of the bridge, proved in
`DescriptiveComplexity.Problems.Machine.Fixpoint`. Its hardness half (stage 4, the
unit-propagation machine for `HORNSAT ≤ᶠᵒ[≤] DTMAccept`) is still open, so the
PTIME-completeness theorem is not yet available; what already follows from
membership alone is recorded here. -/

/-- Deterministic machine acceptance is in NP: `PTIME ⊆ NP`. -/
theorem dtmAccept_mem_NP : DTMAccept ∈ NP :=
  PTIME_subset_NP dtmAccept_mem_PTIME

/-- **Determinism is a special case of nondeterminism**, as a reduction:
deterministic acceptance reduces to machine acceptance. (Through SAT, by the
machine characterization of NP – no bespoke interpretation needed.) -/
theorem dtmAccept_reduces_to_ntmAccept : Nonempty (DTMAccept ≤ᶠᵒ[≤] NTMAccept) :=
  (mem_NP_iff_le_ntmAccept DTMAccept).mp dtmAccept_mem_NP

/-- **The textbook Grädel-side discharge**: deterministic machine acceptance
reduces to HORN-SAT, the P-level analogue of
`DescriptiveComplexity.ntmAccept_reduces_to_sat`. -/
theorem dtmAccept_reduces_to_hornSat : Nonempty (DTMAccept ≤ᶠᵒ[≤] HORNSAT) :=
  hornSat_hard_of_sigmaSOHornDefinable DTMAccept dtmAccept_mem_PTIME

end DescriptiveComplexity
