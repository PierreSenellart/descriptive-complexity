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
import DescriptiveComplexity.Problems.Machine.HornInterp
import DescriptiveComplexity.Problems.Machine.Space
import DescriptiveComplexity.Problems.Machine.SpaceHard
import DescriptiveComplexity.Problems.Qsat
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.HornSat

/-!
# Machine acceptance is NP-complete, and its deterministic restriction PTIME-complete

Umbrella file for `DescriptiveComplexity.NTMAccept`, the problem “does this
nondeterministic Turing machine accept its input within as many steps as there
are positions?”, with the machine carried by the instance.

The point of the problem is the machine bridge: every class
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
reduction to SAT applies to it like to any other. Conjoined with the hardness
direction, this gives `DescriptiveComplexity.ntmAccept_interreducible_sat` –
machine acceptance and satisfiability reduce to each other – the most faithful
representation of the Cook–Levin theorem this library offers.

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
theorem mem_NP_iff_le_ntmAccept {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
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

/-- **Machine acceptance and satisfiability are interreducible** – the most
faithful representation of the Cook–Levin theorem in this library, both
directions of the correspondence in one statement: acceptance reduces to
`DescriptiveComplexity.SAT` through the `Σ₁` definition of a run, and
`DescriptiveComplexity.SAT` reduces back by building the machine `M_φ`
inside the instance. -/
theorem ntmAccept_interreducible_sat :
    Nonempty (NTMAccept ≤ᶠᵒ[≤] SAT) ∧ Nonempty (SAT ≤ᶠᵒ[≤] NTMAccept) :=
  ⟨ntmAccept_reduces_to_sat, ⟨SatTM.sat_ordered_fo_reduction_ntmAccept⟩⟩

/-! ### The deterministic problem

The same bridge one level down, for `DescriptiveComplexity.DTMAccept`: membership –
a deterministic run is a least fixed point, proved in
`DescriptiveComplexity.Problems.Machine.Fixpoint` through the formalized FO(LFP) →
SO-Horn translation – and hardness by the unit-propagation machine of
`DescriptiveComplexity.Problems.Machine.HornHardness`, transcribed in
`DescriptiveComplexity.Problems.Machine.HornInterp`. Together they make deterministic
machine acceptance PTIME-complete, and the library's logically defined
polynomial time the machine one. -/

/-- Deterministic machine acceptance is in NP: `PTIME ⊆ NP`. -/
theorem dtmAccept_mem_NP : DTMAccept ∈ NP :=
  PTIME_subset_NP dtmAccept_mem_PTIME

/-- **The textbook Grädel-side discharge**: deterministic machine acceptance
reduces to HORN-SAT, the P-level analogue of
`DescriptiveComplexity.ntmAccept_reduces_to_sat`. -/
theorem dtmAccept_reduces_to_hornSat : Nonempty (DTMAccept ≤ᶠᵒ[≤] HORNSAT) :=
  hornSat_hard_of_sigmaSOHornDefinable DTMAccept dtmAccept_mem_PTIME

/-- Deterministic machine acceptance is PTIME-hard: HORN-SAT reduces to it by
building the unit-propagation machine inside the instance. -/
theorem dtmAccept_PTIME_hard : PTIME.Hard DTMAccept :=
  PTIME.hard_of_orderedReduction HornTM.hornSat_ordered_fo_reduction_dtmAccept
    hornSat_PTIME_hard

/-- **Deterministic machine acceptance is PTIME-complete**: the analogue of
`DescriptiveComplexity.ntmAccept_NP_complete` one level down. The library's
polynomial time is defined by the Horn fragment; this theorem is the bridge
saying it is the machine one. -/
theorem dtmAccept_PTIME_complete : PTIME.Complete DTMAccept :=
  ⟨dtmAccept_mem_PTIME, dtmAccept_PTIME_hard⟩

/-- **The machine characterization of PTIME**: a problem is SO-Horn definable
– equivalently, FO(LFP) definable – exactly when it ordered-FO-reduces to
deterministic machine acceptance. Forward through HORN-SAT – the Horn
discharge followed by the unit-propagation machine – and backward because
membership travels along reductions. -/
theorem mem_PTIME_iff_le_dtmAccept {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    P ∈ PTIME ↔ Nonempty (P ≤ᶠᵒ[≤] DTMAccept) := by
  constructor
  · intro hP
    obtain ⟨g⟩ := hornSat_hard_of_sigmaSOHornDefinable P hP
    exact ⟨g.trans HornTM.hornSat_ordered_fo_reduction_dtmAccept⟩
  · rintro ⟨f⟩
    exact PTIME.mem_of_orderedReduction f dtmAccept_mem_PTIME

/-! ### The space-bounded problems

Drop the step bound and the same machines measure *space* instead of time: a
run of `DescriptiveComplexity.NTMAcceptSpace` may be arbitrarily long, but it
never leaves the positions of the instance, so its configurations are the
assignments of a fixed second-order block and its runs are a transitive closure
over them. That is exactly an SO(TC) specification, so both problems are in
PSPACE (`DescriptiveComplexity.Problems.Machine.Space`). Hardness is proved once,
for the *deterministic* problem, by the QBF-evaluating machine of
`DescriptiveComplexity.Problems.Machine.QsatInterp`, and travels to the
nondeterministic one along `DescriptiveComplexity.dtmAcceptSpace_fo_reduction_ntmAcceptSpace`
– hardness moves forward along reductions, which is why the deterministic
problem is the one to prove hard and why Savitch is never run on the machine
side. Both are therefore PSPACE-complete. -/

/-- **Space-bounded machine acceptance is PSPACE-complete**, deterministic
(`DescriptiveComplexity.dtmAcceptSpace_PSPACE_complete`) or not
(`DescriptiveComplexity.ntmAcceptSpace_PSPACE_complete`): the library's
logically defined PSPACE is the machine one. -/
theorem spaceMachines_PSPACE_complete :
    PSPACE.Complete DTMAcceptSpace ∧ PSPACE.Complete NTMAcceptSpace :=
  ⟨dtmAcceptSpace_PSPACE_complete, ntmAcceptSpace_PSPACE_complete⟩

/-- **Space-bounded machine acceptance reduces to QSAT**, the machine-side
reading of Savitch's theorem: the nondeterministic space-bounded run is
evaluated by a quantified Boolean formula, whose decision procedure is
deterministic. -/
theorem ntmAcceptSpace_reduces_to_qsat : Nonempty (NTMAcceptSpace ≤ʳᶠᵒ[≤] QSAT) :=
  qsat_PSPACE_hard QSAT ⟨(FOReduction.refl QSAT).toOrdered.toRel⟩ NTMAcceptSpace
    ntmAcceptSpace_sotcDefinable

end DescriptiveComplexity
