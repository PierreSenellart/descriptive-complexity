/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Membership
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Program
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Tape
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Hardness
import Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Interp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Lax904597Proofs.DescriptiveComplexity.Hierarchy
import Lax904597Proofs.DescriptiveComplexity.OrderWalk
import Lax904597Proofs.DescriptiveComplexity.Padding
import Lax904597Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax904597Proofs.DescriptiveComplexity.SecondOrderHornPull
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Lax904597Proofs.DescriptiveComplexity.OrderedComposition
import Lax904597Proofs.DescriptiveComplexity.Problems.Sat
import Lax904597Proofs.DescriptiveComplexity.SecondOrder
import Lax904597Proofs.DescriptiveComplexity.Ordered
import Lax904597Proofs.DescriptiveComplexity.SecondOrderPull
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Lax904597Proofs.DescriptiveComplexity.Problems.Sat.TseitinFormulas
import Lax904597Proofs.DescriptiveComplexity.Vocabulary
import Lax904597Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Machine acceptance is NP-complete, and its deterministic restriction PTIME-complete

Umbrella file for `Lax904597Proofs.DescriptiveComplexity.NTMAccept`, the problem “does this
nondeterministic Turing machine accept its input within as many steps as there
are positions?”, with the machine carried by the instance.

The point of the problem is the machine bridge: every class
in this library is a definition in logic and every completeness theorem is
discharged by a first-order reduction, so that these classes really are *the*
NP and *the* P was, until this file, a citation. `NTMAccept` closes that gap
from inside the framework:

* **membership** (`Lax904597Proofs.DescriptiveComplexity.ntmAccept_mem_NP`,
  `Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Membership`) is Fagin's tableau argument – one
  existential block guesses the run, a first-order kernel checks it, and
  `Lax904597Proofs.DescriptiveComplexity.TMData.accepts_iff_exists_walk` turns an `ℕ`-indexed run into
  one indexed by the position elements, which is where the unary time bound is
  cashed in;
* **hardness** (`Lax904597Proofs.DescriptiveComplexity.ntmAccept_NP_hard`) is the reduction
  `SAT ≤ᶠᵒ[≤] NTMAccept`: a bespoke machine – guess an assignment in one sweep,
  check one clause per sweep, alternating direction – built *semantically* in
  `Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Hardness` on the tape of
  `Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Tape`, run by the phase machinery of
  `Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Program`, and transcribed into defining
  formulas in `Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Interp`.

Two consequences are worth naming. `Lax904597Proofs.DescriptiveComplexity.mem_NP_iff_le_ntmAccept` is
the machine characterization of the class: a problem is in NP – that is,
`Σ₁`-definable – exactly when it ordered-FO-reduces to machine acceptance.
And `Lax904597Proofs.DescriptiveComplexity.ntmAccept_reduces_to_sat` is the *textbook form* of the
Cook–Levin theorem – machine acceptance reduces to satisfiability – obtained
from the machine-free Tseitin discharge with no tableau-to-CNF encoding: the
membership proof already wrote the run as a `Σ₁` formula, and the generic
reduction to SAT applies to it like to any other. Conjoined with the hardness
direction, this gives `Lax904597Proofs.DescriptiveComplexity.ntmAccept_interreducible_sat` –
machine acceptance and satisfiability reduce to each other – the most faithful
representation of the Cook–Levin theorem this library offers.
`Lax904597Proofs.DescriptiveComplexity.SAT_complete_for_ntmAccept` states the same content with
the hardness half quantified over the class, which is SAT's NP-completeness for
the NP the *machine* defines and the form to compare with the mechanizations
that prove Cook–Levin over a machine model.

As with any complexity-theoretic statement, these results are about finite
structures only
(`Lax904597Proofs.DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace Lax904597Proofs.DescriptiveComplexity

open FirstOrder

/-- **The machine characterization of NP**: a problem is `Σ₁`-definable exactly
when it ordered-FO-reduces to machine acceptance. Forward through SAT – the
generic Tseitin discharge followed by the machine of a CNF formula – and
backward because membership travels along reductions. -/
theorem mem_NP_iff_le_ntmAccept {L : Language.{0, 0}} [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ NP ↔ Nonempty (P ≤ᶠᵒ[≤] NTMAccept) := by
  constructor
  · intro hP
    obtain ⟨g⟩ := sat_hard_of_sigmaSODefinable P hP
    exact ⟨g.trans SatTM.sat_ordered_fo_reduction_ntmAccept⟩
  · rintro ⟨f⟩
    exact NP.mem_of_orderedReduction f ntmAccept_mem_NP

/-- **`Lax904597Proofs.DescriptiveComplexity.SAT` is NP-complete, `NP` read as the machine
class**: satisfiability is accepted by a machine, and *every* problem accepted
by one reduces to it.

This is `ntmAccept_interreducible_sat` with the hardness half quantified over
the class rather than stated at one problem, which is the form the mechanized
Cook–Levin literature proves; it is the statement to compare against, since
nothing here is definitional about the logically defined
`Lax904597Proofs.DescriptiveComplexity.NP` – the class it is complete for is the one the
machine defines. The extra content over the interreducible form is exactly the
cofinal quantifier: `Lax904597Proofs.DescriptiveComplexity.mem_NP_iff_le_ntmAccept` turns an
arbitrary problem accepted by a machine into a `Σ₁` definition, which the
generic discharge then sends to `Lax904597Proofs.DescriptiveComplexity.SAT`. -/
theorem SAT_complete_for_ntmAccept :
    Nonempty (Lax904597.Sat.SAT ≤ᶠᵒ[≤] NTMAccept) ∧
      ∀ {L : Language.{0, 0}} [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L),
        Nonempty (P ≤ᶠᵒ[≤] NTMAccept) → Nonempty (P ≤ᶠᵒ[≤] Lax904597.Sat.SAT) :=
  ⟨⟨SatTM.sat_ordered_fo_reduction_ntmAccept⟩,
    fun P h => sat_hard_of_sigmaSODefinable P ((mem_NP_iff_le_ntmAccept P).mpr h)⟩

/-! ### The deterministic problem

The same bridge one level down, for `Lax904597Proofs.DescriptiveComplexity.DTMAccept`: membership –
a deterministic run is a least fixed point, proved in
`Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Fixpoint` through the formalized FO(LFP) →
SO-Horn translation – and hardness by the unit-propagation machine of
`Lax904597Proofs.DescriptiveComplexity.Problems.Machine.HornHardness`, transcribed in
`Lax904597Proofs.DescriptiveComplexity.Problems.Machine.HornInterp`. Together they make deterministic
machine acceptance PTIME-complete, and the library's logically defined
polynomial time the machine one. -/

/-! ### The space-bounded problems

Drop the step bound and the same machines measure *space* instead of time: a
run of `Lax904597Proofs.DescriptiveComplexity.NTMAcceptSpace` may be arbitrarily long, but it
never leaves the positions of the instance, so its configurations are the
assignments of a fixed second-order block and its runs are a transitive closure
over them. That is exactly an SO(TC) specification, so both problems are in
PSPACE (`Lax904597Proofs.DescriptiveComplexity.Problems.Machine.Space`). Hardness is proved once,
for the *deterministic* problem, by the QBF-evaluating machine of
`Lax904597Proofs.DescriptiveComplexity.Problems.Machine.QsatInterp`, and travels to the
nondeterministic one along `Lax904597Proofs.DescriptiveComplexity.dtmAcceptSpace_fo_reduction_ntmAcceptSpace`
– hardness moves forward along reductions, which is why the deterministic
problem is the one to prove hard and why Savitch is never run on the machine
side. Both are therefore PSPACE-complete. -/

end Lax904597Proofs.DescriptiveComplexity


