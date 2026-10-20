/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Membership
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Program
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Tape
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Hardness
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Interp
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax564036Proofs.DescriptiveComplexity.FixedPoint
import Lax564036Proofs.DescriptiveComplexity.FixedPointHorn
import Mathlib.Data.Fintype.Lattice
import Lax564036Proofs.DescriptiveComplexity.OrderedComposition
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax564036Proofs.DescriptiveComplexity.SecondOrderPull
import Lax564036Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Lax564036Proofs.DescriptiveComplexity.Ordered
import Lax564036Proofs.DescriptiveComplexity.Padding
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat.TseitinFormulas
import Lax564036Proofs.DescriptiveComplexity.Vocabulary
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT)
end Lax564036Proofs.DescriptiveComplexity

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
`DescriptiveComplexity.SAT_complete_for_ntmAccept` states the same content with
the hardness half quantified over the class, which is SAT's NP-completeness for
the NP the *machine* defines and the form to compare with the mechanizations
that prove Cook–Levin over a machine model.

As with any complexity-theoretic statement, these results are about finite
structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

/-- Machine acceptance is NP-hard: SAT reduces to it by building the machine
`M_φ` inside the instance. -/
theorem ntmAccept_NP_hard : NP.Hard NTMAccept :=
  NP.hard_of_orderedReduction SatTM.sat_ordered_fo_reduction_ntmAccept sat_NP_hard

/-! ### The deterministic problem

The same bridge one level down, for `DescriptiveComplexity.DTMAccept`: membership –
a deterministic run is a least fixed point, proved in
`DescriptiveComplexity.Problems.Machine.Fixpoint` through the formalized FO(LFP) →
SO-Horn translation – and hardness by the unit-propagation machine of
`DescriptiveComplexity.Problems.Machine.HornHardness`, transcribed in
`DescriptiveComplexity.Problems.Machine.HornInterp`. Together they make deterministic
machine acceptance PTIME-complete, and the library's logically defined
polynomial time the machine one. -/

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

end Lax564036Proofs.DescriptiveComplexity


