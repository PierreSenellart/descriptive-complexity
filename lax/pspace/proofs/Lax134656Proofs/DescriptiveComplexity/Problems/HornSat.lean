/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat.Defs
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat.Membership
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Lax134656Proofs.DescriptiveComplexity.OrderWalk
import Lax134656Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax134656Proofs.DescriptiveComplexity.FixedPoint
import Lax134656Proofs.DescriptiveComplexity.FixedPointHorn
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (LFPDefinable)
end Lax134656Proofs.DescriptiveComplexity

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

namespace Lax134656Proofs.DescriptiveComplexity

/-- **PTIME ⊆ NP**, i.e., `SigmaP 0 ⊆ SigmaP 1`: every SO-Horn definable problem
reduces to HORN-SAT, which is in NP. This is the level-0 case of
`DescriptiveComplexity.sigmaP_subset_sigmaP_succ`; it lives here rather than with the
hierarchy because it goes through the Horn discharge, needing no separate
compilation of a Horn program into an existential second-order sentence. -/
theorem PTIME_subset_NP : PTIME ⊆ NP := by
  intro L _ P hP
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable P hP
  exact NP.mem_of_orderedReduction f hornSat_mem_NP

/-! ### Monotonicity of the hierarchy

`DescriptiveComplexity.sigmaP_subset_sigmaP_succ` climbs one level at a time and only
from level 1 up, its level-0 step being `DescriptiveComplexity.PTIME_subset_NP` above:
padding an existential second-order sentence with an unused block is not what
takes a Horn program to `Σ₁`. Assembling the two into the uniform statement
therefore has to happen here, downstream of the Horn discharge. -/

end Lax134656Proofs.DescriptiveComplexity


