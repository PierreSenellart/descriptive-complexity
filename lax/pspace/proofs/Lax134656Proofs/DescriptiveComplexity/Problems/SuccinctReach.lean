/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach.Defs
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach.Membership
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach.Double
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach.Hardness
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

/-!
# SUCCINCT-REACH: reachability in a propositionally described transition system

Umbrella file for `DescriptiveComplexity.SUCCINCTREACH`, the canonical complete
problem for `DescriptiveComplexity.PSPACE`: given three CNF formulas describing
the transitions, the source states and the target states of a system whose
states are the truth assignments to a set of marked *state variables*, is a
target state reachable from a source state? The described graph has
exponentially many vertices, which is why walking it is a polynomial-*space*
and not a polynomial-*time* question. The same problem is propositional STRIPS
plan existence, and the reachability query of symbolic model checking.

* `DescriptiveComplexity.Problems.SuccinctReach.Defs`: the vocabulary
  `FirstOrder.Language.transSys`, the semantics
  (`DescriptiveComplexity.StepRel`, `DescriptiveComplexity.IsStart`,
  `DescriptiveComplexity.IsGoal`, `DescriptiveComplexity.SuccinctReachable`), its
  isomorphism-invariance, and the bundled problem
  `DescriptiveComplexity.SUCCINCTREACH`.
* `DescriptiveComplexity.Problems.SuccinctReach.Membership`: the membership half,
  `DescriptiveComplexity.succinctReach_mem_PSPACE`, by the SO(TC) specification
  `DescriptiveComplexity.srSpec` whose states carry the state being walked together
  with the three existential witnesses a transitive closure cannot quantify on
  its own.
* `DescriptiveComplexity.Problems.SuccinctReach.Double`: the doubled block and the
  language renamings that put a transition sentence over two block copies and
  two endpoint sentences over one on the same footing.
* `DescriptiveComplexity.Problems.SuccinctReach.Hardness`: the hardness half,
  `DescriptiveComplexity.succinctReach_hard_of_sotcDefinable`, the Tseitin discharge
  ([Tseitin 1968][tseitin1968complexity]) of an SO(TC) specification.

## The shape of the discharge

The two halves are the two readings of the same identification, and they mirror
the Cook–Levin pair for `∃SO` and SAT exactly:

* *membership* reads a transition system as an SO(TC) walk – a state is a
  monadic relation variable, a transition is a first-order condition on two
  consecutive states;
* *hardness* reads an SO(TC) walk as a transition system, by Tseitin-encoding
  the three sentences of a `DescriptiveComplexity.SOTCSpec` into three clause
  groups. The semantic core of the SAT discharge
  (`DescriptiveComplexity.Tseitin.satCond_iff_gates` and the gate-correctness
  lemmas) is reused unchanged; what is new is that the three encodings are
  taken over the **doubled** block, so that the propositional variables
  standing for the atoms of the block are the *same elements* in all three –
  they are exactly the state variables the walk carries, their second copies
  the next-state copies.

Because a state of the interpreted system is an assignment of the block and
nothing else, the two walks correspond step by step, with no initialization or
finalization steps to peel off; that is why the endpoint conditions stay two
extra clause groups rather than being folded into the transition.
-/

namespace Lax134656Proofs.DescriptiveComplexity

/-- **SUCCINCT-REACH is PSPACE-hard.** -/
theorem succinctReach_PSPACE_hard : PSPACE.Hard SUCCINCTREACH :=
  SUCCINCTREACH_PSPACE_complete.hard

end Lax134656Proofs.DescriptiveComplexity


