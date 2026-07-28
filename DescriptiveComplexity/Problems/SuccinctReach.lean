/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SuccinctReach.Defs
import DescriptiveComplexity.Problems.SuccinctReach.Membership
import DescriptiveComplexity.Problems.SuccinctReach.Double
import DescriptiveComplexity.Problems.SuccinctReach.Hardness

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

namespace DescriptiveComplexity

/-- **SUCCINCT-REACH is in PSPACE**: the walk on states of the described
transition system is an SO(TC) walk. -/
theorem succinctReach_PSPACE_mem : SUCCINCTREACH ∈ PSPACE :=
  succinctReach_mem_PSPACE

/-- **SUCCINCT-REACH is PSPACE-hard.** -/
theorem succinctReach_PSPACE_hard : PSPACE.Hard SUCCINCTREACH :=
  SUCCINCTREACH_PSPACE_complete.hard

end DescriptiveComplexity
