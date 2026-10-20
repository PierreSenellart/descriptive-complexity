/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Problems.TwoSat.Defs
import Lax480241Proofs.DescriptiveComplexity.Problems.TwoSat.Membership
import Lax480241Proofs.DescriptiveComplexity.Problems.TwoSat.Hardness
import Lax480241Proofs.DescriptiveComplexity.Problems.TwoSat.Ptime
import Lax480241Proofs.DescriptiveComplexity.Problems.HornSat
import Mathlib.Data.Finite.Sigma
import Lax480241Proofs.DescriptiveComplexity.ClauseDischarge
import Lax480241Proofs.DescriptiveComplexity.Complexity
import Lax480241Proofs.DescriptiveComplexity.InductiveCounting.Order
import Lax480241Proofs.DescriptiveComplexity.LogSpace
import Lax480241Proofs.DescriptiveComplexity.Ordered
import Lax480241Proofs.DescriptiveComplexity.OrderedComposition
import Lax480241Proofs.DescriptiveComplexity.Problems.Reachability
import Lax480241Proofs.DescriptiveComplexity.SecondOrderKrom
import Lax480241Proofs.DescriptiveComplexity.SecondOrderPull
import Lax480241Proofs.DescriptiveComplexity.TwoCnf
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
# 2SAT is NL-complete

The width-two restriction of SAT (`DescriptiveComplexity.TwoSAT`) is complete for
`DescriptiveComplexity.NL`, the class defined by the Krom fragment of existential
second-order logic (`DescriptiveComplexity.SigmaSOKromDefinable`). This is the NL-level
analogue of HORN-SAT for PTIME and of SAT for NP, and like them it is
machine-free: both halves are first-order constructions over the fragment that
*defines* the class.

* Membership (`DescriptiveComplexity.twoSat_mem_NL`,
  `DescriptiveComplexity.Problems.TwoSat.Membership`): a Krom program that guesses the
  truth assignment and reads each input clause through a covering pair of
  occurrences. The width promise of 2SAT and the absence of an empty clause are
  enforced by *guards*, which are first-order over the input vocabulary – a
  promise costs one goal clause and no second-order machinery.
* Hardness (`DescriptiveComplexity.twoSat_hard_of_sigmaSOKromDefinable`,
  `DescriptiveComplexity.Problems.TwoSat.Hardness`): the Krom discharge, emitting one
  propositional 2-clause per clause of the program and per instantiation of its
  universally quantified variables satisfying its guard. The output is
  width-two by construction, exactly as the Horn discharge's output is Horn.

One thing is deliberately *not* claimed, as for HORN-SAT: **Grädel's capture
theorem against machines is not formalized.** That SO-Krom captures
nondeterministic logarithmic space on ordered structures ([Grädel
1992][gradel1992capturing]) has a direction that simulates a machine, and lies
outside a machine-model-free library; note also that its *easy* direction, `2SAT
∈ NL`, already needs Immerman–Szelepcsényi, since 2-satisfiability is the
complement of a reachability condition on the implication graph. So
`DescriptiveComplexity.NL` is *defined* as SO-Krom definability, exactly as
`DescriptiveComplexity.PTIME` is defined as SO-Horn definability.

Completeness is also what places NL inside the classes above it. Neither
inclusion is syntactic – a Krom kernel is not a Horn kernel – so both go through
this problem: 2SAT is in PTIME by the Horn program of
`DescriptiveComplexity.Problems.TwoSat.Ptime`, which guesses reachability in the
implication graph, whence `DescriptiveComplexity.NL_subset_PTIME` and, composing with
`DescriptiveComplexity.PTIME_subset_NP`, `DescriptiveComplexity.NL_subset_NP`. The
logarithmic-space class below inherits both
(`DescriptiveComplexity.LOGSPACE_subset_PTIME`, `DescriptiveComplexity.LOGSPACE_subset_NP`),
its own inclusion in NL being immediate.
-/

namespace Lax480241Proofs.DescriptiveComplexity

/-- **NL ⊆ PTIME**: every SO-Krom definable problem reduces to 2SAT, which is in
PTIME by the Horn program for its implication graph. The inclusion has no
syntactic route – a Krom kernel is not a Horn kernel – so it goes through the
complete problem, exactly as `DescriptiveComplexity.PTIME_subset_NP` goes through
HORN-SAT. -/
theorem NL_subset_PTIME : NL ⊆ PTIME := by
  intro L _ P hP
  obtain ⟨f⟩ := twoSat_hard_of_sigmaSOKromDefinable P hP
  exact PTIME.mem_of_orderedReduction f twoSat_mem_PTIME

end Lax480241Proofs.DescriptiveComplexity


