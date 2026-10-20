/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Lattice.Nat
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Orbits of a self-map on a finite type

The quantitative facts every fixed-point iteration in this library rests on,
stated for a bare self-map `f : α → α` with no logic in sight:

* once an orbit plateaus it is constant
  (`DescriptiveComplexity.iterate_eq_of_isFixedPt`);
* an orbit on a finite type repeats within `Nat.card α` steps
  (`DescriptiveComplexity.exists_iterate_eq_of_finite`), so if it ever reaches
  a fixed point, the `Nat.card α`-th iterate already is one
  (`DescriptiveComplexity.isFixedPt_iterate_card_iff`) – the pigeonhole behind
  the partial fixed-point semantics;
* an *inflationary* map on the subsets of a finite type reaches a fixed point
  within `Nat.card X` steps – the height of the subset lattice, not its size
  (`DescriptiveComplexity.isFixedPt_iterate_card_of_subset`), via the plateau
  of any monotone chain of subsets
  (`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, with the dual
  `DescriptiveComplexity.exists_succ_eq_of_antitone_subset` for descending
  refinement chains).

Consumers: the stages of `DescriptiveComplexity.derivesIn`
(`DescriptiveComplexity.FixedPoint`), the inflationary and partial iterations of
`DescriptiveComplexity.StepDef` (`DescriptiveComplexity.FixedPointStep`), and any
future exponential iteration (SO(LFP), SO(PFP)). Everything is stated over an
arbitrary starting point, so ascending chains from `⊥` and descending chains
from `⊤` are both instances.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open Function (IsFixedPt)

variable {α : Type*} {f : α → α}

/-! ### Constancy from a plateau -/

/-- Once an orbit reaches a fixed point, it stays there: the orbit is constant
from any index whose value is a fixed point. -/
theorem iterate_eq_of_isFixedPt {a : α} {N : ℕ} (h : IsFixedPt f (f^[N] a)) {n : ℕ}
    (hn : N ≤ n) : f^[n] a = f^[N] a := by
  conv_lhs => rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  exact h.iterate (n - N)

/-! ### Pigeonhole: repeats and eventual periodicity -/

/-! ### Monotone chains of subsets plateau within the cardinality

The bound here is `Nat.card X` – the height of the subset lattice – rather
than the `2 ^ Nat.card X` states a bare pigeonhole would give. -/

end Lax822549Proofs.DescriptiveComplexity


