/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Lattice.Nat
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
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

namespace Lax895169Proofs.DescriptiveComplexity

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

/-- A monotone chain of subsets of a finite type plateaus within `Nat.card X`
steps. -/
theorem exists_succ_eq_of_monotone_subset {X : Type*} [Finite X] {c : ℕ → Set X}
    (hc : ∀ n, c n ⊆ c (n + 1)) : ∃ N ≤ Nat.card X, c (N + 1) = c N := by
  by_contra hcon
  push Not at hcon
  have hcard : ∀ N ≤ Nat.card X + 1, (c 0).ncard + N ≤ (c N).ncard := by
    intro N
    induction N with
    | zero => simp
    | succ N ihN =>
      intro hN
      have hssub : c N ⊂ c (N + 1) :=
        (hc N).ssubset_of_ne (Ne.symm (hcon N (by omega)))
      have h1 := ihN (by omega)
      have h2 := Set.ncard_lt_ncard hssub (Set.toFinite _)
      omega
  have h1 := hcard (Nat.card X + 1) le_rfl
  have h2 := Set.ncard_le_ncard (Set.subset_univ (c (Nat.card X + 1))) (Set.toFinite _)
  rw [Set.ncard_univ] at h2
  omega

end Lax895169Proofs.DescriptiveComplexity


