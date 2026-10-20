/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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
# Reading a count off a digit

What a counting reduction with one oracle call needs of arithmetic: a sum of
powers `∑ i, B ^ m i` is a number in base `B` whose digit of rank `p` is the
number of indices `i` with `m i = p`, as long as each of those numbers is below
`B` (`DescriptiveComplexity.sum_pow_div_mod`). A gadget that multiplies the
solutions of weight `p` by `B ^ p` therefore lets a quotient and a remainder
count the solutions of one weight.

Also here: a finite set with `k` elements has `2 ^ k` subsets, stated for
predicates (`DescriptiveComplexity.card_subsets_eq_two_pow`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

/-- The sets of elements satisfying `p` are as many as two to the number of
such elements. -/
theorem card_subsets_eq_two_pow {α : Type} [Finite α] (p : α → Prop) :
    Nat.card {ν : α → Prop // ∀ x, ν x → p x} = 2 ^ Nat.card {x // p x} := by
  have e : {ν : α → Prop // ∀ x, ν x → p x} ≃ ({x // p x} → Prop) :=
    { toFun := fun ν x => ν.1 x.1
      invFun := fun μ => ⟨fun a => ∃ h : p a, μ ⟨a, h⟩, fun _ ⟨h, _⟩ => h⟩
      left_inv := fun ν => Subtype.ext (funext fun a =>
        propext ⟨fun ⟨_, hν⟩ => hν, fun hν => ⟨ν.2 a hν, hν⟩⟩)
      right_inv := fun μ => funext fun x => propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩ }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_prop]

section Digits

variable {ι : Type} [Fintype ι] (m : ι → ℕ) {B : ℕ}

/-- The terms of exponent below `p` add up to less than `B ^ p`, when fewer
than `B` terms share each exponent. -/
theorem sum_pow_lt (hB : 0 < B)
    (h : ∀ q, (Finset.univ.filter fun i => m i = q).card < B) (p : ℕ) :
    (∑ i, if m i < p then B ^ m i else 0) < B ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hsplit : ∀ i, (if m i < p + 1 then B ^ m i else 0) =
        (if m i < p then B ^ m i else 0) + (if m i = p then B ^ p else 0) := by
      intro i
      rcases lt_trichotomy (m i) p with hi | hi | hi
      · simp [hi, Nat.lt_succ_of_lt hi, Nat.ne_of_lt hi]
      · simp [hi]
      · simp [Nat.not_lt_of_gt hi, Nat.ne_of_gt hi, Nat.not_lt.mpr (Nat.succ_le_of_lt hi)]
    have hmid : (∑ i, if m i = p then B ^ p else 0) =
        (Finset.univ.filter fun i => m i = p).card * B ^ p := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hmid, pow_succ]
    have hc := h p
    have hle : (Finset.univ.filter fun i => m i = p).card * B ^ p ≤ (B - 1) * B ^ p :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hc)
    have hBB : (B - 1) * B ^ p + B ^ p = B ^ p * B := by
      obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    omega

/-- **Digit extraction**: in the sum `∑ i, B ^ m i`, read in base `B`, the
digit of rank `p` is the number of indices of exponent `p`, when fewer than `B`
indices share each exponent. -/
theorem sum_pow_div_mod (hB : 0 < B)
    (h : ∀ q, (Finset.univ.filter fun i => m i = q).card < B) (p : ℕ) :
    (∑ i, B ^ m i) / B ^ p % B = (Finset.univ.filter fun i => m i = p).card := by
  have hsplit : ∀ i, B ^ m i =
      (if m i < p then B ^ m i else 0) +
        B ^ p * ((if m i = p then 1 else 0) +
          B * (if p < m i then B ^ (m i - (p + 1)) else 0)) := by
    intro i
    rcases lt_trichotomy (m i) p with hi | hi | hi
    · simp [hi, Nat.ne_of_lt hi, Nat.lt_asymm hi]
    · simp [hi]
    · have : B ^ m i = B ^ p * (B * B ^ (m i - (p + 1))) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      simp [hi, Nat.ne_of_gt hi, Nat.lt_asymm hi, this]
  have hmid : (∑ i, if m i = p then 1 else 0) = (Finset.univ.filter fun i => m i = p).card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, hmid,
    Nat.add_mul_div_left _ _ (Nat.pow_pos hB), Nat.div_eq_of_lt (sum_pow_lt m hB h p),
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h p)]

end Digits

end Lax794877Proofs.DescriptiveComplexity


