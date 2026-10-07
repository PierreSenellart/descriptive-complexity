/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Hom.Set
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
# Binary representation of numbers in finite structures

The binary encoding: a number carried by an instance is given by a set of
*bit positions*, the positions being linearly ordered elements of the
structure. This is the honest encoding for problems whose numbers must be
exponential in the instance size (SubsetSum, Partition, Knapsack…), where the
unary representation of `DescriptiveComplexity.Numbers.Unary` would change the
complexity.

* `DescriptiveComplexity.posRank`: the rank of a position in the increasing enumeration
  (via `monoEquivOfFin`, so positions need not literally be `Fin m`);
* `DescriptiveComplexity.binValue b`: the number `∑ 2 ^ rank p` over set bits – the
  decoding function;
* `DescriptiveComplexity.binEncode k`: the canonical encoding, via `Nat.testBit`;
* round-trips `DescriptiveComplexity.binValue_binEncode` (for `k < 2 ^ #positions`) and
  `DescriptiveComplexity.testBit_binValue`;
* range bound `DescriptiveComplexity.binValue_lt_two_pow`;
* invariance under order-isomorphisms (`DescriptiveComplexity.binValue_orderIso`), for
  the `DecisionProblem.iso_invariant` proof of a problem carrying binary
  numbers;
* the most-significant-differing-bit comparison
  `DescriptiveComplexity.binValue_lt_binValue_iff` – the Lean counterpart of the FO(≤)
  formula comparing two binary numbers.

The problems of the catalog reach this layer through
`DescriptiveComplexity.Numbers.BinRel`, which decodes the same bits when the
order on positions is a relation symbol of the vocabulary rather than a
`LinearOrder` instance: Knapsack, Partition, Job Sequencing and 0-1 Integer
Programming. The choice between this encoding and the unary one is argued in
`DescriptiveComplexity.Numbers`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open Finset

/-! ### Sums of powers of two over a bit predicate -/

section SumBits

private theorem sum_bits_factor (m : ℕ) (c : ℕ → Bool) :
    (∑ i ∈ range (m + 1), if c i then 2 ^ i else 0) =
      2 * (∑ i ∈ range m, if c (i + 1) then 2 ^ i else 0) + (if c 0 then 1 else 0) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> simp [pow_succ, Nat.mul_comm]

private theorem sum_bits_value (m k : ℕ) (h : k < 2 ^ m) :
    (∑ i ∈ range m, if Nat.testBit k i then 2 ^ i else 0) = k := by
  induction m generalizing k with
  | zero =>
    simp only [range_zero, Finset.sum_empty]
    omega
  | succ m ih =>
    rw [sum_bits_factor]
    simp only [Nat.testBit_add_one, Nat.testBit_zero]
    have h2 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
    have hk2 : k / 2 < 2 ^ m := by omega
    rw [ih (k / 2) hk2]
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm <;> simp [hm] <;> omega

end SumBits

/-! ### Positions, decoding and encoding -/

variable (P : Type) [Fintype P] [LinearOrder P]

/-- The rank of a bit position: its index in the increasing enumeration of
the positions. -/
noncomputable def posRank (p : P) : ℕ :=
  ((monoEquivOfFin P rfl).symm p : ℕ)

theorem posRank_injective : Function.Injective (posRank P) := by
  intro p q h
  exact (monoEquivOfFin P rfl).symm.injective (Fin.val_injective h)

/-- On `Fin m`, which is already the increasing enumeration of itself, the
rank of a position is its index. This is what lets a concrete encoder lay its
bit positions out as `Fin m` and read the place values off directly. -/
@[simp]
theorem posRank_fin {m : ℕ} (p : Fin m) : posRank (Fin m) p = (p : ℕ) := by
  simp [posRank]

open Classical in
/-- The number represented in binary by a set of positions: the sum of
`2 ^ rank` over the set bits. This is the decoding function of the binary
representation. -/
noncomputable def binValue (b : P → Prop) : ℕ :=
  ∑ p : P, if b p then 2 ^ posRank P p else 0

/-- The canonical binary encoding of a number as a set of positions. -/
def binEncode (k : ℕ) : P → Prop :=
  fun p => Nat.testBit k (posRank P p)

open Classical in
/-- The bits of a set of positions, as a function of the rank. -/
noncomputable def posBits (b : P → Prop) : ℕ → Bool :=
  fun i => decide (∃ p, posRank P p = i ∧ b p)

variable {P}

theorem posBits_posRank (b : P → Prop) (p : P) : posBits P b (posRank P p) = true ↔ b p := by
  simp only [posBits, decide_eq_true_eq]
  exact ⟨fun ⟨q, hq, hb⟩ => posRank_injective P hq ▸ hb, fun hb => ⟨p, rfl, hb⟩⟩

open Classical in
theorem binValue_eq_sum_range (b : P → Prop) :
    binValue P b = ∑ i ∈ range (Fintype.card P), if posBits P b i then 2 ^ i else 0 := by
  rw [← Fin.sum_univ_eq_sum_range, binValue,
    ← Equiv.sum_comp (monoEquivOfFin P rfl).toEquiv
      fun p => if b p then 2 ^ posRank P p else 0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrank : posRank P ((monoEquivOfFin P rfl).toEquiv i) = (i : ℕ) := by
    simp [posRank]
  have hbit : posBits P b (i : ℕ) = true ↔ b ((monoEquivOfFin P rfl).toEquiv i) := by
    rw [← hrank, posBits_posRank]
  rw [hrank]
  cases hb : posBits P b (i : ℕ) with
  | false =>
    rw [if_neg fun hh => absurd (hbit.mpr hh) (by simp [hb]), if_neg (by simp)]
  | true => rw [if_pos (hbit.mp hb), if_pos rfl]

/-- Decoding after encoding is the identity, for numbers within range. -/
theorem binValue_binEncode {k : ℕ} (h : k < 2 ^ Fintype.card P) :
    binValue P (binEncode P k) = k := by
  conv_rhs => rw [← sum_bits_value (Fintype.card P) k h]
  rw [binValue_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hbits : posBits P (binEncode P k) i = Nat.testBit k i := by
    rw [Bool.eq_iff_iff]
    simp only [posBits, decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, hb⟩
      rw [← hp]
      exact hb
    · intro hb
      refine ⟨monoEquivOfFin P rfl ⟨i, hi⟩, by simp [posRank], ?_⟩
      change Nat.testBit k (posRank P (monoEquivOfFin P rfl ⟨i, hi⟩)) = true
      rw [show posRank P (monoEquivOfFin P rfl ⟨i, hi⟩) = i by simp [posRank]]
      exact hb
  rw [hbits]

end Lax794877Proofs.DescriptiveComplexity


