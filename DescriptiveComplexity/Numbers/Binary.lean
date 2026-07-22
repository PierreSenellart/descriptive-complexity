/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Hom.Set

/-!
# Binary representation of numbers in finite structures

Representation (C) of the design notes: a number carried by an instance is
encoded in binary by a set of *bit positions*, the positions being linearly
ordered elements of the structure. This is the honest encoding for problems
whose numbers must be exponential in the instance size (SubsetSum, Partition,
Knapsack…), where the unary representation of
`DescriptiveComplexity.Numbers.Unary` would change the complexity.

* `DescriptiveComplexity.posRank`: the rank of a position in the increasing enumeration
  (via `monoEquivOfFin`, so positions need not literally be `Fin m`);
* `DescriptiveComplexity.binValue b`: the number `∑ 2 ^ rank p` over set bits – the
  decoding function;
* `DescriptiveComplexity.binEncode k`: the canonical encoding, via `Nat.testBit`;
* round-trips `DescriptiveComplexity.binValue_binEncode` (for `k < 2 ^ #positions`) and
  `DescriptiveComplexity.testBit_binValue`;
* range bound `DescriptiveComplexity.binValue_lt_two_pow`;
* invariance under order-isomorphisms (`DescriptiveComplexity.binValue_orderIso`), which
  feeds `DecisionProblem.iso_invariant` proofs;
* the most-significant-differing-bit comparison
  `DescriptiveComplexity.binValue_lt_binValue_iff` – the Lean counterpart of the FO(≤)
  formula comparing two binary numbers.
-/

namespace DescriptiveComplexity

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

private theorem sum_bits_lt (m : ℕ) (c : ℕ → Bool) :
    (∑ i ∈ range m, if c i then 2 ^ i else 0) < 2 ^ m := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [sum_bits_factor]
    have h1 := ih fun i => c (i + 1)
    have h2 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
    split <;> omega

private theorem sum_bits_testBit (m : ℕ) (c : ℕ → Bool) (j : ℕ) :
    Nat.testBit (∑ i ∈ range m, if c i then 2 ^ i else 0) j =
      (decide (j < m) && c j) := by
  induction m generalizing c j with
  | zero => simp
  | succ m ih =>
    rw [sum_bits_factor]
    cases j with
    | zero =>
      rw [Nat.testBit_zero]
      have hmod : (2 * (∑ i ∈ range m, if c (i + 1) then 2 ^ i else 0) +
          (if c 0 then 1 else 0)) % 2 = if c 0 then 1 else 0 := by
        split <;> omega
      rw [hmod]
      cases c 0 <;> simp
    | succ j =>
      rw [Nat.testBit_add_one]
      have hdiv : (2 * (∑ i ∈ range m, if c (i + 1) then 2 ^ i else 0) +
          (if c 0 then 1 else 0)) / 2 = ∑ i ∈ range m, if c (i + 1) then 2 ^ i else 0 := by
        split <;> omega
      rw [hdiv, ih]
      simp [Nat.succ_lt_succ_iff]

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

theorem posRank_lt (p : P) : posRank P p < Fintype.card P :=
  ((monoEquivOfFin P rfl).symm p).2

theorem posRank_lt_posRank_iff {p q : P} : posRank P p < posRank P q ↔ p < q := by
  rw [posRank, posRank, ← Fin.lt_def, OrderIso.lt_iff_lt]

theorem posRank_injective : Function.Injective (posRank P) := by
  intro p q h
  exact (monoEquivOfFin P rfl).symm.injective (Fin.val_injective h)

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

theorem posBits_of_le (b : P → Prop) {i : ℕ} (h : Fintype.card P ≤ i) :
    posBits P b i = false := by
  simp only [posBits, decide_eq_false_iff_not]
  rintro ⟨p, hp, -⟩
  exact absurd (hp ▸ posRank_lt P p) (not_lt.mpr h)

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

/-- The decoded number is smaller than `2 ^ #positions`. -/
theorem binValue_lt_two_pow (b : P → Prop) : binValue P b < 2 ^ Fintype.card P := by
  rw [binValue_eq_sum_range]
  exact sum_bits_lt _ _

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

/-- The bits of the decoded number are the original set of positions. -/
theorem testBit_binValue (b : P → Prop) (p : P) :
    Nat.testBit (binValue P b) (posRank P p) = true ↔ b p := by
  rw [binValue_eq_sum_range, sum_bits_testBit]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [posBits_posRank]
  exact ⟨fun h => h.2, fun h => ⟨posRank_lt P p, h⟩⟩

/-- The decoded number is invariant under order-isomorphisms of the
positions. -/
theorem binValue_orderIso {Q : Type} [Fintype Q] [LinearOrder Q] (e : P ≃o Q)
    (b : Q → Prop) : binValue P (fun p => b (e p)) = binValue Q b := by
  classical
  have hcard : Fintype.card P = Fintype.card Q := Fintype.card_congr e.toEquiv
  have hrank : ∀ p : P, posRank Q (e p) = posRank P p := by
    intro p
    have h1 : (monoEquivOfFin P rfl).trans e =
        (Fin.castOrderIso hcard).trans (monoEquivOfFin Q rfl) := Subsingleton.elim _ _
    have h2 : e ((monoEquivOfFin P rfl) ((monoEquivOfFin P rfl).symm p)) =
        (monoEquivOfFin Q rfl) (Fin.castOrderIso hcard ((monoEquivOfFin P rfl).symm p)) :=
      congrFun (congrArg (fun f => (DFunLike.coe f)) h1) ((monoEquivOfFin P rfl).symm p)
    rw [OrderIso.apply_symm_apply] at h2
    rw [posRank, posRank, h2, OrderIso.symm_apply_apply]
    rfl
  rw [binValue, binValue, ← Equiv.sum_comp e.toEquiv
    fun q => if b q then 2 ^ posRank Q q else 0]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show posRank Q (e.toEquiv p) = posRank P p from hrank p]
  rfl

/-- `binValue` only depends on the extension of the bit predicate. -/
theorem binValue_congr {b b' : P → Prop} (h : ∀ p, b p ↔ b' p) :
    binValue P b = binValue P b' := by
  classical
  rw [binValue, binValue]
  exact Finset.sum_congr rfl fun p _ => by rw [if_congr (h p) rfl rfl]

/-- **Most-significant-bit comparison**: one binary number is smaller than
another iff at some position the first has bit `0` and the second bit `1`,
all higher positions agreeing. This is the Lean counterpart of the FO(≤)
formula comparing binary numbers. -/
theorem binValue_lt_binValue_iff (b b' : P → Prop) :
    binValue P b < binValue P b' ↔
      ∃ p, ¬b p ∧ b' p ∧ ∀ q, p < q → (b q ↔ b' q) := by
  classical
  have keybit : ∀ (c c' : P → Prop) (p : P), ¬c p → c' p →
      (∀ q, p < q → (c q ↔ c' q)) → binValue P c < binValue P c' := by
    intro c c' p hc hc' hab
    refine Nat.lt_of_testBit (posRank P p) ?_ ?_ ?_
    · exact Bool.eq_false_iff.mpr fun hh => hc ((testBit_binValue c p).mp hh)
    · exact (testBit_binValue c' p).mpr hc'
    · intro j hj
      rcases lt_or_ge j (Fintype.card P) with hjm | hjm
      · set q : P := monoEquivOfFin P rfl ⟨j, hjm⟩ with hq
        have hrank : posRank P q = j := by
          rw [hq, posRank, OrderIso.symm_apply_apply]
        have hpq : p < q := by
          rw [← posRank_lt_posRank_iff (P := P), hrank]
          exact hj
        rw [← hrank, Bool.eq_iff_iff, testBit_binValue, testBit_binValue]
        exact hab q hpq
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (binValue_lt_two_pow c)
            (Nat.pow_le_pow_right (by omega) hjm)),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (binValue_lt_two_pow c')
            (Nat.pow_le_pow_right (by omega) hjm))]
  constructor
  · intro h
    have hDne : (Finset.univ.filter fun p => ¬(b p ↔ b' p)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra hD'
      push Not at hD'
      exact absurd (binValue_congr fun p => hD' p (Finset.mem_univ p)) (ne_of_lt h)
    set p₀ := (Finset.univ.filter fun p => ¬(b p ↔ b' p)).max' hDne with hp₀
    have hd : ¬(b p₀ ↔ b' p₀) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hDne)).2
    have hab : ∀ q, p₀ < q → (b q ↔ b' q) := by
      intro q hq
      by_contra hq'
      exact absurd (Finset.le_max' _ q (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq'⟩))
        (not_le.mpr hq)
    by_cases hb : b p₀
    · have hb' : ¬b' p₀ := fun h' => hd ⟨fun _ => h', fun _ => hb⟩
      exact absurd (keybit b' b p₀ hb' hb fun q hq => (hab q hq).symm)
        (not_lt.mpr (le_of_lt h))
    · have hb' : b' p₀ := by
        by_contra h'
        exact hd ⟨fun hh => absurd hh hb, fun hh => absurd hh h'⟩
      exact ⟨p₀, hb, hb', hab⟩
  · rintro ⟨p, hb, hb', hab⟩
    exact keybit b b' p hb hb' hab

end DescriptiveComplexity
