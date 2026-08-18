/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Lattice
import DescriptiveComplexity.LogTime.Definable

/-!
# The bit layer of a finite ordered universe

An element of a finite linearly ordered universe *is* a number, its rank; this
file gives access to that number **one bit at a time**, in the two ways a bit
position can be named, and relates them.

## Two namings, and what each is for

A bit position can be named by its **index** `i`, or by its **place value**, the
element `p` whose rank is `2 ^ i`. Both appear here, and neither is a variant of
the other:

* `DescriptiveComplexity.BitIx` is the index naming – `BIT(x, i)`, the primitive
  of the classical vocabulary `FO(≤, BIT)`. It is total, needs no guard, and its
  bookkeeping is the arithmetic of the universe: the next position is `i + 1`,
  and “the bit `k` positions up” is an addition. It is what the logic and the
  machine model of `DescriptiveComplexity.LogTime` are built on, because reading
  a bit at a *guessed* index is the random access those machines have.
* `DescriptiveComplexity.BitAt` is the place-value naming, and it is what makes
  a bit first-order in `FO(≤, +, ×)` (`DescriptiveComplexity.arithDef_bit`): the
  bit of `x` at place value `p` is a division with remainder, `x = u + v` with
  `2p ∣ u` and `p ≤ v < 2p`, all three of whose witnesses are below `x`, hence
  are ranks of the universe and are not lost to truncation. Being a place value
  is itself first-order – `orank p ≠ 0` together with “every divisor is `1` or
  even” (`DescriptiveComplexity.isPos_iff_forall_dvd`).

`DescriptiveComplexity.bitIx_iff_bitAt` is the bridge, and it is one
existential: `BitIx i x` is `BitAt p x` at the `p` of rank `2 ^ i`. What that
existential costs is the *definability of the graph of* `i ↦ 2 ^ i`
(`DescriptiveComplexity.PowArithDef`) – [Immerman 1999][immerman1999descriptive]
Thm 1.17(2), and the single lemma on which the translation of the machine's
logic into `FO(≤, +, ×)` rests. It is a named statement rather than an
assumption, and it is proved: `DescriptiveComplexity.powArithDef`
(`LogTime/Pow.lean`); see `DescriptiveComplexity.LogTime`.

The number of positions is `Nat.clog 2 (Nat.card A)`
(`DescriptiveComplexity.posCount`), and the ranks are exactly the numbers whose
bits live in that range; the top index is
`DescriptiveComplexity.IsTopIx`, read off the bits of the greatest element and
so needing no arithmetic on exponents.

## What a bit vector can hold

A single element holds one bit per position, so it can carry a whole
`Bool`-valued function of the positions – provided the value stays below the
size of the universe. That is the reason for
`DescriptiveComplexity.exists_orank_testBit`, stated with an explicit bit
budget: below `posCount A` a bit vector is *not* in general a rank (the universe
need not have a power of two elements), below `posCount A - 1` it always is.
That one-position gap is what forces the sweep simulation of
`DescriptiveComplexity.LogTime` to carry the state of its last step separately,
and it is the only place the arithmetic of the layer is not uniform.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Bits of a natural number -/

section NatBits

/-- **A bit is a comparison of the remainder**: the bit of `x` at place value
`2 ^ i` is set exactly when `x` is at least `2 ^ i` modulo `2 ^ (i + 1)`. -/
theorem testBit_iff_two_pow_le_mod (x i : ℕ) :
    x.testBit i = true ↔ 2 ^ i ≤ x % 2 ^ (i + 1) := by
  have h2 : (0 : ℕ) < 2 ^ i := Nat.two_pow_pos i
  have key : x % 2 ^ (i + 1) / 2 ^ i = x / 2 ^ i % 2 := by
    rw [pow_succ]
    exact Nat.mod_mul_right_div_self x (2 ^ i) 2
  have hlt : x % 2 ^ (i + 1) < 2 ^ (i + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  rw [← key]
  constructor
  · intro h
    exact (Nat.one_le_div_iff h2).mp (by omega)
  · intro h
    have h1 : 1 ≤ x % 2 ^ (i + 1) / 2 ^ i := (Nat.one_le_div_iff h2).mpr h
    have h2' : x % 2 ^ (i + 1) / 2 ^ i < 2 := by
      rw [Nat.div_lt_iff_lt_mul h2]
      rw [pow_succ] at hlt
      omega
    omega

/-- **A bit is a splitting**: the bit of `x` at place value `2 ^ i` is set
exactly when `x` splits as a multiple of `2 ^ (i + 1)` plus a remainder between
`2 ^ i` and `2 ^ (i + 1)`. Every witness is at most `x`, which is what makes the
statement survive the truncation of a finite universe. -/
theorem testBit_iff_exists_split (x i : ℕ) :
    x.testBit i = true ↔
      ∃ u v : ℕ, u + v = x ∧ 2 ^ i ≤ v ∧ v < 2 ^ (i + 1) ∧ 2 ^ (i + 1) ∣ u := by
  rw [testBit_iff_two_pow_le_mod]
  constructor
  · intro h
    refine ⟨x / 2 ^ (i + 1) * 2 ^ (i + 1), x % 2 ^ (i + 1), ?_, h,
      Nat.mod_lt _ (Nat.two_pow_pos _), ⟨x / 2 ^ (i + 1), by ring⟩⟩
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x _
  · rintro ⟨u, v, hsum, hv1, hv2, m, rfl⟩
    have : (2 ^ (i + 1) * m + v) % 2 ^ (i + 1) = v := by
      rw [Nat.mul_comm, Nat.mul_add_mod', Nat.mod_eq_of_lt hv2]
    rw [← hsum, this]
    exact hv1

/-- Below `2 ^ (i + 1)` a bit is just a comparison: the truncated case, where
the doubling of the place value has overflowed the universe. -/
theorem testBit_iff_le_of_lt {x i : ℕ} (h : x < 2 ^ (i + 1)) :
    x.testBit i = true ↔ 2 ^ i ≤ x := by
  rw [testBit_iff_two_pow_le_mod, Nat.mod_eq_of_lt h]

/-- **Powers of two, by their divisors**: a nonzero number all of whose divisors
are `1` or even is a power of two. This is the first-order reading of “`p` is a
position”, and it needs no primality. -/
theorem eq_two_pow_of_forall_dvd :
    ∀ p : ℕ, p ≠ 0 → (∀ d, d ∣ p → d = 1 ∨ 2 ∣ d) → ∃ i, p = 2 ^ i := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro hp h
    rcases eq_or_ne p 1 with rfl | hne
    · exact ⟨0, rfl⟩
    · obtain ⟨m, rfl⟩ : 2 ∣ p := (h p dvd_rfl).resolve_left hne
      have hm : m ≠ 0 := by rintro rfl; simp at hp
      obtain ⟨i, hi⟩ := IH m (by omega) hm fun d hd => h d (hd.mul_left 2)
      exact ⟨i + 1, by rw [hi, pow_succ, Nat.mul_comm]⟩

/-- The converse: every divisor of a power of two is `1` or even. -/
theorem forall_dvd_of_eq_two_pow {p : ℕ} {i : ℕ} (hp : p = 2 ^ i) :
    ∀ d, d ∣ p → d = 1 ∨ 2 ∣ d := by
  subst hp
  intro d hd
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases j with
  | zero => exact Or.inl rfl
  | succ j => exact Or.inr ⟨2 ^ j, by rw [pow_succ, Nat.mul_comm]⟩

/-- The value of a finite bit vector, as a sum of place values. -/
noncomputable def bitsVal (b : ℕ → Bool) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, if b i then 2 ^ i else 0

/-- Peeling the top bit of a finite bit vector. -/
theorem bitsVal_succ (b : ℕ → Bool) (m : ℕ) :
    bitsVal b (m + 1) = bitsVal b m + (if b m then 2 ^ m else 0) := by
  rw [bitsVal, Finset.sum_range_succ, ← bitsVal]

theorem bitsVal_lt (b : ℕ → Bool) (m : ℕ) : bitsVal b m < 2 ^ m := by
  induction m with
  | zero => simp [bitsVal]
  | succ m ih =>
    rw [bitsVal_succ, pow_succ]
    split <;> omega

theorem testBit_bitsVal (b : ℕ → Bool) (m : ℕ) {i : ℕ} (hi : i < m) :
    (bitsVal b m).testBit i = b i := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hb : bitsVal b m < 2 ^ m := bitsVal_lt b m
    rw [bitsVal_succ]
    rcases Nat.lt_or_ge i m with hlt | hge
    · cases hbm : b m with
      | false => rw [if_neg (by simp), Nat.add_zero]; exact ih hlt
      | true =>
        rw [if_pos (by simp), Nat.add_comm, Nat.testBit_two_pow_add_gt hlt]
        exact ih hlt
    · have him : i = m := by omega
      subst him
      cases hbm : b i with
      | false =>
        rw [if_neg (by simp), Nat.add_zero]
        exact Nat.testBit_lt_two_pow hb
      | true =>
        rw [if_pos (by simp), Nat.add_comm, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow hb]
        rfl

end NatBits

/-! ### Positions of a finite ordered universe -/

section Positions

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The number of bit positions** of the ranks of `A`: the ranks are the
numbers below `Nat.card A`, so they are exactly the numbers whose bits live
below `Nat.clog 2 (Nat.card A)`. -/
noncomputable def posCount (A : Type) [LinearOrder A] [Finite A] : ℕ :=
  Nat.clog 2 (Nat.card A)

/-- A place value is that of a position exactly when it is a rank. -/
theorem two_pow_lt_card_iff_lt_posCount (i : ℕ) :
    2 ^ i < Nat.card A ↔ i < posCount A :=
  (Nat.lt_clog_iff_pow_lt (by norm_num)).symm

/-- Above the positions, every rank has a zero bit. -/
theorem testBit_orank_eq_false {x : A} {i : ℕ} (hi : posCount A ≤ i) :
    (orank x).testBit i = false := by
  refine Nat.testBit_lt_two_pow (lt_of_lt_of_le (orank_lt_card x) ?_)
  exact le_trans (Nat.le_pow_clog (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) hi)

/-- `p` is a **position**: its rank is a place value `2 ^ i`. The element *is*
the place value; the exponent never appears in a formula. -/
def IsPos (p : A) : Prop := ∃ i : ℕ, orank p = 2 ^ i

/-- The exponent of a position. -/
noncomputable def posExp (p : A) : ℕ := Nat.log 2 (orank p)

omit [Finite A] in
theorem posExp_eq {p : A} {i : ℕ} (h : orank p = 2 ^ i) : posExp p = i := by
  rw [posExp, h, Nat.log_pow (by norm_num)]

omit [Finite A] in
theorem orank_eq_two_pow_posExp {p : A} (h : IsPos p) : orank p = 2 ^ posExp p := by
  obtain ⟨i, hi⟩ := h
  rw [posExp_eq hi, hi]

/-- Every exponent in range is the exponent of a position. -/
theorem exists_isPos {i : ℕ} (hi : i < posCount A) : ∃ p : A, orank p = 2 ^ i :=
  exists_orank_eq (two_pow_lt_card_iff_lt_posCount i |>.mpr hi)

/-- **Being a position is first-order**: a nonzero rank all of whose divisors
are `1` or even, with every divisor and cofactor a rank of the universe – which
they are, being at most `orank p`. -/
theorem isPos_iff_forall_dvd (p : A) :
    IsPos p ↔ orank p ≠ 0 ∧ ∀ d : A, (∃ w : A, orank w * orank d = orank p) →
      orank d = 1 ∨ ∃ e : A, orank e + orank e = orank d := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨by rw [hi]; positivity, fun d hd => ?_⟩
    obtain ⟨w, hw⟩ := hd
    have hdvd : orank d ∣ orank p := ⟨orank w, by rw [← hw]; ring⟩
    rcases forall_dvd_of_eq_two_pow hi _ hdvd with h1 | ⟨k, hk⟩
    · exact Or.inl h1
    · have hklt : k < Nat.card A := lt_of_le_of_lt (by omega) (orank_lt_card d)
      obtain ⟨e, he⟩ := exists_orank_eq (A := A) hklt
      exact Or.inr ⟨e, by rw [he, hk]; omega⟩
  · rintro ⟨hne, h⟩
    refine eq_two_pow_of_forall_dvd (orank p) hne fun d hd => ?_
    have hdle : d ≤ orank p := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd
    obtain ⟨dA, hdA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hdle (orank_lt_card p))
    obtain ⟨c, hc⟩ := hd
    have hcle : c ≤ orank p := by
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · simp only [Nat.zero_mul] at hc
        omega
      · have h1 : c ≤ d * c := Nat.le_mul_of_pos_left c hdpos
        omega
    obtain ⟨w, hwA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hcle (orank_lt_card p))
    rcases h dA ⟨w, by rw [hwA, hdA, hc]; ring⟩ with h1 | ⟨e, he⟩
    · exact Or.inl (by rw [← hdA]; exact h1)
    · exact Or.inr ⟨orank e, by rw [← hdA, ← he]; ring⟩

/-- **The bit budget of a trace**: a bit vector supported below the top position
is a rank, whatever the size of the universe. -/
theorem exists_orank_testBit [Nonempty A] (b : ℕ → Bool) :
    ∃ t : A, ∀ i, i + 1 < posCount A → (orank t).testBit i = b i := by
  rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
  · obtain ⟨t⟩ := ‹Nonempty A›
    exact ⟨t, fun i hi => by omega⟩
  · have hbound : 2 ^ (posCount A - 1) < Nat.card A := by
      rw [two_pow_lt_card_iff_lt_posCount]
      omega
    have hlt : bitsVal b (posCount A - 1) < Nat.card A :=
      lt_trans (bitsVal_lt b _) hbound
    obtain ⟨t, ht⟩ := exists_orank_eq (A := A) hlt
    exact ⟨t, fun i hi => by rw [ht]; exact testBit_bitsVal b _ (by omega)⟩

/-- **The same, with the top positions pinned to zero**: the element a bit
vector names carries *no* bit at the top position, which is what a construction
needs when it also has to say that nothing outside its layout is set. -/
theorem exists_orank_testBit' [Nonempty A] (b : ℕ → Bool) :
    ∃ t : A, (∀ i, i + 1 < posCount A → (orank t).testBit i = b i) ∧
      ∀ i, posCount A ≤ i + 1 → (orank t).testBit i = false := by
  rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
  · obtain ⟨t⟩ := ‹Nonempty A›
    have hcard : Nat.card A ≤ 1 := by
      by_contra hc
      have : (0 : ℕ) < posCount A := by
        rw [← two_pow_lt_card_iff_lt_posCount]
        simpa using by omega
      omega
    have h0t : orank t = 0 := by have := orank_lt_card t; omega
    exact ⟨t, fun i hi => by omega, fun i _ => by rw [h0t]; simp⟩
  · have hbound : 2 ^ (posCount A - 1) < Nat.card A := by
      rw [two_pow_lt_card_iff_lt_posCount]
      omega
    have hlt : bitsVal b (posCount A - 1) < Nat.card A :=
      lt_trans (bitsVal_lt b _) hbound
    obtain ⟨t, ht⟩ := exists_orank_eq (A := A) hlt
    refine ⟨t, fun i hi => by rw [ht]; exact testBit_bitsVal b _ (by omega), fun i hi => ?_⟩
    rw [ht]
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (bitsVal_lt b _) (Nat.pow_le_pow_right (by norm_num) (by omega)))

end Positions

/-! ### The bit of an element at a position -/

section BitAt

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The bit of `x` at the place value `p`**, first-order in `≤`, `+` and `×`:
either the doubling `q = p + p` exists, and then `x` splits as a multiple `u` of
`q` plus a remainder `v` with `p ≤ v < q`; or it does not, and then `x` is below
`2 p` already and the bit is the comparison `p ≤ x`. -/
def BitAt (p x : A) : Prop :=
  (∃ q u v w : A, orank p + orank p = orank q ∧ orank u + orank v = orank x ∧
      p ≤ v ∧ v < q ∧ orank w * orank q = orank u) ∨
    ((¬∃ q : A, orank p + orank p = orank q) ∧ p ≤ x)

/-- **`BitAt` is `BIT`**: at a position of place value `2 ^ i`, it is the `i`-th
bit of the rank. -/
theorem bitAt_iff {p x : A} {i : ℕ} (hp : orank p = 2 ^ i) :
    BitAt p x ↔ (orank x).testBit i = true := by
  by_cases hq : ∃ q : A, orank p + orank p = orank q
  · obtain ⟨q, hqe⟩ := hq
    have hq2 : orank q = 2 ^ (i + 1) := by rw [← hqe, hp, pow_succ]; ring
    constructor
    · rintro (⟨q', u, v, w, hq', hsum, hpv, hvq, hw⟩ | ⟨hno, -⟩)
      · have hq'e : orank q' = 2 ^ (i + 1) := by rw [← hq', hp, pow_succ]; ring
        refine (testBit_iff_exists_split (orank x) i).mpr ⟨orank u, orank v, hsum, ?_, ?_, ?_⟩
        · rw [← hp]; exact orank_le_iff.mpr hpv
        · rw [← hq'e]; exact orank_lt_orank hvq
        · exact ⟨orank w, by rw [← hq'e, ← hw]; ring⟩
      · exact absurd ⟨q, hqe⟩ hno
    · intro h
      obtain ⟨u, v, hsum, hu1, hu2, m, hm⟩ := (testBit_iff_exists_split (orank x) i).mp h
      have hule : u ≤ orank x := by omega
      have hvle : v ≤ orank x := by omega
      have hmle : m ≤ orank x := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · omega
        · have h1 : m ≤ 2 ^ (i + 1) * m := Nat.le_mul_of_pos_left m (Nat.two_pow_pos _)
          omega
      obtain ⟨uA, huA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hule (orank_lt_card x))
      obtain ⟨vA, hvA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hvle (orank_lt_card x))
      obtain ⟨mA, hmA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hmle (orank_lt_card x))
      refine Or.inl ⟨q, uA, vA, mA, hqe, by rw [huA, hvA]; exact hsum, ?_, ?_, ?_⟩
      · exact orank_le_iff.mp (by rw [hvA, hp]; exact hu1)
      · exact lt_of_not_ge fun hcon => by
          have := orank_le_iff.mpr hcon
          rw [hvA, hq2] at this
          omega
      · rw [hmA, huA, hq2, hm]; ring
  · have hxlt : orank x < 2 ^ (i + 1) := by
      rcases Nat.lt_or_ge (orank x) (2 ^ (i + 1)) with hlt | hge
      · exact hlt
      · exfalso
        have hcard : Nat.card A ≤ 2 ^ (i + 1) := by
          rcases Nat.lt_or_ge (2 ^ (i + 1)) (Nat.card A) with hlt' | hge'
          · obtain ⟨q, hqe⟩ := exists_orank_eq (A := A) hlt'
            exact absurd ⟨q, by rw [hqe, hp, pow_succ]; ring⟩ hq
          · exact hge'
        have := orank_lt_card x
        omega
    constructor
    · rintro (⟨q', -, -, -, hq', -, -, -, -⟩ | ⟨-, hpx⟩)
      · exact absurd ⟨q', hq'⟩ hq
      · rw [testBit_iff_le_of_lt hxlt, ← hp]
        exact orank_le_iff.mpr hpx
    · intro h
      rw [testBit_iff_le_of_lt hxlt, ← hp] at h
      exact Or.inr ⟨hq, orank_le_iff.mp h⟩

end BitAt

/-! ### The bit of an element at an index -/

section BitIx

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The bit of `x` at the index `i`**: the `BIT` of the classical vocabulary
`FO(≤, BIT)`, the position being named by the element whose *rank* is the
exponent. Total, and with no guard – above the bit positions of the universe
every bit is simply clear. -/
def BitIx (i x : A) : Prop := (orank x).testBit (orank i) = true

omit [Finite A] in
theorem bitIx_iff {i x : A} : BitIx i x ↔ (orank x).testBit (orank i) = true := Iff.rfl

/-- **A bit that is set is at a position of the universe.** -/
theorem orank_lt_posCount_of_bitIx {i x : A} (h : BitIx i x) : orank i < posCount A := by
  by_contra hcon
  rw [bitIx_iff, testBit_orank_eq_false (by omega)] at h
  exact Bool.noConfusion h

/-- A finite nonempty order has a greatest element – the one a formula reads
the top index off. -/
theorem exists_isMax (A : Type) [LinearOrder A] [Finite A] [Nonempty A] :
    ∃ m : A, ∀ k : A, k ≤ m := Finite.exists_max (fun a : A => a)

/-- **The two namings agree**: the bit at the index `i` is the bit at the place
value `2 ^ i`. The existential is the whole of the difference between the two
readings of `BIT`, and `DescriptiveComplexity.PowArithDef` is what it costs. -/
theorem bitIx_iff_bitAt {i x : A} :
    BitIx i x ↔ ∃ p : A, orank p = 2 ^ orank i ∧ BitAt p x := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_isPos (A := A) (orank_lt_posCount_of_bitIx h)
    exact ⟨p, hp, (bitAt_iff hp).mpr h⟩
  · rintro ⟨p, hp, hb⟩
    exact (bitAt_iff hp).mp hb

/-- `i` is the **top index**: the highest bit position of the universe. -/
def IsTopIx (i : A) : Prop := orank i + 1 = posCount A

/-- `i` is a **low index**: a bit position with a further one above it. What
separates the two is the budget of `DescriptiveComplexity.exists_orank_testBit`:
a guessed trace carries a bit at every low index, and the top one has to be
carried apart. -/
def IsLowIx (i : A) : Prop := orank i + 1 < posCount A

/-- **The greatest element has its highest bit at the top index**: `orank` of it
is `Nat.card A - 1`, which lies between `2 ^ (posCount A - 1)` and
`2 ^ posCount A`. This is what lets a formula find the end of the tape without
any arithmetic on exponents – it reads it off the bits of an element it
already has. -/
theorem bitIx_max_of_isTopIx {i m : A} (hm : ∀ k : A, k ≤ m) (h : IsTopIx i) :
    BitIx i m := by
  have hcard : 0 < Nat.card A := lt_of_le_of_lt (Nat.zero_le _) (orank_lt_card m)
  have hpos : 0 < posCount A := by rw [IsTopIx] at h; omega
  have hd : orank i = posCount A - 1 := by rw [IsTopIx] at h; omega
  have hsucc : posCount A - 1 + 1 = posCount A := by omega
  have hlt : 2 ^ (posCount A - 1) < Nat.card A :=
    (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
  have hle : Nat.card A ≤ 2 ^ posCount A := Nat.le_pow_clog (by norm_num) _
  rw [bitIx_iff, hd, orank_isTop hm, testBit_iff_le_of_lt
    (by rw [hsucc]; exact lt_of_lt_of_le (Nat.sub_lt hcard Nat.one_pos) hle)]
  exact Nat.le_sub_one_of_lt hlt

/-- Every index below the count is the rank of an element. -/
theorem lt_card_of_lt_posCount {d : ℕ} (h : d < posCount A) : d < Nat.card A :=
  lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_two_pow_self))
    ((two_pow_lt_card_iff_lt_posCount d).mpr h)

/-- **The count of positions is itself a rank**: there are never more bit
positions than elements, so a formula may quantify over an index one above the
top – which is what pins the absence of a carry out of the last position. -/
theorem posCount_lt_card [Nonempty A] : posCount A < Nat.card A := by
  rcases Nat.eq_zero_or_pos (posCount A) with h0 | hpos
  · rw [h0]
    exact Nat.card_pos
  · have h1 : 2 ^ (posCount A - 1) < Nat.card A :=
      (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
    have h2 : posCount A - 1 < 2 ^ (posCount A - 1) := Nat.lt_two_pow_self
    omega

/-- **The top index, read from the bits of the greatest element**: it is the
highest index carrying a bit there. -/
theorem isTopIx_iff_bits {i m : A} (hm : ∀ k : A, k ≤ m) :
    IsTopIx i ↔ (BitIx i m ∧ ∀ k : A, i < k → ¬ BitIx k m) := by
  constructor
  · intro h
    refine ⟨bitIx_max_of_isTopIx hm h, fun k hk hb => ?_⟩
    have h1 : orank i < orank k := orank_lt_orank hk
    have h2 := orank_lt_posCount_of_bitIx hb
    rw [IsTopIx] at h
    omega
  · rintro ⟨hb, hno⟩
    have h1 := orank_lt_posCount_of_bitIx hb
    by_contra hne
    have hlt : orank i + 1 < posCount A := by rw [IsTopIx] at hne; omega
    obtain ⟨t, ht⟩ := exists_orank_eq (A := A)
      (lt_card_of_lt_posCount (A := A) (Nat.sub_lt (by omega) Nat.one_pos))
    have hit : i < t := by
      refine lt_of_not_ge fun hcon => ?_
      have := orank_le_iff.mpr hcon
      omega
    exact hno t hit (bitIx_max_of_isTopIx hm (by rw [IsTopIx, ht]; omega))

/-- **A low index, read from the same bits**: one with a bit of the greatest
element strictly above it. -/
theorem isLowIx_iff_bits {i m : A} (hm : ∀ k : A, k ≤ m) :
    IsLowIx i ↔ ∃ k : A, i < k ∧ BitIx k m := by
  constructor
  · intro h
    rw [IsLowIx] at h
    obtain ⟨t, ht⟩ := exists_orank_eq (A := A)
      (lt_card_of_lt_posCount (A := A) (Nat.sub_lt (by omega) Nat.one_pos))
    have hit : i < t := by
      refine lt_of_not_ge fun hcon => ?_
      have := orank_le_iff.mpr hcon
      omega
    exact ⟨t, hit, bitIx_max_of_isTopIx hm (by rw [IsTopIx, ht]; omega)⟩
  · rintro ⟨k, hik, hb⟩
    have h1 : orank i < orank k := orank_lt_orank hik
    have h2 := orank_lt_posCount_of_bitIx hb
    rw [IsLowIx]
    omega

end BitIx

/-! ### Definability of the bit layer -/

section Definability

variable {L : Language.{0, 0}} {α : Type}

/-- The strict order between two variables is definable. -/
theorem arithDef_lt (x y : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => v x < v y) :=
  ((arithDef_le x y).and (arithDef_le y x).not).congr fun _ _ _ _ _ _ =>
    lt_iff_le_not_ge.symm

/-- A rank being zero is definable: `x + x = x` holds of the least element
only. -/
theorem arithDef_isZero (x : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => orank (v x) = 0) :=
  (arithDef_plus x x x).congr fun _ _ _ _ _ _ => by omega

/-- A rank being one is definable: an idempotent nonzero rank. -/
theorem arithDef_isOne (x : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => orank (v x) = 1) :=
  ((arithDef_times x x x).and (arithDef_isZero x).not).congr fun _ _ _ _ _ v => by
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : orank (v x) * orank (v x) = orank (v x) * 1 := by omega
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) h3
    · rintro h
      rw [h]
      exact ⟨rfl, by omega⟩

/-- **Being a position is definable**, by
`DescriptiveComplexity.isPos_iff_forall_dvd`. -/
theorem arithDef_isPos (x : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => IsPos (v x)) := by
  have hdvd : ArithDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u => ∃ w : Fin 1 → _, orank (w 0) * orank (u (Sum.inr 0)) =
        orank (u (Sum.inl x))) :=
    (arithDef_times (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1)
      (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inl x))).exs
  have heven : ArithDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u => ∃ e : Fin 1 → _, orank (e 0) + orank (e 0) =
        orank (u (Sum.inr 0))) :=
    (arithDef_plus (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1)
      (Sum.inr 0) (Sum.inr 0) (Sum.inl (Sum.inr 0))).exs
  have hstep := (hdvd.imp ((arithDef_isOne (L := L) (α := α ⊕ Fin 1) (Sum.inr 0)).or heven)).all
  refine ((arithDef_isZero (L := L) (α := α) x).not.and hstep).congr fun A _ _ _ _ v => ?_
  rw [isPos_iff_forall_dvd]
  refine and_congr Iff.rfl (forall_congr' fun d => ?_)
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro h ⟨w, hw⟩
    rcases h ⟨fun _ => w, hw⟩ with h1 | ⟨e, he⟩
    · exact Or.inl h1
    · exact Or.inr ⟨e 0, he⟩
  · rintro h ⟨w, hw⟩
    rcases h ⟨w 0, hw⟩ with h1 | ⟨e, he⟩
    · exact Or.inl h1
    · exact Or.inr ⟨fun _ => e, he⟩

/-- **The bit relation is definable**: `DescriptiveComplexity.BitAt` is a
formula of `FO(≤, +, ×)`, so the bit layer costs the logic nothing. -/
theorem arithDef_bit (p x : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => BitAt (v p) (v x)) := by
  have hsplit : ArithDef (L := L) (α := α ⊕ Fin 4)
      (fun _ _ _ _ _ u =>
        orank (u (Sum.inl p)) + orank (u (Sum.inl p)) = orank (u (Sum.inr 0)) ∧
          (orank (u (Sum.inr 1)) + orank (u (Sum.inr 2)) = orank (u (Sum.inl x)) ∧
            (u (Sum.inl p) ≤ u (Sum.inr 2) ∧
              (u (Sum.inr 2) < u (Sum.inr 0) ∧
                orank (u (Sum.inr 3)) * orank (u (Sum.inr 0)) = orank (u (Sum.inr 1)))))) :=
    (arithDef_plus (Sum.inl p) (Sum.inl p) (Sum.inr 0)).and
      ((arithDef_plus (Sum.inr 1) (Sum.inr 2) (Sum.inl x)).and
        ((arithDef_le (Sum.inl p) (Sum.inr 2)).and
          ((arithDef_lt (Sum.inr 2) (Sum.inr 0)).and
            (arithDef_times (Sum.inr 3) (Sum.inr 0) (Sum.inr 1)))))
  have hover : ArithDef (L := L) (α := α)
      (fun _ _ _ _ _ v => ∃ q : Fin 1 → _,
        orank (v p) + orank (v p) = orank (q 0)) :=
    (arithDef_plus (L := L) (α := α ⊕ Fin 1) (Sum.inl p) (Sum.inl p) (Sum.inr 0)).exs
  refine (hsplit.exs.or (hover.not.and (arithDef_le p x))).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, BitAt]
  refine or_congr ?_ (and_congr ?_ Iff.rfl)
  · constructor
    · rintro ⟨w, h1, h2, h3, h4, h5⟩
      exact ⟨w 0, w 1, w 2, w 3, h1, h2, h3, h4, h5⟩
    · rintro ⟨q, u, v', w, h1, h2, h3, h4, h5⟩
      exact ⟨![q, u, v', w], h1, h2, h3, h4, h5⟩
  · constructor
    · rintro h ⟨q, hq⟩
      exact h ⟨fun _ => q, hq⟩
    · rintro h ⟨q, hq⟩
      exact h ⟨q 0, hq⟩

/-! #### The naming bridge

The one thing the place-value naming does not hand over. Everything above is a
formula of `FO(≤, +, ×)` outright; the *index* naming needs, on top of it, the
graph of `i ↦ 2 ^ i`, and that is a theorem rather than a construction – the
half of [Immerman 1999][immerman1999descriptive] Thm 1.17 that goes from `+, ×`
to `BIT` at an exponent. It is named here, where its consumers are, and proved
in `DescriptiveComplexity.LogTime.Pow`, which is where the certificate it is
proved by can be stated. -/

/-- **The naming bridge**: the graph of `i ↦ 2 ^ i` is a formula of
`FO(≤, +, ×)`, uniformly in the variable layout.

This is [Immerman 1999][immerman1999descriptive] Thm 1.17(2), and it is proved:
`DescriptiveComplexity.powArithDef`, by the packing argument that guesses the
doubling chain of `i`. It is a `def` rather than a plain statement because every
consumer needs it at its own variable layout;
`DescriptiveComplexity.BitDefinable` is a logic over the index naming, and this
is what turns its bit atom back into the place-value one. -/
def PowArithDef (L : Language.{0, 0}) : Prop :=
  ∀ {α : Type} (i p : α),
    ArithDef (L := L) (α := α) fun _ _ _ _ _ v => orank (v p) = 2 ^ orank (v i)

/-- **The bit at an index is first-order, given the bridge**: guess the place
value, and read the place-value bit there. -/
theorem PowArithDef.arithDef_bitIx (h : PowArithDef L) (i x : α) :
    ArithDef (L := L) (α := α) fun _ _ _ _ _ v => BitIx (v i) (v x) := by
  refine (((h (α := α ⊕ Fin 1) (Sum.inl i) (Sum.inr 0)).and
    (arithDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl x))).ex).congr
    fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [bitIx_iff_bitAt]

end Definability

end DescriptiveComplexity
