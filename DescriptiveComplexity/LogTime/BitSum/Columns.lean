/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import DescriptiveComplexity.LogTime.BitSum.Sum

/-!
# The columns of a product, and the carry chain that adds one block of them

The schoolbook product of two `P`-bit numbers is a sum of columns,
`x · y = Σ_j c_j 2 ^ j`, where `c_j` counts the pairs of set bits whose indices
add to `j` – a count the Bit Sum Lemma delivers, one column at a time
(`DescriptiveComplexity.BitSum.mul_eq_colSum`). What the Bit Sum Lemma does
*not* deliver is the outer sum: summing the `2 P` weighted columns is an
iterated addition again, and every direct route to it fails – brute force,
carries guessed for the whole product, digit tables, Chinese remainders.

The way out is the block split, taken once, plus a **guessed carry chain per
block**. Cut the columns into blocks of `g` with `2 ^ g > P`; the sum of one
block is `Σ_{t<g} c_{a+t} 2 ^ t`, and adding it column by column keeps a running
remainder below `P` – so the whole chain of a block is `g` remainders of `g`
bits, which fits in **one element** and is laid out with the boundary-set
device. That is exactly the "guess the carries" route the design notes rule out
for the *whole* product (there it is `P` remainders, one element cannot hold
them); confined to a block it is affordable, and no further descent is needed.

This file is the `ℕ` side of that construction, with no structure in sight:

* `DescriptiveComplexity.BitSum.intervalSum` – the weighted sum of a range of
  columns, and its concatenation law
  (`DescriptiveComplexity.BitSum.intervalSum_append`);
* `DescriptiveComplexity.BitSum.carryChain` – the remainders of the column-wise
  addition, defined as quotients of the partial sums, with the three equations
  the certificate checks: the first column
  (`DescriptiveComplexity.BitSum.carryChain_base`), one step
  (`DescriptiveComplexity.BitSum.carryChain_step`), and the final remainder
  being the high bits (`DescriptiveComplexity.BitSum.carryChain_last`);
* `DescriptiveComplexity.BitSum.eq_packVal_of_windows` and
  `DescriptiveComplexity.BitSum.packVal_evenOdd` – reading a packed element off
  its windows, and re-assembling the even and the odd blocks into the sum of
  all columns;
* `DescriptiveComplexity.BitSum.colWordN` /
  `DescriptiveComplexity.BitSum.colCountN` – the word whose ones are one
  column, and the column count, with the product identity
  `DescriptiveComplexity.BitSum.mul_eq_colSum`.
-/

namespace DescriptiveComplexity

namespace BitSum

open Finset

/-! ### Reading a bit as a number -/

/-- **A bit, as the number it contributes**: the digit of `x` at `i`. -/
theorem toNat_testBit (x i : ℕ) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  have hlt : x / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h1 : x / 2 ^ i % 2 = 1
  · simp [h1]
  · simp only [h1, decide_false, Bool.toNat_false]
    omega

/-- **One more bit of a remainder**: the next binary digit, in the form the
carry chain steps through. -/
theorem mod_two_pow_succ (x k : ℕ) :
    x % 2 ^ (k + 1) = x % 2 ^ k + (x.testBit k).toNat * 2 ^ k := by
  have h := Nat.mod_pow_succ (x := x) (b := 2) (k := k)
  have hc : 2 ^ k * (x / 2 ^ k % 2) = (x / 2 ^ k % 2) * 2 ^ k := Nat.mul_comm _ _
  rw [toNat_testBit]
  omega

/-- **A number is the sum of its bits**, below any width that bounds it. -/
theorem mod_two_pow_eq_sum (x : ℕ) : ∀ m : ℕ,
    x % 2 ^ m = ∑ i ∈ range m, (x.testBit i).toNat * 2 ^ i := by
  intro m
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih => rw [mod_two_pow_succ, sum_range_succ, ih]

/-- The same, for a number known to fit. -/
theorem eq_sum_testBit {x m : ℕ} (hx : x < 2 ^ m) :
    x = ∑ i ∈ range m, (x.testBit i).toNat * 2 ^ i :=
  (Nat.mod_eq_of_lt hx).symm.trans (mod_two_pow_eq_sum x m)

/-- **A number with no high bits is small**: the converse of
`Nat.testBit_lt_two_pow`, which the guessed elements' vanishing conditions are
read through. -/
theorem lt_two_pow_of_high_bits {v k : ℕ} (h : ∀ i, k ≤ i → v.testBit i = false) :
    v < 2 ^ k := by
  have hmod : v % 2 ^ k = v := Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.lt_or_ge i k with hi | hi
    · rw [decide_eq_true hi, Bool.true_and]
    · rw [h i hi, decide_eq_false (by omega), Bool.false_and]
  rw [← hmod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **A number with no low bits is a shifted quotient.** -/
theorem eq_two_pow_mul_div {x b : ℕ} (hlow : ∀ i, i < b → x.testBit i = false) :
    x = 2 ^ b * (x / 2 ^ b) := by
  have hmod : x % 2 ^ b = 0 := by
    rw [mod_two_pow_eq_sum]
    exact Finset.sum_eq_zero fun i hi => by
      rw [hlow i (mem_range.mp hi)]
      simp
  have := Nat.div_add_mod x (2 ^ b)
  omega

/-- **A number whose bits are another's, shifted, is that number shifted**: the
identity that reads a certificate's tail element as `2 ^ b` times its value. -/
theorem eq_two_pow_mul_of_testBit {x t b : ℕ} (hlow : ∀ i, i < b → x.testBit i = false)
    (hbits : ∀ k, x.testBit (b + k) = t.testBit k) : x = 2 ^ b * t := by
  rw [eq_two_pow_mul_div hlow]
  congr 1
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Nat.testBit_div_two_pow, ← hbits k]
  congr 1
  omega

/-! ### Weighted sums of column ranges -/

/-- **The weighted sum of a range of columns**: `Σ_{t<m} h (a + t) · 2 ^ t`,
the value of the columns `a, …, a + m - 1` read from position `a`. -/
def intervalSum (h : ℕ → ℕ) (a m : ℕ) : ℕ := ∑ t ∈ range m, h (a + t) * 2 ^ t

@[simp] theorem intervalSum_zero (h : ℕ → ℕ) (a : ℕ) : intervalSum h a 0 = 0 := by
  simp [intervalSum]

/-- One more column on top. -/
theorem intervalSum_succ (h : ℕ → ℕ) (a m : ℕ) :
    intervalSum h a (m + 1) = intervalSum h a m + h (a + m) * 2 ^ m :=
  sum_range_succ _ _

@[simp] theorem intervalSum_one (h : ℕ → ℕ) (a : ℕ) : intervalSum h a 1 = h a := by
  simp [intervalSum]

/-- **Concatenating two ranges of columns**: the second range enters shifted by
the width of the first. Every regrouping below is this identity. -/
theorem intervalSum_append (h : ℕ → ℕ) (a m m' : ℕ) :
    intervalSum h a (m + m') = intervalSum h a m + 2 ^ m * intervalSum h (a + m) m' := by
  induction m' with
  | zero => simp
  | succ m' ih =>
    rw [show m + (m' + 1) = (m + m') + 1 from rfl, intervalSum_succ, ih,
      intervalSum_succ, show a + (m + m') = a + m + m' by omega, pow_add]
    ring

/-- **The sum of a range fits** just above the widest column. -/
theorem intervalSum_lt {h : ℕ → ℕ} {a m H : ℕ} (hH : 0 < H)
    (hb : ∀ t, t < m → h (a + t) < H) : intervalSum h a m < H * 2 ^ m := by
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    have h1 : intervalSum h a m < H * 2 ^ m := ih fun t ht => hb t (by omega)
    have h2 : h (a + m) * 2 ^ m ≤ (H - 1) * 2 ^ m :=
      Nat.mul_le_mul_right _ (by have := hb m (by omega); omega)
    have h3 : (H - 1) * 2 ^ m + 2 ^ m = H * 2 ^ m := by
      have hH1 : H - 1 + 1 = H := by omega
      calc (H - 1) * 2 ^ m + 2 ^ m = (H - 1 + 1) * 2 ^ m := by ring
        _ = H * 2 ^ m := by rw [hH1]
    have h4 : H * 2 ^ (m + 1) = H * 2 ^ m + H * 2 ^ m := by
      rw [pow_succ]
      ring
    have h5 : 0 < 2 ^ m := Nat.two_pow_pos m
    rw [intervalSum_succ]
    omega

/-! ### The carry chain of one range -/

/-- **The remainder after adding the columns up to `a + t`**: what has been
accumulated and not yet written, i.e. the partial sum shifted below its first
unwritten position. The certificate stores these, one field per column. -/
def carryChain (h : ℕ → ℕ) (a t : ℕ) : ℕ := intervalSum h a (t + 1) / 2 ^ (t + 1)

/-- **The remainders stay small**: below any bound on the columns. -/
theorem carryChain_lt {h : ℕ → ℕ} {a t H : ℕ} (hH : 0 < H)
    (hb : ∀ u, u < t + 1 → h (a + u) < H) : carryChain h a t < H :=
  (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (intervalSum_lt hH hb)

/-- **The first column**: it splits into the lowest bit of the sum and the
first remainder. -/
theorem carryChain_base {h : ℕ → ℕ} {a m : ℕ} (hm : 0 < m) :
    h a = 2 * carryChain h a 0 + ((intervalSum h a m).testBit 0).toNat := by
  have hsplit : intervalSum h a m = h a + 2 * intervalSum h (a + 1) (m - 1) := by
    have := intervalSum_append h a 1 (m - 1)
    rw [show 1 + (m - 1) = m by omega] at this
    rw [this]
    simp
  have hmod : (h a + 2 * intervalSum h (a + 1) (m - 1)) % 2 = h a % 2 := by
    rw [Nat.mul_comm, Nat.add_mul_mod_self_right]
  have hchain : carryChain h a 0 = h a / 2 := by
    rw [carryChain, intervalSum_one, pow_one]
  have hdm := Nat.div_add_mod (h a) 2
  rw [hchain, toNat_testBit, pow_zero, Nat.div_one, hsplit, hmod]
  omega

/-- **One step of the chain**: the incoming remainder plus the next column
splits into the next bit of the sum and the outgoing remainder. This is the
equation the certificate checks at every boundary. -/
theorem carryChain_step {h : ℕ → ℕ} {a m t : ℕ} (ht : t + 1 < m) :
    carryChain h a t + h (a + (t + 1)) =
      2 * carryChain h a (t + 1) + ((intervalSum h a m).testBit (t + 1)).toNat := by
  have hleft : carryChain h a t + h (a + (t + 1)) = intervalSum h a (t + 2) / 2 ^ (t + 1) := by
    have h2 : intervalSum h a (t + 2)
        = intervalSum h a (t + 1) + h (a + (t + 1)) * 2 ^ (t + 1) :=
      intervalSum_succ h a (t + 1)
    rw [carryChain, h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (t + 1))]
  have hsplit : intervalSum h a m
      = intervalSum h a (t + 2) + 2 ^ (t + 2) * intervalSum h (a + (t + 2)) (m - (t + 2)) := by
    have hap := intervalSum_append h a (t + 2) (m - (t + 2))
    rw [show t + 2 + (m - (t + 2)) = m by omega] at hap
    exact hap
  have hmod : intervalSum h a m / 2 ^ (t + 1) % 2
      = intervalSum h a (t + 2) / 2 ^ (t + 1) % 2 := by
    rw [hsplit, show 2 ^ (t + 2) * intervalSum h (a + (t + 2)) (m - (t + 2))
        = intervalSum h (a + (t + 2)) (m - (t + 2)) * 2 * 2 ^ (t + 1) by rw [pow_succ]; ring,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos (t + 1)), Nat.add_mul_mod_self_right]
  have hdd : intervalSum h a (t + 2) / 2 ^ (t + 1) / 2
      = intervalSum h a (t + 2) / 2 ^ (t + 2) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hdm := Nat.div_add_mod (intervalSum h a (t + 2) / 2 ^ (t + 1)) 2
  have hV : ((intervalSum h a m).testBit (t + 1)).toNat
      = intervalSum h a (t + 2) / 2 ^ (t + 1) % 2 := by
    rw [toNat_testBit, hmod]
  have hcc : carryChain h a (t + 1) = intervalSum h a (t + 2) / 2 ^ (t + 2) := rfl
  rw [hleft, hV, hcc]
  omega

/-- **The final remainder is the high part**: what is left after the last
column is exactly the bits of the sum above the range. -/
theorem carryChain_last {h : ℕ → ℕ} {a m : ℕ} (hm : 0 < m) :
    intervalSum h a m / 2 ^ m = carryChain h a (m - 1) := by
  rw [carryChain, Nat.sub_add_cancel hm]

/-! ### Reading a packed element off its windows -/

/-- **An element whose windows are a packing's fields is the packing**: equal
windows at every field, no bits above, and the values fitting their fields pin
the number bit by bit. This is how the soundness half reads the two half-sums
off the guessed elements. -/
theorem eq_packVal_of_windows {x w M : ℕ} {f : ℕ → ℕ} (hw : 0 < w)
    (hf : ∀ m, m < M → f m < 2 ^ w)
    (hwin : ∀ m, m < M → x / 2 ^ (m * w) % 2 ^ w = f m)
    (hhigh : ∀ i, M * w ≤ i → x.testBit i = false) : x = packVal w f M := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases Nat.lt_or_ge i (M * w) with hi | hi
  · have hm : i / w < M := (Nat.div_lt_iff_lt_mul hw).mpr hi
    have hk : i % w < w := Nat.mod_lt _ hw
    have hi' : i / w * w + i % w = i := by
      have h1 := Nat.div_add_mod i w
      have h2 : w * (i / w) = i / w * w := Nat.mul_comm _ _
      omega
    have hx : x.testBit i = (f (i / w)).testBit (i % w) := by
      rw [← hwin (i / w) hm, testBit_window, decide_eq_true hk, Bool.true_and, hi']
    have hp : (packVal w f M).testBit i = (f (i / w)).testBit (i % w) := by
      rw [← packVal_window hf hm, testBit_window, decide_eq_true hk, Bool.true_and, hi']
    rw [hx, hp]
  · rw [hhigh i hi]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (packVal_lt hf)
      (Nat.pow_le_pow_right (by norm_num) hi))).symm

/-- **Re-assembling the two half-sums**: the packing of the even block sums
plus the packing of the odd ones, shifted by one block, is the weighted sum of
all the columns they cover. This is the identity behind the one addition of the
certificate. -/
theorem packVal_evenOdd (h : ℕ → ℕ) (g : ℕ) : ∀ M : ℕ,
    packVal (2 * g) (fun m => intervalSum h (m * (2 * g)) g) M
      + 2 ^ g * packVal (2 * g) (fun m => intervalSum h (m * (2 * g) + g) g) M
      = intervalSum h 0 (M * (2 * g)) := by
  intro M
  induction M with
  | zero => simp [packVal]
  | succ M ih =>
    have hE : packVal (2 * g) (fun m => intervalSum h (m * (2 * g)) g) (M + 1)
        = packVal (2 * g) (fun m => intervalSum h (m * (2 * g)) g) M
          + intervalSum h (M * (2 * g)) g * 2 ^ (M * (2 * g)) := rfl
    have hO : packVal (2 * g) (fun m => intervalSum h (m * (2 * g) + g) g) (M + 1)
        = packVal (2 * g) (fun m => intervalSum h (m * (2 * g) + g) g) M
          + intervalSum h (M * (2 * g) + g) g * 2 ^ (M * (2 * g)) := rfl
    have hblock : intervalSum h (M * (2 * g)) (2 * g)
        = intervalSum h (M * (2 * g)) g + 2 ^ g * intervalSum h (M * (2 * g) + g) g := by
      rw [show 2 * g = g + g from two_mul g, intervalSum_append]
    have hsplit : intervalSum h 0 ((M + 1) * (2 * g))
        = intervalSum h 0 (M * (2 * g))
          + 2 ^ (M * (2 * g)) * intervalSum h (M * (2 * g)) (2 * g) := by
      rw [show (M + 1) * (2 * g) = M * (2 * g) + 2 * g by ring, intervalSum_append,
        Nat.zero_add]
    rw [hE, hO, hsplit, hblock, ← ih]
    ring

/-! ### The columns of a product -/

/-- **The word of one column**: its bit at `i` says that `y` has a one at `i`
and `x` a one at `j - i` – a pair of set bits whose indices add to `j`. It is a
sub-mask of `y`, so it is always the value of an element. -/
noncomputable def colWordN (x y j : ℕ) : ℕ :=
  y &&& bitsVal (fun i => decide (i ≤ j) && x.testBit (j - i)) (j + 1)

/-- What the bits of a column word are. -/
theorem testBit_colWordN (x y j i : ℕ) :
    (colWordN x y j).testBit i = (y.testBit i && (decide (i ≤ j) && x.testBit (j - i))) := by
  rw [colWordN, Nat.testBit_land]
  rcases Nat.lt_or_ge i (j + 1) with hi | hi
  · rw [testBit_bitsVal _ _ hi]
  · have h1 : (bitsVal (fun i => decide (i ≤ j) && x.testBit (j - i)) (j + 1)).testBit i =
        false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitsVal_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) hi))
    rw [h1, decide_eq_false (by omega : ¬ i ≤ j)]
    simp

/-- A column word is a sub-mask of `y`. -/
theorem colWordN_le (x y j : ℕ) : colWordN x y j ≤ y := Nat.and_le_left

/-- **The count of one column**: the number of ones of its word among the
first `P` positions. -/
noncomputable def colCountN (x y P j : ℕ) : ℕ := onesBelow (colWordN x y j) P

/-- A column has no more ones than there are positions. -/
theorem colCountN_le (x y P j : ℕ) : colCountN x y P j ≤ P := onesBelow_le _ _

/-- **The product is the weighted sum of its column counts** – the schoolbook
multiplication, columns grouped by weight, under the one condition that no pair
of set bits reaches past the available positions. -/
theorem mul_eq_colSum {x y P : ℕ} (hx : x < 2 ^ P) (hy : y < 2 ^ P)
    (hover : ∀ i d, y.testBit i = true → x.testBit d = true → i + d < P) :
    x * y = intervalSum (colCountN x y P) 0 P := by
  classical
  set S : Finset (ℕ × ℕ) :=
    (range P ×ˢ range P).filter fun p => y.testBit p.1 = true ∧ x.testBit p.2 = true with hS
  -- the product as a sum over the pairs of set bits
  have hstep1 : x * y = ∑ p ∈ S, 2 ^ (p.1 + p.2) := by
    calc x * y
        = (∑ i ∈ range P, (y.testBit i).toNat * 2 ^ i)
          * (∑ d ∈ range P, (x.testBit d).toNat * 2 ^ d) := by
          rw [← eq_sum_testBit hx, ← eq_sum_testBit hy, Nat.mul_comm]
      _ = ∑ i ∈ range P, ∑ d ∈ range P,
            (y.testBit i).toNat * (x.testBit d).toNat * 2 ^ (i + d) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [pow_add]
          ring
      _ = ∑ p ∈ range P ×ˢ range P,
            (y.testBit p.1).toNat * (x.testBit p.2).toNat * 2 ^ (p.1 + p.2) :=
          (Finset.sum_product' (s := range P) (t := range P) (f := fun i d =>
            (y.testBit i).toNat * (x.testBit d).toNat * 2 ^ (i + d))).symm
      _ = ∑ p ∈ S, (y.testBit p.1).toNat * (x.testBit p.2).toNat * 2 ^ (p.1 + p.2) :=
          (Finset.sum_filter_of_ne fun p _ hne => by
            constructor
            · by_contra hc
              rw [Bool.not_eq_true] at hc
              rw [hc] at hne
              simp at hne
            · by_contra hc
              rw [Bool.not_eq_true] at hc
              rw [hc] at hne
              simp at hne).symm
      _ = ∑ p ∈ S, 2 ^ (p.1 + p.2) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hS] at hp
          simp only [Finset.mem_filter] at hp
          rw [hp.2.1, hp.2.2]
          simp
  -- grouped by column
  have hmaps : ∀ p ∈ S, p.1 + p.2 ∈ range P := by
    intro p hp
    rw [hS] at hp
    simp only [Finset.mem_filter] at hp
    exact mem_range.mpr (hover _ _ hp.2.1 hp.2.2)
  have hstep2 : ∑ p ∈ S, 2 ^ (p.1 + p.2)
      = ∑ j ∈ range P, ∑ p ∈ S.filter (fun p => p.1 + p.2 = j), 2 ^ (p.1 + p.2) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  -- one column's fiber is counted by its word
  have hcard : ∀ j, j < P →
      (S.filter fun p => p.1 + p.2 = j).card = colCountN x y P j := by
    intro j hj
    rw [colCountN, onesBelow]
    refine (Finset.card_nbij (fun i => (i, j - i)) ?_ ?_ ?_).symm
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiP, hbit⟩ := hi
      rw [testBit_colWordN, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbit
      obtain ⟨hyi, hij, hxd⟩ := hbit
      simp only [hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨hiP, by omega⟩, hyi, hxd⟩, by omega⟩
    · intro i _ i' _ hii'
      exact (Prod.mk.injEq _ _ _ _).mp hii' |>.1
    · intro p hp
      simp only [hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      obtain ⟨⟨⟨h1P, h2P⟩, hyb, hxb⟩, hsum⟩ := hp
      refine ⟨p.1, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨h1P, ?_⟩
        rw [testBit_colWordN, hyb, decide_eq_true (by omega : p.1 ≤ j),
          show j - p.1 = p.2 by omega, hxb]
        rfl
      · change (p.1, j - p.1) = p
        rw [show j - p.1 = p.2 by omega]
  -- assemble
  rw [hstep1, hstep2, intervalSum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hfiber : ∑ p ∈ S.filter (fun p => p.1 + p.2 = j), 2 ^ (p.1 + p.2)
      = ∑ p ∈ S.filter (fun p => p.1 + p.2 = j), 2 ^ j := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    rw [hp.2]
  rw [hfiber, Finset.sum_const, smul_eq_mul, hcard j (mem_range.mp hj), Nat.zero_add]

end BitSum

end DescriptiveComplexity
