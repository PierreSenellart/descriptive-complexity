/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Sum

/-!
# Level 2: counting a middling word by its sub-blocks

The first instantiation of the running sum
(`DescriptiveComplexity.LogTime.BitSum.Sum`): cut a word of `m` bits into
sub-blocks, keep the running count in each, and let the table
(`DescriptiveComplexity.BitSum.PopShort`) count one sub-block. The result has the
*same shape* as the table's own statement –

> `DescriptiveComplexity.BitSum.PopMid m x y`: `y` is the number of ones of the
> `m`-bit word `x` –

which is what lets level 1 be the very same construction one size up, with
`PopMid` in the place `PopShort` occupies here.

## Two things the certificate does not have to say

**Which sub-block length to use.** The length `l` is existentially quantified and
constrained only to be a position index: soundness holds for *any* such `l`
(`DescriptiveComplexity.BitSum.popMid_sound` takes no size hypothesis at all),
and the completeness half is where a concrete `l` is chosen and the sizes of
`DescriptiveComplexity.LogTime.BitSum.Sizes` are checked. This is what keeps the
formula free of arithmetic it could not express: “the table fits” is a product of
two variables, and no formula here ever has to state it.

**Where the word ends.** The certificate reads the running sum at any boundary
past `m`, not at `m` itself, so the sub-block length never has to divide the word
length. Counting further costs nothing, the word having no ones up there.
-/

namespace DescriptiveComplexity

namespace BitSum

open Finset

/-! ### Counting past the end of a word -/

/-- **Counting further than the word is long changes nothing.** -/
theorem onesBelow_eq_of_ge {x w k : ℕ} (hx : ∀ i, w ≤ i → x.testBit i = false) (hk : w ≤ k) :
    onesBelow x k = onesBelow x w := by
  rw [onesBelow, onesBelow]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  refine ⟨fun hi => ⟨?_, hi.2⟩, fun hi => ⟨by omega, hi.2⟩⟩
  by_contra hc
  rw [hx i (by omega)] at hi
  exact absurd hi.2 (by simp)

/-- **A word has no more ones than it is long.** -/
theorem onesBelow_le_of_bits {x w k : ℕ} (hx : ∀ i, w ≤ i → x.testBit i = false) :
    onesBelow x k ≤ w := by
  rcases Nat.le_total w k with hk | hk
  · rw [onesBelow_eq_of_ge hx hk]
    exact onesBelow_le _ _
  · exact le_trans (onesBelow_le _ _) hk

/-! ### The level -/

section Level2

variable {A : Type} [LinearOrder A] [Finite A]

/-- **`y` is the number of ones of the `m`-bit word `x`**: a sub-block length, a
boundary set, the running sums along it, and a boundary past `m` at which the
running sum is read. The sub-block counts are supplied by the table. -/
def PopMid (m x y : A) : Prop :=
  ∃ l B S b b' : A, orank l ≠ 0 ∧ IsLowIx l ∧ IsBlockSet l B ∧ SumOk l B x S (PopShort l) ∧
    BitIx b B ∧ m ≤ b ∧ orank b + orank l = orank b' ∧ IsLowIx b' ∧ WindowAt b b' S y

/-- **The certificate is sound, with no condition on the sizes**: whatever
sub-block length is guessed, the running sum read past the end of the word is the
number of its ones. The level below is used only through
`DescriptiveComplexity.BitSum.popShort_sound`, which is itself unconditional
above the index range. -/
theorem popMid_sound {m x y : A} (hx : ∀ i, orank m ≤ i → (orank x).testBit i = false)
    (h : PopMid m x y) : orank y = onesBelow (orank x) (orank m) := by
  obtain ⟨l, B, S, b, b', hl0, hllow, hB, hS, hbB, hmb, hsum, hlow', hwin⟩ := h
  have hlpos : 0 < orank l := by omega
  have hlP : orank l < posCount A := by
    rw [IsLowIx] at hllow
    omega
  obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hlpos hB b).mp hbB
  have hcount := sum_eq hlpos hB hS (fun w n _ hn => popShort_sound hlP hn) j b b' y hj hbB
    hsum hlow' hwin
  rw [hcount, onesBelow_eq_of_ge hx (orank_le_iff.mpr hmb)]

/-- **The certificate exists**: the sub-block length of
`DescriptiveComplexity.LogTime.BitSum.Sizes`, the boundaries at that gap, the
running sums along them, and the first boundary past the end of the word. All
three size conditions of the table are discharged here, and nowhere else. -/
theorem exists_popMid [Nonempty A] {m x : A} (hP : 2 ^ 20 ≤ posCount A)
    (hm : orank m < 2 ^ lvl2Block (posCount A))
    (hroom : orank m + 2 * lvl2Block (posCount A) + 2 < posCount A)
    (hx : ∀ i, orank m ≤ i → (orank x).testBit i = false) :
    ∃ y : A, PopMid m x y := by
  classical
  have hcard := posCount_lt_card (A := A)
  set K := lvl2Block (posCount A) with hK
  have hK2 : 2 ≤ K := two_le_lvl2Block hP
  -- the sub-block length, as an element
  obtain ⟨l, hl⟩ := exists_orank_eq (A := A) (m := K) (by omega)
  have hl0 : orank l ≠ 0 := by omega
  have hlpos : 0 < orank l := by omega
  have hllow : IsLowIx l := by
    rw [IsLowIx, hl]
    omega
  have hlP : orank l < posCount A := by omega
  -- the boundaries and the running sums
  obtain ⟨B, hB⟩ := exists_isBlockSet (A := A) (g := l) (by omega)
  have hfit : (orank l + 1) * 2 ^ orank l < posCount A - 1 := by rw [hl]; exact table_lt hP
  have hcap : posCount A ≤ 2 ^ orank l * 2 ^ 2 ^ orank l := by
    have h1 : posCount A < 2 ^ Nat.size (posCount A) := Nat.lt_size_self _
    have h2 : Nat.size (posCount A) ≤ 2 ^ orank l := by rw [hl]; exact size_le_two_pow_lvl2Block _
    have h3 : (2 : ℕ) ^ Nat.size (posCount A) ≤ 2 ^ 2 ^ orank l :=
      Nat.pow_le_pow_right (by norm_num) h2
    have h4 : (1 : ℕ) ≤ 2 ^ orank l := Nat.one_le_two_pow
    have h5 : (2 : ℕ) ^ 2 ^ orank l ≤ 2 ^ orank l * 2 ^ 2 ^ orank l :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨S, hS⟩ := exists_sumOk (x := x) hlpos hB
    (fun w n _ hn => popShort_sound hlP hn)
    (fun w hw => by
      obtain ⟨n, hn⟩ := exists_orank_eq (A := A)
        (m := onesBelow (orank w) (orank l)) (by
          have := onesBelow_le (orank w) (orank l)
          omega)
      exact ⟨n, popShort_of_eq hfit hcap hw hn⟩)
    (fun k => lt_of_le_of_lt (onesBelow_le_of_bits hx) (by rw [hl]; exact hm))
  -- the first boundary past the end of the word
  set j := orank m / orank l + 1 with hj
  have hbval : orank l * j ≤ orank m + orank l := by
    have := Nat.div_mul_le_self (orank m) (orank l)
    have hcomm : orank l * (orank m / orank l) = orank m / orank l * orank l := Nat.mul_comm _ _
    rw [hj, Nat.mul_succ]
    omega
  have hbgt : orank m < orank l * j := by
    have hmod := Nat.div_add_mod (orank m) (orank l)
    have hlt : orank m % orank l < orank l := Nat.mod_lt _ hlpos
    have hcomm : orank l * (orank m / orank l) = orank m / orank l * orank l := Nat.mul_comm _ _
    rw [hj, Nat.mul_succ]
    omega
  obtain ⟨b, hb⟩ := exists_orank_eq (A := A) (m := orank l * j) (by omega)
  obtain ⟨b', hb'⟩ := exists_orank_eq (A := A) (m := orank l * j + orank l) (by omega)
  have hblow : IsLowIx b := by rw [IsLowIx, hb]; omega
  have hb'low : IsLowIx b' := by rw [IsLowIx, hb']; omega
  have hbB : BitIx b B := (bitIx_iff_of_isBlockSet hlpos hB b).mpr ⟨⟨j, hb⟩, hblow⟩
  obtain ⟨y, hy⟩ := exists_windowAt (b := b) (e := b') (x := S) (w := orank l) (by omega)
  exact ⟨y, l, B, S, b, b', hl0, hllow, hB, hS, hbB, orank_le_iff.mp (by omega),
    by omega, hb'low, hy⟩

end Level2

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **Level 2 is a formula**, the level below entering it only through
`DescriptiveComplexity.BitSum.bitDef_popShort`, passed to
`DescriptiveComplexity.BitSum.bitDef_sumOk` as the chunk counter. -/
theorem bitDef_popMid (m x y : α) :
    BitDef (L := L) fun _ _ _ _ _ v => PopMid (v m) (v x) (v y) := by
  have hbody : BitDef (L := L) (α := α ⊕ Fin 5) (fun A _ _ _ _ u =>
      orank (u (Sum.inr 0)) ≠ 0 ∧ IsLowIx (u (Sum.inr 0)) ∧
        IsBlockSet (u (Sum.inr 0)) (u (Sum.inr 1)) ∧
          SumOk (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inl x)) (u (Sum.inr 2))
              (PopShort (u (Sum.inr 0))) ∧
            BitIx (u (Sum.inr 3)) (u (Sum.inr 1)) ∧ u (Sum.inl m) ≤ u (Sum.inr 3) ∧
              orank (u (Sum.inr 3)) + orank (u (Sum.inr 0)) = orank (u (Sum.inr 4)) ∧
                IsLowIx (u (Sum.inr 4)) ∧
                  WindowAt (u (Sum.inr 3)) (u (Sum.inr 4)) (u (Sum.inr 2)) (u (Sum.inl y))) :=
    (bitDef_isZero (Sum.inr 0)).not.and <|
      (bitDef_isLowIx (Sum.inr 0)).and <|
        (bitDef_isBlockSet (Sum.inr 0) (Sum.inr 1)).and <|
          (bitDef_sumOk (Cnt := fun _ _ _ p w n => PopShort p w n)
            (fun p w n => bitDef_popShort p w n)
            (Sum.inr 0) (Sum.inr 0) (Sum.inr 1) (Sum.inl x) (Sum.inr 2)).and <|
            (bitDef_bit (Sum.inr 3) (Sum.inr 1)).and <|
              (bitDef_le (Sum.inl m) (Sum.inr 3)).and <|
                (bitDef_plus (Sum.inr 3) (Sum.inr 0) (Sum.inr 4)).and <|
                  (bitDef_isLowIx (Sum.inr 4)).and
                    (bitDef_windowAt (Sum.inr 3) (Sum.inr 4) (Sum.inr 2) (Sum.inl y))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, w 2, w 3, w 4, hw⟩,
    fun ⟨l, B, S, b, b', h⟩ => ⟨![l, B, S, b, b'], h⟩⟩

end Definability

end BitSum

end DescriptiveComplexity
