/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Counter

/-!
# Counting ones, and the two atoms level 3 counts with

The Bit Sum Lemma is about *how many ones a word has*, and this file says what
that means and gives the two bit-level operations its base level
(`LogTime/BitSum/Table.lean`) breaks the circularity with.

## The count

`DescriptiveComplexity.BitSum.onesBelow x w` is the number of ones of `x` among
the first `w` positions. It is a `Finset.card`, not a recursion, because every
statement about it is about *changing one bit*: clearing a set bit lowers the
count by one (`DescriptiveComplexity.BitSum.onesBelow_clear`), and that single
fact is the whole recursion the level-3 table is pinned by. The width is a
parameter rather than “all of them” because levels 1 and 2 count ones below a
*position*, not of a whole element.

## The two atoms

* `DescriptiveComplexity.BitSum.ClearLow x x'` – `x'` is `x` with its lowest one
  cleared. It is first-order in `≤` and `BIT` (name the lowest set index, say
  every lower index is clear, and copy every bit but that one), the count drops
  by exactly one, and it exists whenever `x ≠ 0`. This is what lets the table for
  `popcount` be pinned *locally*, by a recursion on the value rather than on the
  count.
* `DescriptiveComplexity.BitSum.IsPowIx i p` – `p` is the place value `2 ^ i`.
  In the index naming this is free (`p` is the element whose only bit is at `i`),
  which is the mirror image of `DescriptiveComplexity.powArithDef`, where the
  same statement in `FO(≤, +, ×)` cost a certificate. It is how a level gets the
  *number* of values a sub-block can take, which is the gap of the table's
  sections.
-/

namespace DescriptiveComplexity

namespace BitSum

open Finset

/-! ### Counting ones, in `ℕ` -/

/-- **The number of ones of `x` below the position `w`.** -/
def onesBelow (x w : ℕ) : ℕ := ((range w).filter fun i => x.testBit i = true).card

@[simp] theorem onesBelow_zero (x : ℕ) : onesBelow x 0 = 0 := by simp [onesBelow]

/-- There are no more ones than positions. -/
theorem onesBelow_le (x w : ℕ) : onesBelow x w ≤ w := by
  have h := card_le_card (filter_subset (fun i => x.testBit i = true) (range w))
  rw [card_range] at h
  exact h

/-- **Nothing is counted only when there is nothing**: with all bits below `w`,
the count is `0` exactly at `0`. This is the base case of the table. -/
theorem onesBelow_eq_zero_iff {x w : ℕ} (hx : ∀ i, w ≤ i → x.testBit i = false) :
    onesBelow x w = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.zero_testBit]
    rcases Nat.lt_or_ge i w with hi | hi
    · by_contra hb
      have hmem : i ∈ (range w).filter fun j => x.testBit j = true := by
        simp only [mem_filter, mem_range]
        exact ⟨hi, by simpa using hb⟩
      rw [onesBelow, card_eq_zero] at h
      simp [h] at hmem
    · exact hx i hi
  · rintro rfl
    simp [onesBelow]

/-- **Clearing a one lowers the count by one** – whichever one it is. The
level-3 table clears the *lowest*, but the counting does not care. -/
theorem onesBelow_clear {x x' i w : ℕ} (hi : x.testBit i = true) (hiw : i < w)
    (hx' : ∀ j, x'.testBit j = (x.testBit j && decide (j ≠ i))) :
    onesBelow x' w + 1 = onesBelow x w := by
  classical
  have hmem : i ∈ (range w).filter fun j => x.testBit j = true := by
    simp only [mem_filter, mem_range]
    exact ⟨hiw, hi⟩
  have hset : ((range w).filter fun j => x'.testBit j = true)
      = ((range w).filter fun j => x.testBit j = true).erase i := by
    ext j
    simp only [mem_filter, mem_range, mem_erase, hx', Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩
  have hpos : 0 < ((range w).filter fun j => x.testBit j = true).card :=
    card_pos.mpr ⟨i, hmem⟩
  rw [onesBelow, onesBelow, hset, card_erase_of_mem hmem]
  omega

/-! ### Clearing the lowest one -/

section ClearLow

variable {A : Type} [LinearOrder A] [Finite A]

/-- **`x'` is `x` with its lowest one cleared**: an index that is set with
nothing set below it, and every other bit copied. -/
def ClearLow (x x' : A) : Prop :=
  ∃ i : A, BitIx i x ∧ (∀ j : A, j < i → ¬ BitIx j x) ∧
    ∀ j : A, (BitIx j x' ↔ (BitIx j x ∧ j ≠ i))

/-- **What clearing costs**: one one. -/
theorem onesBelow_of_clearLow {x x' : A} {w : ℕ} (h : ClearLow x x')
    (hx : ∀ i, w ≤ i → (orank x).testBit i = false) :
    onesBelow (orank x') w + 1 = onesBelow (orank x) w := by
  obtain ⟨i, hi, -, hbit⟩ := h
  rw [bitIx_iff] at hi
  have hiw : orank i < w := by
    by_contra hc
    rw [hx (orank i) (by omega)] at hi
    exact absurd hi (by simp)
  refine onesBelow_clear hi hiw fun j => ?_
  by_cases hj : j < Nat.card A
  · obtain ⟨e, he⟩ := exists_orank_eq (A := A) hj
    have hbe := hbit e
    rw [bitIx_iff, bitIx_iff, he] at hbe
    have hne : (e ≠ i) ↔ (j ≠ orank i) := by
      rw [← he]
      exact not_congr orank_inj_iff.symm
    refine Bool.eq_iff_iff.mpr ?_
    rw [Bool.and_eq_true, decide_eq_true_eq, hbe]
    exact and_congr Iff.rfl hne
  · have hbig : ∀ y : A, (orank y).testBit j = false := fun y =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (orank_lt_card y)
        (le_trans (le_of_lt Nat.lt_two_pow_self)
          (Nat.pow_le_pow_right (by norm_num) (by omega))))
    rw [hbig x', hbig x]
    simp

/-- **Clearing a one makes the number smaller** – so a recursion on “clear the
lowest one” terminates, which is what the level-3 table's induction rests on. -/
theorem orank_lt_of_clearLow {x x' : A} (h : ClearLow x x') : orank x' < orank x := by
  obtain ⟨i, hi, -, hbit⟩ := h
  rw [bitIx_iff] at hi
  refine Nat.lt_of_testBit (orank i) ?_ hi fun j hj => ?_
  · have hii := hbit i
    rw [bitIx_iff, bitIx_iff] at hii
    simp only [ne_eq, not_true_eq_false, and_false, iff_false, Bool.not_eq_true] at hii
    exact hii
  · by_cases hj' : j < Nat.card A
    · obtain ⟨e, he⟩ := exists_orank_eq (A := A) hj'
      have hbe := hbit e
      rw [bitIx_iff, bitIx_iff, he] at hbe
      have hne : e ≠ i := fun hc => by rw [hc] at he; omega
      refine Bool.eq_iff_iff.mpr ?_
      rw [hbe]
      exact ⟨fun hc => hc.1, fun hc => ⟨hc, hne⟩⟩
    · have hbig : ∀ y : A, (orank y).testBit j = false := fun y =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (orank_lt_card y)
          (le_trans (le_of_lt Nat.lt_two_pow_self)
            (Nat.pow_le_pow_right (by norm_num) (by omega))))
      rw [hbig x', hbig x]

/-- **The lowest one can always be cleared**: the result is smaller, hence a
rank. -/
theorem exists_clearLow [Nonempty A] {x : A} (hx : orank x ≠ 0) : ∃ x' : A, ClearLow x x' := by
  classical
  have hex : ∃ i : ℕ, (orank x).testBit i = true := by
    by_contra hc
    refine hx (Nat.eq_of_testBit_eq fun i => ?_)
    rw [Nat.zero_testBit]
    simpa using not_exists.mp hc i
  set i₀ := Nat.find hex with hi₀
  have hset : (orank x).testBit i₀ = true := Nat.find_spec hex
  have hlow : ∀ j, j < i₀ → (orank x).testBit j = false := fun j hj => by
    simpa using Nat.find_min hex hj
  -- the value with that bit cleared is smaller
  have hbits : ∀ j, (Nat.ldiff (orank x) (2 ^ i₀)).testBit j
      = ((orank x).testBit j && decide (j ≠ i₀)) := by
    intro j
    rw [Nat.testBit_ldiff, Nat.testBit_two_pow]
    by_cases hj : i₀ = j <;> simp [hj, Ne.symm]
  have hlt : Nat.ldiff (orank x) (2 ^ i₀) < orank x := by
    refine Nat.lt_of_testBit i₀ ?_ hset fun j hj => ?_
    · rw [hbits]
      simp
    · rw [hbits, decide_eq_true (by omega), Bool.and_true]
  obtain ⟨x', hx'⟩ := exists_orank_eq (A := A) (lt_trans hlt (orank_lt_card x))
  -- the index of the lowest one is a position, hence an element
  have hi₀lt : i₀ < Nat.card A :=
    lt_of_lt_of_le (lt_of_not_ge fun hc => by
      rw [testBit_orank_eq_false hc] at hset
      exact absurd hset (by simp)) (le_of_lt posCount_lt_card)
  obtain ⟨e, he⟩ := exists_orank_eq (A := A) hi₀lt
  refine ⟨x', e, by rw [bitIx_iff, he]; exact hset, fun j hj => ?_, fun j => ?_⟩
  · rw [bitIx_iff]
    have : orank j < i₀ := by rw [← he]; exact orank_lt_orank hj
    simp [hlow (orank j) this]
  · rw [bitIx_iff, bitIx_iff, hx', hbits, Bool.and_eq_true, decide_eq_true_eq]
    exact and_congr Iff.rfl (by rw [← he]; exact not_congr orank_inj_iff)

end ClearLow

/-! ### Place values, in the index naming -/

section PowIx

variable {A : Type} [LinearOrder A] [Finite A]

/-- **`p` is the place value of the index `i`**: its only bit is at `i`. What
`DescriptiveComplexity.powArithDef` had to prove in `FO(≤, +, ×)` is, in the
index naming, this one line. -/
def IsPowIx (i p : A) : Prop := ∀ j : A, (BitIx j p ↔ j = i)

/-- **What a place value is worth.** -/
theorem orank_of_isPowIx {i p : A} (hi : orank i < posCount A) (h : IsPowIx i p) :
    orank p = 2 ^ orank i := by
  haveI : Nonempty A := ⟨i⟩
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_two_pow]
  by_cases hj : j < Nat.card A
  · obtain ⟨e, he⟩ := exists_orank_eq (A := A) hj
    have hbe := h e
    rw [bitIx_iff, he] at hbe
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_eq, hbe, ← he]
    exact ⟨fun hc => by rw [hc], fun hc => orank_inj hc.symm⟩
  · have h1 : (orank p).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (orank_lt_card p)
        (le_trans (le_of_lt Nat.lt_two_pow_self)
          (Nat.pow_le_pow_right (by norm_num) (by omega))))
    have h2 : orank i ≠ j := by
      have := lt_of_lt_of_le hi (le_of_lt posCount_lt_card)
      omega
    rw [h1, decide_eq_false h2]

/-- **Every position has its place value**, the two being the two namings of the
same thing. -/
theorem exists_isPowIx {i : A} (hi : orank i < posCount A) : ∃ p : A, IsPowIx i p := by
  obtain ⟨p, hp⟩ := exists_isPos (A := A) hi
  refine ⟨p, fun j => ?_⟩
  rw [bitIx_iff, hp, Nat.testBit_two_pow]
  exact ⟨fun hc => orank_inj (by simpa using (decide_eq_true_eq.mp hc).symm),
    fun hc => by rw [hc]; simp⟩

end PowIx

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **Clearing the lowest one is first-order in the bit logic.** -/
theorem bitDef_clearLow (x x' : α) :
    BitDef (L := L) fun _ _ _ _ _ v => ClearLow (v x) (v x') := by
  have hlow : BitDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u => ∀ j, j < u (Sum.inr 0) → ¬ BitIx j (u (Sum.inl x))) :=
    ((bitDef_lt (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1) (Sum.inr 0) (Sum.inl (Sum.inr 0))).imp
      (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl x))).not).all
  have hcopy : BitDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u => ∀ j, (BitIx j (u (Sum.inl x')) ↔
        (BitIx j (u (Sum.inl x)) ∧ j ≠ u (Sum.inr 0)))) :=
    ((bitDef_bit (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1) (Sum.inr 0) (Sum.inl (Sum.inl x'))).iff
      ((bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl x))).and
        (bitDef_eq (Sum.inr 0) (Sum.inl (Sum.inr 0))).not)).all
  refine (((bitDef_bit (Sum.inr 0) (Sum.inl x)).and (hlow.and hcopy)).ex).congr
    fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

/-- **Being a place value is first-order in the bit logic** – one quantifier and
two atoms, where the other naming needed a two-element certificate. -/
theorem bitDef_isPowIx (i p : α) :
    BitDef (L := L) fun _ _ _ _ _ v => IsPowIx (v i) (v p) := by
  refine (((bitDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl p)).iff
    (bitDef_eq (Sum.inr 0) (Sum.inl i))).all).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

end Definability

end BitSum

end DescriptiveComplexity
