/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Sizes
import DescriptiveComplexity.LogTime.BitLogic

/-!
# Co-location: the one device the Bit Sum Lemma is built out of

Every packing of the Bit Sum Lemma has to answer the same question – *given the
item, where is its field?* – and the answer is never “compute the product of the
item's number with the field width”, which is exactly what a logic without
multiplication cannot do. It is always:

> **Guess the boundaries, and put each item's field at the item.** A set of
> positions is one element; “the next boundary is `g` further on” is `PLUS` on
> indices, which the index naming makes free; and if the walk over items *is* the
> walk over boundaries, no index is ever computed from an item.

This file is that device, once, for the whole construction: the boundary set
(`DescriptiveComplexity.BitSum.IsBlockSet`) and the reader that takes a field
out of an element (`DescriptiveComplexity.BitSum.WindowAt`). `LogTime/Pow.lean`
is the same pattern with a *doubling* gap, written before it was worth factoring
out; here the gap is constant, and that makes “consecutive boundaries” a plain
addition instead of a “nothing in between” quantifier.

## The two notions

* `DescriptiveComplexity.BitSum.WindowAt b e x m`: `m` is the number written in
  the bits of `x` from the index `b` (included) to the index `e` (excluded). It
  is `DescriptiveComplexity.FieldAt` read in the *index* naming – a bit-level
  statement rather than a division with remainder – and its semantics is
  `DescriptiveComplexity.BitSum.windowAt_iff`. Every layout in the construction
  is stated with it, and no bit is touched again.
* `DescriptiveComplexity.BitSum.IsBlockSet g B`: the bits of `B` are exactly the
  multiples of `g` that are not the top position. Three local conditions pin it
  (`DescriptiveComplexity.BitSum.bitIx_iff_of_isBlockSet`), and the downward one
  – every non-zero boundary has a boundary `g` below it – is what rules out a
  set that starts somewhere other than `0`.

## What is not here, and why

There is no “consecutive boundaries” relation: with a constant gap, `b` and `b'`
are consecutive exactly when `orank b + orank g = orank b'`, and that is an atom.
The **counter field** – a second element carrying, in the field the same
boundaries delimit, the number of the boundary – is the other half of the device
and comes with the level it is first needed at.
-/

namespace DescriptiveComplexity

namespace BitSum

/-! ### Windows, in `ℕ` -/

/-- **What a window reads**: the bits of `x / 2 ^ a % 2 ^ w` are those of `x`
from `a` up, and nothing from `w` on. -/
theorem testBit_window (x a w k : ℕ) :
    (x / 2 ^ a % 2 ^ w).testBit k = (decide (k < w) && x.testBit (a + k)) := by
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

/-! ### Windows of an element -/

section Window

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The window of `x` between the indices `b` and `e`**, read as the number
`m`: the bits of `m` are those of `x` shifted down by `b`, and `m` has none at
or above the width. Stated bit by bit, so that it is an atom-for-atom formula of
the bit logic (`DescriptiveComplexity.BitSum.bitDef_windowAt`). -/
def WindowAt (b e x m : A) : Prop :=
  (∀ k k' : A, orank b + orank k = orank k' → k' < e → (BitIx k' x ↔ BitIx k m)) ∧
    ∀ k : A, (∀ k' : A, orank b + orank k = orank k' → e ≤ k') → ¬ BitIx k m

/-- **What a window is worth**: at a window of width `w`, the number read is the
`w` bits of `x` above the index `b`. -/
theorem windowAt_iff {b e x m : A} {w : ℕ} (hw : orank b + w = orank e) :
    WindowAt b e x m ↔ orank m = orank x / 2 ^ orank b % 2 ^ w := by
  have : Nonempty A := ⟨b⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_window]
    by_cases hi : i < Nat.card A
    · obtain ⟨k, hk⟩ := exists_orank_eq (A := A) hi
      by_cases hlt : i < w
      · have hlt' : orank b + i < Nat.card A := by
          have := orank_lt_card e
          omega
        obtain ⟨k', hk'⟩ := exists_orank_eq (A := A) hlt'
        have hiff := h1 k k' (by rw [hk, hk']) (lt_of_orank_lt (by rw [hk']; omega))
        rw [bitIx_iff, bitIx_iff, hk, hk'] at hiff
        rw [decide_eq_true hlt, Bool.true_and]
        exact Bool.eq_iff_iff.mpr hiff.symm
      · have hno : ¬ BitIx k m := h2 k fun k' hk' => by
          refine orank_le_iff.mp ?_
          rw [hk] at hk'
          omega
        rw [bitIx_iff, hk, Bool.not_eq_true] at hno
        rw [hno, decide_eq_false (by omega), Bool.false_and]
    · have hcard : Nat.card A ≤ i := by omega
      have hm : (orank m).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (orank_lt_card m)
          (le_trans (le_of_lt (Nat.lt_two_pow_self))
            (Nat.pow_le_pow_right (by norm_num) hcard)))
      have hx : (orank x).testBit (orank b + i) = false :=
        testBit_orank_eq_false (le_trans (le_of_lt posCount_lt_card) (by omega))
      rw [hm, hx, Bool.and_false]
  · intro hm
    refine ⟨fun k k' hsum hlt => ?_, fun k hk => ?_⟩
    · have hlt' : orank k' < orank e := orank_lt_orank hlt
      rw [bitIx_iff, bitIx_iff, hm, testBit_window, decide_eq_true (by omega), Bool.true_and,
        ← hsum]
    · rw [bitIx_iff, hm, testBit_window]
      have hge : w ≤ orank k := by
        by_contra hc
        have hlt' : orank b + orank k < Nat.card A := by
          have := orank_lt_card e
          omega
        obtain ⟨k', hk'⟩ := exists_orank_eq (A := A) hlt'
        have := orank_le_iff.mpr (hk k' hk'.symm)
        omega
      rw [decide_eq_false (by omega), Bool.false_and]
      simp

/-- **A window is always there to be read**: what it reads is at most `x`, hence
a rank of the universe. -/
theorem exists_windowAt {b e x : A} {w : ℕ} (hw : orank b + w = orank e) :
    ∃ m : A, WindowAt b e x m := by
  obtain ⟨m, hm⟩ := exists_orank_eq (A := A) (m := orank x / 2 ^ orank b % 2 ^ w)
    (lt_of_le_of_lt (le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)) (orank_lt_card x))
  exact ⟨m, (windowAt_iff hw).mpr hm⟩

end Window

/-! ### The boundaries of a packing -/

section Blocks

variable {A : Type} [LinearOrder A] [Finite A]

/-- **A set of boundaries at a constant gap `g`**: the least position is one,
every boundary is below the top position, a boundary `g` further on is one, and
every boundary other than the least has one `g` below it. The last condition is
what pins the set down – without it it could start anywhere. -/
def IsBlockSet (g B : A) : Prop :=
  (∀ z : A, orank z = 0 → BitIx z B) ∧
    (∀ b : A, BitIx b B → IsLowIx b) ∧
      (∀ b b' : A, BitIx b B → orank b + orank g = orank b' → IsLowIx b' → BitIx b' B) ∧
        ∀ b : A, BitIx b B → orank b ≠ 0 → ∃ b' : A, orank b' + orank g = orank b ∧ BitIx b' B

/-- **What the conditions pin**: the boundaries are exactly the multiples of the
gap below the top position. -/
theorem bitIx_iff_of_isBlockSet {g B : A} (hg : 0 < orank g) (h : IsBlockSet g B) (b : A) :
    BitIx b B ↔ (orank g ∣ orank b ∧ IsLowIx b) := by
  obtain ⟨hzero, hlow, hup, hdown⟩ := h
  constructor
  · intro hb
    refine ⟨?_, hlow b hb⟩
    have key : ∀ n : ℕ, ∀ c : A, orank c = n → BitIx c B → orank g ∣ orank c := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro c hc hbit
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact ⟨0, by omega⟩
        · obtain ⟨c', hsum, hc'⟩ := hdown c hbit (by omega)
          obtain ⟨q, hq⟩ := ih (orank c') (by omega) c' rfl hc'
          refine ⟨q + 1, ?_⟩
          rw [Nat.mul_succ, ← hq]
          omega
    exact key (orank b) b rfl hb
  · rintro ⟨⟨j, hj⟩, hlowb⟩
    have key : ∀ j : ℕ, ∀ c : A, orank c = orank g * j → IsLowIx c → BitIx c B := by
      intro j
      induction j with
      | zero => exact fun c hc _ => hzero c (by omega)
      | succ j ih =>
        intro c hc hlowc
        have hmono : orank g * j ≤ orank g * (j + 1) := Nat.mul_le_mul_left _ (by omega)
        have hprev : orank g * j < Nat.card A := by
          have := orank_lt_card c
          omega
        obtain ⟨c', hc'⟩ := exists_orank_eq (A := A) hprev
        have hlow' : IsLowIx c' := by
          rw [IsLowIx] at hlowc ⊢
          omega
        exact hup c' c (ih c' hc' hlow') (by rw [hc', hc, Nat.mul_succ]) hlowc
    exact key j b hj hlowb

/-- **A boundary set exists**: the multiples of the gap below the top position
are a bit vector supported below that position, hence a rank
(`DescriptiveComplexity.exists_orank_testBit'`). -/
theorem exists_isBlockSet [Nonempty A] {g : A} (hP : 1 < posCount A) :
    ∃ B : A, IsBlockSet g B := by
  classical
  obtain ⟨B, hB, hB'⟩ := exists_orank_testBit' (A := A) fun i => decide (orank g ∣ i)
  have hbit : ∀ c : A, BitIx c B ↔ (orank g ∣ orank c ∧ IsLowIx c) := by
    intro c
    rw [bitIx_iff]
    by_cases hc : orank c + 1 < posCount A
    · rw [hB _ hc]
      simp only [decide_eq_true_eq, IsLowIx]
      exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
    · rw [hB' _ (by omega)]
      simp only [IsLowIx, Bool.false_eq_true, false_iff, not_and]
      omega
  refine ⟨B, fun z hz => ?_, fun b hb => ((hbit b).mp hb).2, fun b b' hb hsum hlow => ?_,
    fun b hb hne => ?_⟩
  · rw [hbit]
    exact ⟨by rw [hz]; exact Dvd.intro 0 (by omega), by rw [IsLowIx, hz]; omega⟩
  · rw [hbit]
    refine ⟨?_, hlow⟩
    obtain ⟨q, hq⟩ := ((hbit b).mp hb).1
    exact ⟨q + 1, by rw [Nat.mul_succ, ← hq]; omega⟩
  · obtain ⟨⟨q, hq⟩, hlowb⟩ := (hbit b).mp hb
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · omega
      · exact h
    have hlt : orank g * (q - 1) < Nat.card A := by
      have hmono : orank g * (q - 1) ≤ orank g * q := Nat.mul_le_mul_left _ (by omega)
      have := orank_lt_card b
      omega
    obtain ⟨b', hb'⟩ := exists_orank_eq (A := A) hlt
    refine ⟨b', ?_, (hbit b').mpr ⟨⟨q - 1, hb'⟩, ?_⟩⟩
    · rw [hb', hq, ← Nat.mul_succ]
      congr 2
      omega
    · rw [IsLowIx] at hlowb ⊢
      have hmono : orank g * (q - 1) ≤ orank g * q := Nat.mul_le_mul_left _ (by omega)
      omega

end Blocks

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **A window is first-order in the bit logic**: two quantified indices, an
addition, a comparison and two bit reads. -/
theorem bitDef_windowAt (b e x m : α) :
    BitDef (L := L) fun _ _ _ _ _ v => WindowAt (v b) (v e) (v x) (v m) := by
  have hin : BitDef (L := L) (α := α ⊕ Fin 2)
      (fun _ _ _ _ _ u =>
        orank (u (Sum.inl b)) + orank (u (Sum.inr 0)) = orank (u (Sum.inr 1)) →
          u (Sum.inr 1) < u (Sum.inl e) →
            (BitIx (u (Sum.inr 1)) (u (Sum.inl x)) ↔ BitIx (u (Sum.inr 0)) (u (Sum.inl m)))) :=
    (bitDef_plus (Sum.inl b) (Sum.inr 0) (Sum.inr 1)).imp
      ((bitDef_lt (Sum.inr 1) (Sum.inl e)).imp
        ((bitDef_bit (Sum.inr 1) (Sum.inl x)).iff (bitDef_bit (Sum.inr 0) (Sum.inl m))))
  have hout : BitDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u =>
        (∀ a, orank (u (Sum.inl b)) + orank (u (Sum.inr 0)) = orank a →
            u (Sum.inl e) ≤ a) →
          ¬ BitIx (u (Sum.inr 0)) (u (Sum.inl m))) :=
    (((bitDef_plus (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1)
      (Sum.inl (Sum.inl b)) (Sum.inl (Sum.inr 0)) (Sum.inr 0)).imp
        (bitDef_le (Sum.inl (Sum.inl e)) (Sum.inr 0))).all).imp
      (bitDef_bit (Sum.inr 0) (Sum.inl m)).not
  refine (hin.alls.and hout.all).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, WindowAt]
  refine and_congr ?_ ?_
  · exact ⟨fun h k k' => h ![k, k'], fun h w => h (w 0) (w 1)⟩
  · exact Iff.rfl

/-- **A boundary set is first-order in the bit logic.** -/
theorem bitDef_isBlockSet (g B : α) :
    BitDef (L := L) fun _ _ _ _ _ v => IsBlockSet (v g) (v B) := by
  have hzero : BitDef (L := L) (α := α)
      (fun _ _ _ _ _ v => ∀ z, orank z = 0 → BitIx z (v B)) :=
    ((bitDef_isZero (L := L) (α := α ⊕ Fin 1) (Sum.inr 0)).imp
      (bitDef_bit (Sum.inr 0) (Sum.inl B))).all
  have hlow : BitDef (L := L) (α := α)
      (fun _ _ _ _ _ v => ∀ c, BitIx c (v B) → IsLowIx c) :=
    ((bitDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl B)).imp
      (bitDef_isLowIx (Sum.inr 0))).all
  have hup : BitDef (L := L) (α := α) (fun _ _ _ _ _ v => ∀ c c' : _,
      BitIx c (v B) → orank c + orank (v g) = orank c' → IsLowIx c' → BitIx c' (v B)) := by
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 2) (Sum.inr 0) (Sum.inl B)).imp
      ((bitDef_plus (Sum.inr 0) (Sum.inl g) (Sum.inr 1)).imp
        ((bitDef_isLowIx (Sum.inr 1)).imp
          (bitDef_bit (Sum.inr 1) (Sum.inl B))))).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h c c' => h ![c, c'], fun h w => h (w 0) (w 1)⟩
  have hdown : BitDef (L := L) (α := α) (fun _ _ _ _ _ v => ∀ c, BitIx c (v B) →
      orank c ≠ 0 → ∃ c' : _, orank c' + orank (v g) = orank c ∧ BitIx c' (v B)) := by
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl B)).imp
      ((bitDef_isZero (Sum.inr 0)).not.imp
        (((bitDef_plus (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1)
          (Sum.inr 0) (Sum.inl (Sum.inl g)) (Sum.inl (Sum.inr 0))).and
            (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl B)))).ex))).all).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
  exact (hzero.and (hlow.and (hup.and hdown))).congr fun _ _ _ _ _ _ => Iff.rfl

end Definability

end BitSum

end DescriptiveComplexity
