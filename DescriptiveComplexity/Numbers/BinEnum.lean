/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.Binary
import DescriptiveComplexity.Numbers.BinRel

/-!
# Binary numbers on enumerated positions

What an *encoder* of binary numbers needs, once and for all. An encoded
universe lays its bit positions out as the image of an enumeration
`e : Fin N → A` that is injective, hits exactly the positions, and reflects
the order (`DescriptiveComplexity.BinEnum`). Then

* the rank of a position is its index (`DescriptiveComplexity.BinEnum.bitRank_eq`);
* the decoded number is the plain sum of place values
  (`DescriptiveComplexity.BinEnum.binNum_eq_sum`);
* a set of positions carrying the `Nat.testBit` digits of a number that fits
  decodes to that number (`DescriptiveComplexity.BinEnum.binNum_eq_of_testBit`).

The last statement is the one an encoding's faithfulness proof uses: the
encoder writes `w.testBit p` at the position of index `p`, and the abstract
semantics reads `w` back. Whatever else the universe holds – items, vertices,
facts – plays no part.
-/

namespace DescriptiveComplexity

variable {A : Type} {N : ℕ}

/-- The positions of a universe, enumerated in increasing order: the
enumeration is injective, its range is the set of positions, and it reflects
the order. -/
structure BinEnum (Le : A → A → Prop) (Posn : A → Prop) (e : Fin N → A) : Prop where
  /-- Distinct indices are distinct positions. -/
  injective : Function.Injective e
  /-- The positions are exactly the enumerated elements. -/
  posn_iff : ∀ q, Posn q ↔ ∃ p, q = e p
  /-- The order of the positions is the order of their indices. -/
  le_iff : ∀ p p', Le (e p) (e p') ↔ p ≤ p'

namespace BinEnum

variable {Le : A → A → Prop} {Posn : A → Prop} {e : Fin N → A}

/-- The rank of a position is its index. -/
theorem bitRank_eq (h : BinEnum Le Posn e) (p : Fin N) : bitRank Le Posn (e p) = (p : ℕ) := by
  classical
  have hset : {q : A | Posn q ∧ Le q (e p) ∧ q ≠ e p} = e '' ↑(Finset.Iio p) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_Iio, Set.mem_Iio]
    constructor
    · rintro ⟨hq, hle, hne⟩
      obtain ⟨p', rfl⟩ := (h.posn_iff q).mp hq
      exact ⟨p', lt_of_le_of_ne ((h.le_iff _ _).mp hle) fun hp => hne (hp ▸ rfl), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(h.posn_iff _).mpr ⟨x, rfl⟩, (h.le_iff _ _).mpr (le_of_lt hx),
        fun hp => ne_of_lt hx (h.injective hp)⟩
  unfold bitRank
  rw [hset, Set.ncard_image_of_injective _ h.injective, Set.ncard_coe_finset, Fin.card_Iio]

open Classical in
/-- The decoded number is the sum of the place values of its bits. -/
theorem binNum_eq_sum (h : BinEnum Le Posn e) (b : A → Prop) :
    binNum Le Posn b = ∑ p : Fin N, if b (e p) then 2 ^ (p : ℕ) else 0 := by
  have hset : {q : A | Posn q ∧ b q} = e '' ↑(Finset.univ.filter fun p : Fin N => b (e p)) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hq, hb⟩
      obtain ⟨p, rfl⟩ := (h.posn_iff q).mp hq
      exact ⟨p, hb, rfl⟩
    · rintro ⟨p, hb, rfl⟩
      exact ⟨(h.posn_iff _).mpr ⟨p, rfl⟩, hb⟩
  unfold binNum
  rw [hset, finsum_mem_image h.injective.injOn,
    finsum_mem_congr rfl fun p _ => by rw [h.bitRank_eq p], finsum_mem_coe_finset,
    Finset.sum_filter]

/-- **The decoding.** A set of positions carrying the binary digits of a number
that fits in `N` positions decodes to that number. -/
theorem binNum_eq_of_testBit (h : BinEnum Le Posn e) (w : ℕ) (hw : w < 2 ^ N) (b : A → Prop)
    (hb : ∀ p : Fin N, b (e p) ↔ w.testBit (p : ℕ)) : binNum Le Posn b = w := by
  classical
  have hval : binValue (Fin N) (binEncode (Fin N) w) = w :=
    binValue_binEncode (by simpa using hw)
  rw [h.binNum_eq_sum, ← hval, binValue]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : w.testBit (p : ℕ) <;> simp [binEncode, hb p, hp]

/-- The universe `Fin N`, every element a position, in its own order. -/
theorem fin {Le : Fin N → Fin N → Prop} (hle : ∀ a b, Le a b ↔ a ≤ b) :
    BinEnum Le (fun _ => True) (id : Fin N → Fin N) where
  injective := Function.injective_id
  posn_iff q := ⟨fun _ => ⟨q, rfl⟩, fun _ => trivial⟩
  le_iff := hle

end BinEnum

/-- On the universe `Fin N`, ordered as usual and with every element a
position, the `Nat.testBit` digits of a number below `2 ^ N` decode to it. -/
theorem binNum_fin_of_testBit {N : ℕ} {Le : Fin N → Fin N → Prop}
    (hle : ∀ a b, Le a b ↔ a ≤ b) (w : ℕ) (hw : w < 2 ^ N) (b : Fin N → Prop)
    (hb : ∀ p : Fin N, b p ↔ w.testBit (p : ℕ)) : binNum Le (fun _ => True) b = w :=
  (BinEnum.fin hle).binNum_eq_of_testBit w hw b hb

end DescriptiveComplexity
