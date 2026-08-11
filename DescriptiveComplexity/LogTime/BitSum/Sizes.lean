/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Bits

/-!
# The three sizes of the Bit Sum Lemma, and that they fit

`DescriptiveComplexity.TimesBitDef` – multiplication of ranks in the bit logic,
the last step between the machine model and AC⁰ – rests on counting the
ones of a `P`-bit word, `P` being the number of bit positions
(`DescriptiveComplexity.posCount`). The count is done in three nested packings,
and each of them has to *fit in one element*, that is, below the place value
`2 ^ (P - 1)`, which is the only size a universe is guaranteed to have room for.
This file fixes the three sizes and proves that they fit, with no formula and no
structure in sight: it is the arithmetic that decides whether the packings of
the Bit Sum Lemma exist at all.

## The sizes

* **Level 1** cuts the `P` positions into blocks of
  `DescriptiveComplexity.BitSum.lvl1Block` positions and keeps, in each block,
  the number of ones below it – a number `≤ P`, so a field of
  `DescriptiveComplexity.BitSum.lvl1Width` bits
  (`DescriptiveComplexity.BitSum.lt_two_pow_lvl1Width`). The block is *twice*
  the field, so the packing occupies half the tape and its top bit stays below
  the top position.
* **Level 2** does the same one size down, inside a single block: sub-blocks of
  `DescriptiveComplexity.BitSum.lvl2Block` positions, with a field of
  `DescriptiveComplexity.BitSum.lvl2Width` bits holding a number `≤ lvl1Block`
  (`DescriptiveComplexity.BitSum.lvl1Block_lt_two_pow_lvl2Width`).
* **Level 3** counts the ones of one sub-block by a *table indexed by its
  value*: `lvl2Block + 1` sections of `2 ^ lvl2Block` bits each. That the table
  fits is `DescriptiveComplexity.BitSum.table_lt`, and it is the inequality the
  whole design turns on.

## Why two levels cannot do it

Level 1 needs its field to hold `P`, so `2 ^ lvl1Block > P`; a table indexed by
the value of a level-1 block would need `(lvl1Block + 1) · 2 ^ lvl1Block < P`.
The two are contradictory, which is the arithmetic form of the packing
obstruction: a level's items and its fields are paired by
co-location, and a level whose fields are wider than the gap between its items
cannot be co-located. Three levels are compatible because the table is indexed
by a *sub*-block, whose value is quadratic in `lvl1Width` and so far below `P`.

## The threshold

Everything holds once `2 ^ 20 ≤ P`, which is
`DescriptiveComplexity.BitSum.le_posCount_of_card` in terms of the universe: a
universe with more than `2 ^ (2 ^ 20 - 1)` elements. The bound is crude on
purpose – it is discharged once and for all by
`DescriptiveComplexity.BitDef.of_large` (`LogTime/Small.lean`), which turns a
statement about the large universes into a statement about all of them, so
nothing downstream carries it.
-/

namespace DescriptiveComplexity

namespace BitSum

/-! ### Two facts about `Nat.size` -/

/-- The width of a number is at most the number. -/
theorem size_le_self (m : ℕ) : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self

/-- A number of `k` bits is at least `2 ^ (k - 1)`. -/
theorem two_pow_size_pred_le {m : ℕ} (hm : 0 < m) : 2 ^ (Nat.size m - 1) ≤ m :=
  Nat.lt_size.mp (by have := Nat.size_pos.mpr hm; omega)

/-- …and less than twice itself. -/
theorem two_pow_size_le {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m := by
  have hpos : 0 < Nat.size m := Nat.size_pos.mpr hm
  have h := two_pow_size_pred_le hm
  have hsplit : (2 : ℕ) ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-! ### The three sizes -/

/-- **The width of a level-1 field**: enough bits to hold a count of ones, which
is at most the number of positions. -/
def lvl1Width (P : ℕ) : ℕ := Nat.size P

/-- **The length of a level-1 block**: twice the field, so that the packing uses
half the tape and stays below the top position. -/
def lvl1Block (P : ℕ) : ℕ := 2 * lvl1Width P

/-- **The width of a level-2 field**: enough bits to hold a count of ones within
one level-1 block. -/
def lvl2Width (P : ℕ) : ℕ := Nat.size (lvl1Block P)

/-- **The length of a level-2 sub-block**: twice its field, for the same
reason. -/
def lvl2Block (P : ℕ) : ℕ := 2 * lvl2Width P

/-- **A level-1 field holds a count of ones**, there being at most `P` of them. -/
theorem lt_two_pow_lvl1Width (P : ℕ) : P < 2 ^ lvl1Width P := Nat.lt_size_self P

/-- **A level-2 field holds a count of ones of one block.** -/
theorem lvl1Block_lt_two_pow_lvl2Width (P : ℕ) : lvl1Block P < 2 ^ lvl2Width P :=
  Nat.lt_size_self _

/-! ### That they fit -/

/-- One doubling swallows the growth of a cube, from `21` on: the arithmetic
core of the induction below. -/
theorem cubic_step {t : ℕ} (ht : 21 ≤ t) : 240 * t ^ 2 + 240 * t + 79 ≤ 80 * t ^ 3 := by
  have hsq : t ≤ t ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left t (by omega)
  have hone : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcube : 1680 * t ^ 2 ≤ 80 * t ^ 3 := by
    have hrw : 80 * t ^ 3 = 80 * t * t ^ 2 := by ring
    rw [hrw]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- The growth fact the three sizes rest on: a cube is eventually far below a
power of two. `21` is where `80 s³ + 1 < 2 ^ (s - 1)` starts to hold, and it is
the only place a concrete number is chosen. -/
theorem cube_lt_two_pow : ∀ {s : ℕ}, 21 ≤ s → 80 * s ^ 3 + 1 < 2 ^ (s - 1) := by
  have key : ∀ k : ℕ, 80 * (k + 21) ^ 3 + 1 < 2 ^ (k + 20) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hpow : (2 : ℕ) ^ (k + 1 + 20) = 2 * 2 ^ (k + 20) := by
        rw [show k + 1 + 20 = (k + 20) + 1 by omega, pow_succ]
        ring
      have hc := cubic_step (t := k + 21) (by omega)
      have hexp : 80 * (k + 1 + 21) ^ 3
          = 80 * (k + 21) ^ 3 + 240 * (k + 21) ^ 2 + 240 * (k + 21) + 80 := by
        rw [show k + 1 + 21 = (k + 21) + 1 by omega]
        ring
      omega
  intro s hs
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 21 := ⟨s - 21, by omega⟩
  have hk := key k
  rwa [show k + 21 - 1 = k + 20 by omega]

/-- Above the threshold, a level-1 block is a negligible part of the tape – the
form in which the growth fact is used three times below. -/
theorem lvl1Block_lt_two_pow_pred {P : ℕ} (hP : 2 ^ 20 ≤ P) :
    lvl1Block P < 2 ^ (Nat.size P - 1) := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hcube := cube_lt_two_pow hs
  have hs3 : Nat.size P ≤ Nat.size P ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [lvl1Block, lvl1Width]
  omega

/-- **A level-1 block fits on the tape**, with room to spare. -/
theorem lvl1Block_lt {P : ℕ} (hP : 2 ^ 20 ≤ P) : lvl1Block P < P :=
  lt_of_lt_of_le (lvl1Block_lt_two_pow_pred hP) (two_pow_size_pred_le (by omega))

/-- **A level-2 sub-block is shorter than a level-1 block**, so the second
packing really does sit inside the first. -/
theorem lvl2Block_lt_lvl1Block {P : ℕ} (hP : 2 ^ 20 ≤ P) : lvl2Block P < lvl1Block P := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hsize : lvl2Width P ≤ Nat.size P - 1 :=
    Nat.size_le.mpr (lvl1Block_lt_two_pow_pred hP)
  rw [lvl2Block, lvl1Block, lvl1Width]
  omega

/-- **The level-3 table fits in one element**: `lvl2Block + 1` sections of
`2 ^ lvl2Block` bits, all below the top position. This is the inequality that
makes the three-level design exist, and the one that fails for two levels. -/
theorem table_lt {P : ℕ} (hP : 2 ^ 20 ≤ P) :
    (lvl2Block P + 1) * 2 ^ lvl2Block P < P - 1 := by
  set s := Nat.size P with hsdef
  have hs : 21 ≤ s := Nat.lt_size.mpr hP
  -- the level-2 field is narrow: `2 ^ lvl2Width ≤ 4 s`
  have hu : 2 ^ lvl2Width P ≤ 4 * s := by
    have h := two_pow_size_le (m := lvl1Block P) (by rw [lvl1Block, lvl1Width]; omega)
    rw [lvl2Width]
    rw [lvl1Block, lvl1Width] at h ⊢
    omega
  -- so the table has at most `16 s²` bits per section
  have hpow : 2 ^ lvl2Block P ≤ 16 * s ^ 2 := by
    have : (2 : ℕ) ^ lvl2Block P = 2 ^ lvl2Width P * 2 ^ lvl2Width P := by
      rw [lvl2Block, ← pow_add]
      congr 1
      omega
    calc 2 ^ lvl2Block P = 2 ^ lvl2Width P * 2 ^ lvl2Width P := this
      _ ≤ (4 * s) * (4 * s) := Nat.mul_le_mul hu hu
      _ = 16 * s ^ 2 := by ring
  -- and at most `5 s` sections
  have hsec : lvl2Block P + 1 ≤ 5 * s := by
    have h1 : lvl2Width P ≤ lvl1Block P := size_le_self _
    rw [lvl2Block, lvl1Block, lvl1Width] at *
    omega
  have hprod : (lvl2Block P + 1) * 2 ^ lvl2Block P ≤ 80 * s ^ 3 := by
    calc (lvl2Block P + 1) * 2 ^ lvl2Block P ≤ (5 * s) * (16 * s ^ 2) :=
          Nat.mul_le_mul hsec hpow
      _ = 80 * s ^ 3 := by ring
  have hcube := cube_lt_two_pow hs
  have hlow : 2 ^ (s - 1) ≤ P := two_pow_size_pred_le (by omega)
  omega

/-- A sub-block is at least two positions long. -/
theorem two_le_lvl2Block {P : ℕ} (hP : 2 ^ 20 ≤ P) : 2 ≤ lvl2Block P := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hpos : 0 < lvl2Width P := by
    rw [lvl2Width]
    refine Nat.size_pos.mpr ?_
    rw [lvl1Block, lvl1Width]
    omega
  rw [lvl2Block]
  omega

/-- A sub-block, and the one after it, leave room below the top position. -/
theorem lvl2Block_succ_lt {P : ℕ} (hP : 2 ^ 20 ≤ P) : lvl2Block P + 1 < P := by
  have h1 := lvl2Block_lt_lvl1Block hP
  have h2 := lvl1Block_lt hP
  omega

/-- **A sub-block's worth of values outnumbers the positions' own width**: what
the level-3 table's capacity condition needs on top of
`DescriptiveComplexity.BitSum.table_lt`. -/
theorem size_le_two_pow_lvl2Block (P : ℕ) : Nat.size P ≤ 2 ^ lvl2Block P := by
  have h1 : lvl1Block P < 2 ^ lvl2Width P := lvl1Block_lt_two_pow_lvl2Width P
  have h2 : (2 : ℕ) ^ lvl2Width P ≤ 2 ^ lvl2Block P :=
    Nat.pow_le_pow_right (by norm_num) (by rw [lvl2Block]; omega)
  rw [lvl1Block, lvl1Width] at h1
  omega

/-- A block is at least two positions long. -/
theorem two_le_lvl1Block {P : ℕ} (hP : 2 ^ 20 ≤ P) : 2 ≤ lvl1Block P := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  rw [lvl1Block, lvl1Width]
  omega

/-- A block, and the position after it, leave room below the top. -/
theorem lvl1Block_succ_lt {P : ℕ} (hP : 2 ^ 20 ≤ P) : lvl1Block P + 1 < P := by
  have h1 := lvl1Block_lt_two_pow_pred hP
  have h2 := two_pow_size_pred_le (m := P) (by omega)
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hcube := cube_lt_two_pow hs
  have hs3 : Nat.size P ≤ Nat.size P ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [lvl1Block, lvl1Width] at *
  omega

/-- **A level-1 field holds a count of ones**, in the form the running sum wants:
the number of positions is below a block's worth of values. -/
theorem lt_two_pow_lvl1Block (P : ℕ) : P < 2 ^ lvl1Block P :=
  lt_of_lt_of_le (lt_two_pow_lvl1Width P)
    (Nat.pow_le_pow_right (by norm_num) (by rw [lvl1Block]; omega))

/-- A block is shorter than a sub-block's worth of values – what level 2 asks of
the word it is given. -/
theorem lvl1Block_lt_two_pow_lvl2Block (P : ℕ) : lvl1Block P < 2 ^ lvl2Block P :=
  lt_of_lt_of_le (lvl1Block_lt_two_pow_lvl2Width P)
    (Nat.pow_le_pow_right (by norm_num) (by rw [lvl2Block]; omega))

/-- …and so is a tail of two blocks, which is what level 1 hands to level 2. -/
theorem two_lvl1Block_lt_two_pow_lvl2Block {P : ℕ} (hP : 2 ^ 20 ≤ P) :
    2 * lvl1Block P + 2 < 2 ^ lvl2Block P := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hL : 42 ≤ lvl1Block P := by rw [lvl1Block, lvl1Width]; omega
  have h1 : lvl1Block P < 2 ^ lvl2Width P := lvl1Block_lt_two_pow_lvl2Width P
  have h2 : (2 : ℕ) ^ lvl2Block P = 2 ^ lvl2Width P * 2 ^ lvl2Width P := by
    rw [lvl2Block, two_mul, pow_add]
  have h3 : lvl1Block P * lvl1Block P ≤ 2 ^ lvl2Width P * 2 ^ lvl2Width P :=
    Nat.mul_le_mul (le_of_lt h1) (le_of_lt h1)
  have h4 : 2 * lvl1Block P + 2 < lvl1Block P * lvl1Block P := by nlinarith
  omega

/-- **There is room for a tail**: three blocks and two sub-blocks fit below the
top position with room to spare, which is what level 1's last chunk needs. -/
theorem lvl1_room {P : ℕ} (hP : 2 ^ 20 ≤ P) :
    3 * lvl1Block P + 2 * lvl2Block P + 4 < P := by
  have hs : 21 ≤ Nat.size P := Nat.lt_size.mpr hP
  have hcube := cube_lt_two_pow hs
  have hlow : 2 ^ (Nat.size P - 1) ≤ P := two_pow_size_pred_le (by omega)
  have hlt : lvl2Block P < lvl1Block P := lvl2Block_lt_lvl1Block hP
  have hs3 : Nat.size P ≤ Nat.size P ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [lvl1Block, lvl1Width] at *
  omega

/-! ### The threshold, on the universe -/

section Universe

variable {A : Type} [LinearOrder A] [Finite A]

/-- **What the threshold asks of a universe**: more than `2 ^ (2 ^ 20 - 1)`
elements. Every statement of the construction is proved for these and lifted to
all universes by `DescriptiveComplexity.BitDef.of_large`, so the bound is never
seen again. -/
theorem le_posCount_of_card (h : 2 ^ (2 ^ 20 - 1) < Nat.card A) : 2 ^ 20 ≤ posCount A := by
  have := (two_pow_lt_card_iff_lt_posCount (A := A) (2 ^ 20 - 1)).mp h
  omega

end Universe

end BitSum

end DescriptiveComplexity
