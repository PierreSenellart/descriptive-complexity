/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Columns
import DescriptiveComplexity.LogTime.BitSum.Level1
import DescriptiveComplexity.LogTime.Small

/-!
# `TIMES` from `BSUM`: multiplication of ranks, in the bit logic

The last step of [Immerman 1999][immerman1999descriptive] Thm 1.17(1), and the
one the textbook leaves entirely to the reader: with the Bit Sum Lemma in hand
(`DescriptiveComplexity.BitSum.PopAll`), define `orank x * orank y = orank z`
in `FO(≤, BIT)`. The design gap it closes is recorded in the module docstring
of `DescriptiveComplexity.LogTime.BitSum.Columns`; the certificate here has
three layers, each guessed and pinned locally, none ever computing a product:

* **A column** (`DescriptiveComplexity.BitSum.ColCount`): the word whose ones
  are the pairs of set bits of `x` and `y` meeting at one column – a sub-mask
  of `y`, read off bit by bit – counted by the Bit Sum Lemma.
* **A range of columns** (`DescriptiveComplexity.BitSum.RangeSum`): the
  weighted sum `Σ_t c_{a+t} 2 ^ t` of the columns `[a, e)`, certified by a
  **carry chain**: the remainders of the column-by-column addition, packed one
  field per column into a single element, walked with the boundary set and the
  counter of `LogTime/BitSum/Blocks` and `Counter`, each step one
  `DescriptiveComplexity.BitSum.StepEq` – an addition and a bit of the result.
* **The product** (`DescriptiveComplexity.BitSum.TimesCert`): cut the columns
  into blocks of `g` with `2 ^ g > P`, so a block sum has `2 g` bits and the
  fields of the even (resp. odd) blocks tile an element exactly; one guessed
  element per parity, their windows certified by `RangeSum`, a tail from the
  last boundary to the top of the tape, and **two additions** put the product
  together. A no-overflow clause makes the columns end below the top, which is
  what confines the whole sum to the tape.

Soundness holds for whatever is guessed
(`DescriptiveComplexity.BitSum.rangeSum_sound` takes no size hypothesis), the
sizes are paid once in the completeness half
(`DescriptiveComplexity.BitSum.timesCert_of_eq`, above the threshold of
`LogTime/BitSum/Sizes`), and `DescriptiveComplexity.BitSum.bitDef_times`
discharges the threshold with `DescriptiveComplexity.BitDef.of_large`. The
result, `DescriptiveComplexity.timesBitDef`, is consumed in
`LogTime/Translate.lean`, where it closes `AC⁰ = FO(≤, BIT)` – the machine
model *is* AC⁰.
-/

namespace DescriptiveComplexity

namespace BitSum

/-! ### Two more sizes -/

/-- **The carry chains fit on the tape**: a chain has at most `4 · lvl1Block`
fields (a block, or the tail, which is at most two blocks and change) of
`lvl1Block` bits each, and that is far below the top position. -/
theorem chain_room {P : ℕ} (hP : 2 ^ 20 ≤ P) :
    lvl1Block P * (4 * lvl1Block P + 2) + 2 < P := by
  set s := Nat.size P with hsdef
  have hs : 21 ≤ s := Nat.lt_size.mpr hP
  have hs2 : s * s ≤ s ^ 3 := by
    have h1 : s * s = s ^ 2 := (sq s).symm
    have h2 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hs3 : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) _
  have hprod : lvl1Block P * (4 * lvl1Block P + 2) + 2 ≤ 80 * s ^ 3 := by
    rw [lvl1Block, lvl1Width, ← hsdef]
    have hexp : 2 * s * (4 * (2 * s) + 2) + 2 = 16 * (s * s) + 4 * s + 2 := by ring
    omega
  have hcube := cube_lt_two_pow hs
  have hlow : 2 ^ (s - 1) ≤ P := two_pow_size_pred_le (by omega)
  omega

/-- **Two positions' worth of sums fit in the universe**: what lets the local
additions of a carry chain always name their result. -/
theorem two_posCount_lt_card {A : Type} [LinearOrder A] [Finite A] [Nonempty A]
    (hP : 2 ^ 20 ≤ posCount A) : 2 * posCount A < Nat.card A := by
  set P := posCount A with hPdef
  set s := Nat.size P with hsdef
  have hs : 21 ≤ s := Nat.lt_size.mpr hP
  have hcube := cube_lt_two_pow hs
  have hs3 : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) _
  have hlow : 2 ^ (s - 1) ≤ P := two_pow_size_pred_le (by omega)
  have hup : P < 2 ^ s := Nat.lt_size_self P
  have h2P : 2 * P < 2 ^ (s + 1) := by
    rw [pow_succ]
    omega
  have hexp : (2 : ℕ) ^ (s + 1) ≤ 2 ^ (P - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 2 ^ (P - 1) < Nat.card A :=
    (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
  omega

/-- **The universe is not bigger than its positions can address.** -/
theorem card_le_two_pow_posCount {A : Type} [LinearOrder A] [Finite A] :
    Nat.card A ≤ 2 ^ posCount A := by
  by_contra hc
  have h1 : 2 ^ posCount A < Nat.card A := by omega
  exact absurd ((two_pow_lt_card_iff_lt_posCount (A := A) (posCount A)).mp h1) (lt_irrefl _)

/-! ### One column -/

section Column

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The word of one column**: the bit of `w` at `i` says that `y` has a one
at `i` and `x` a one at the index completing `i` to `j`. Stated bit by bit,
with the complement named by an addition. -/
def ColWord (x y j w : A) : Prop :=
  ∀ i : A, BitIx i w ↔ (BitIx i y ∧ ∃ d : A, orank i + orank d = orank j ∧ BitIx d x)

/-- **What the column word is worth**: exactly
`DescriptiveComplexity.BitSum.colWordN` of the ranks. -/
theorem colWord_iff {x y j w : A} :
    ColWord x y j w ↔ orank w = colWordN (orank x) (orank y) (orank j) := by
  haveI : Nonempty A := ⟨w⟩
  have hylt : ∀ k, Nat.card A ≤ k → (orank y).testBit k = false := fun k hk =>
    testBit_orank_eq_false (le_trans (le_of_lt posCount_lt_card) hk)
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun k => ?_
    rw [testBit_colWordN]
    by_cases hk : k < Nat.card A
    · obtain ⟨i, hi⟩ := exists_orank_eq (A := A) hk
      have hiff := h i
      rw [bitIx_iff, hi] at hiff
      refine Bool.eq_iff_iff.mpr ?_
      rw [hiff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hy, d, hsum, hx⟩
        rw [bitIx_iff, hi] at hy
        rw [bitIx_iff] at hx
        exact ⟨hy, ⟨by omega, by rw [show orank j - k = orank d by omega]; exact hx⟩⟩
      · rintro ⟨hy, hkj, hx⟩
        obtain ⟨d, hdr⟩ := exists_orank_eq (A := A)
          (m := orank j - k) (lt_of_le_of_lt (Nat.sub_le _ _) (orank_lt_card j))
        refine ⟨by rw [bitIx_iff, hi]; exact hy, d, by omega, ?_⟩
        rw [bitIx_iff, hdr]
        exact hx
    · have h1 : (orank w).testBit k = false :=
        testBit_orank_eq_false (le_trans (le_of_lt posCount_lt_card) (by omega))
      rw [h1, hylt k (by omega), Bool.false_and]
  · intro hw i
    rw [bitIx_iff, hw, testBit_colWordN]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hy, hle, hx⟩
      obtain ⟨d, hdr⟩ := exists_orank_eq (A := A)
        (m := orank j - orank i) (lt_of_le_of_lt (Nat.sub_le _ _) (orank_lt_card j))
      refine ⟨hy, d, by omega, ?_⟩
      rw [bitIx_iff, hdr]
      exact hx
    · rintro ⟨hy, d, hsum, hx⟩
      rw [bitIx_iff] at hx
      exact ⟨hy, by omega, by rw [show orank j - orank i = orank d by omega]; exact hx⟩

/-- **The column word exists**: it is a sub-mask of `y`, hence a rank. -/
theorem exists_colWord [Nonempty A] (x y j : A) : ∃ w : A, ColWord x y j w := by
  obtain ⟨w, hw⟩ := exists_orank_eq (A := A)
    (lt_of_le_of_lt (colWordN_le (orank x) (orank y) (orank j)) (orank_lt_card y))
  exact ⟨w, colWord_iff.mpr hw⟩

/-- **The count of one column**: the column word, counted by the Bit Sum
Lemma. -/
def ColCount (x y j n : A) : Prop := ∃ w : A, ColWord x y j w ∧ PopAll w n

/-- **What the column count is worth** – with no condition at all, the Bit Sum
Lemma's soundness being unconditional. -/
theorem colCount_sound {x y j n : A} (h : ColCount x y j n) :
    orank n = colCountN (orank x) (orank y) (posCount A) (orank j) := by
  obtain ⟨w, hw, hp⟩ := h
  rw [popAll_sound hp, colWord_iff.mp hw]
  rfl

/-- **Every column can be counted**, above the threshold of the Bit Sum
Lemma. -/
theorem exists_colCount [Nonempty A] {x y j : A} (hP : 2 ^ 20 ≤ posCount A) :
    ∃ n : A, ColCount x y j n := by
  obtain ⟨w, hw⟩ := exists_colWord x y j
  obtain ⟨n, hn⟩ := exists_popAll (x := w) hP
  exact ⟨n, w, hw, hn⟩

end Column

/-! ### One step of a carry chain -/

section Step

variable {A : Type} [LinearOrder A] [Finite A]

/-- **One step of the carry chain**: the incoming remainder plus the column
count equals twice the outgoing remainder plus the bit of `V` at `t` – stated
with the sum and the double as guessed elements, so that it is two additions,
a bit read and a successor. -/
def StepEq (n r r' t V : A) : Prop :=
  ∃ s d : A, orank r + orank n = orank s ∧ orank r' + orank r' = orank d ∧
    ((BitIx t V ∧ orank d + 1 = orank s) ∨ (¬ BitIx t V ∧ d = s))

omit [Finite A] in
/-- **What a step says**, read on the ranks. -/
theorem stepEq_sound {n r r' t V : A} (h : StepEq n r r' t V) :
    orank r + orank n = 2 * orank r' + ((orank V).testBit (orank t)).toNat := by
  obtain ⟨s, d, hs, hd, hcase⟩ := h
  rcases hcase with ⟨hbit, hds⟩ | ⟨hbit, rfl⟩
  · rw [bitIx_iff] at hbit
    rw [hbit, Bool.toNat_true]
    omega
  · have hbit' : (orank V).testBit (orank t) = false := by
      rw [bitIx_iff, Bool.not_eq_true] at hbit
      exact hbit
    rw [hbit', Bool.toNat_false]
    omega

/-- **A true step is a certificate step**, as soon as the two intermediate
sums are small enough to be ranks. -/
theorem stepEq_intro {n r r' t V : A} (hs : orank r + orank n < Nat.card A)
    (hd : orank r' + orank r' < Nat.card A)
    (h : orank r + orank n = 2 * orank r' + ((orank V).testBit (orank t)).toNat) :
    StepEq n r r' t V := by
  haveI : Nonempty A := ⟨t⟩
  obtain ⟨s, hsr⟩ := exists_orank_eq (A := A) hs
  obtain ⟨d, hdr⟩ := exists_orank_eq (A := A) hd
  refine ⟨s, d, by omega, by omega, ?_⟩
  by_cases hb : (orank V).testBit (orank t) = true
  · refine Or.inl ⟨hb, ?_⟩
    rw [hb, Bool.toNat_true] at h
    omega
  · rw [Bool.not_eq_true] at hb
    refine Or.inr ⟨by rw [bitIx_iff, hb]; simp, ?_⟩
    rw [hb, Bool.toNat_false] at h
    exact orank_inj (by omega)

end Step

/-! ### A range of columns, by a guessed carry chain -/

section Range

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The sum of the columns `[a, e)`, certified**: a gap, its boundary set and
counter, and one element `R` carrying the remainders of the column-by-column
addition, one field per column. The base pins the first column against the
lowest bit of `V`; the step, guarded by the room it needs, pins each next
column against the next bit, the counter naming the column; and the top names
the field of the last column and reads it as the bits of `V` above the range –
with nothing beyond them. -/
def RangeSum (x y a e V : A) : Prop :=
  ∃ g B C R : A,
    orank g ≠ 0 ∧ IsBlockSet g B ∧ IsCounter g B C ∧
      (∀ p p' r : A, orank p = 0 → orank p + orank g = orank p' → WindowAt p p' R r →
        ∃ n : A, ColCount x y a n ∧ StepEq n p r p V) ∧
      (∀ p p' p'' r r' t j : A, BitIx p B → orank p + orank g = orank p' →
        orank p' + orank g = orank p'' → IsLowIx p'' → WindowAt p p' R r →
          WindowAt p' p'' R r' → WindowAt p' p'' C t → orank a + orank t = orank j →
            j < e → ∃ n : A, ColCount x y j n ∧ StepEq n r r' t V) ∧
      (∃ p p' t r m q : A, BitIx p B ∧ orank p + orank g = orank p' ∧ IsLowIx p' ∧
        WindowAt p p' C t ∧ WindowAt p p' R r ∧ orank t + 1 = orank m ∧
          orank a + orank m = orank e ∧ orank m + orank g = orank q ∧
            WindowAt m q V r ∧ ∀ i : A, q ≤ i → ¬ BitIx i V)

/-- **The certificate is sound, whatever was guessed**: the chain equations,
walked from the first column, force `V` to be the weighted sum of the columns
of the range – with no size hypothesis at all. -/
theorem rangeSum_sound {x y a e V : A} (h : RangeSum x y a e V) :
    ∃ m : ℕ, 0 < m ∧ orank a + m = orank e ∧
      orank V = intervalSum (colCountN (orank x) (orank y) (posCount A)) (orank a) m := by
  haveI : Nonempty A := ⟨a⟩
  obtain ⟨g, B, C, R, hg0, hB, hC, hbase, hstep, ptop, ptop', ttop, rtop, mtop, qtop,
    hptopB, hptopsum, hptop'low, hctop, hrtop, htsucc, hae, hmq, hVwin, hVhigh⟩ := h
  have hgpos : 0 < orank g := by omega
  have httop : orank g * orank ttop = orank ptop :=
    counter_eq hgpos hB hC ptop ptop' ttop hptopB hptopsum hptop'low hctop
  -- the invariant: at the boundary of column `k`, the low bits of `V` plus the
  -- remainder are the partial sum
  have key : ∀ k : ℕ, k < orank ttop + 1 → ∀ p p' r : A, orank p = orank g * k →
      orank p + orank g = orank p' → WindowAt p p' R r →
        orank V % 2 ^ (k + 1) + orank r * 2 ^ (k + 1)
          = intervalSum (colCountN (orank x) (orank y) (posCount A)) (orank a) (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro _ p p' r hp hpp hwin
      have hp0 : orank p = 0 := by omega
      obtain ⟨n, hcol, hse⟩ := hbase p p' r hp0 hpp hwin
      have hn := colCount_sound hcol
      have hs := stepEq_sound hse
      rw [hp0] at hs
      have hbit0 : ((orank V).testBit 0).toNat = orank V % 2 := by
        rw [toNat_testBit, pow_zero, Nat.div_one]
      rw [intervalSum_one, pow_one]
      omega
    | succ k ih =>
      intro hk p p' r hp hpp hwin
      -- everything sits below the top boundary, so the guards hold
      have hkle : k + 1 ≤ orank ttop := by omega
      have hple : orank p ≤ orank ptop := by
        rw [hp, ← httop]
        exact Nat.mul_le_mul_left _ hkle
      have hp'low : IsLowIx p' := by
        rw [IsLowIx] at hptop'low ⊢
        omega
      have hplow : IsLowIx p := by
        rw [IsLowIx] at hp'low ⊢
        omega
      -- the boundary below
      have hpk : orank g * k < Nat.card A := by
        have hmono : orank g * k ≤ orank g * (k + 1) := Nat.mul_le_mul_left _ (by omega)
        have := orank_lt_card p
        omega
      obtain ⟨p₀, hp₀⟩ := exists_orank_eq (A := A) hpk
      have hp₀sum : orank p₀ + orank g = orank p := by rw [hp₀, hp, Nat.mul_succ]
      have hp₀low : IsLowIx p₀ := by
        rw [IsLowIx] at hplow ⊢
        omega
      have hpB : BitIx p B := (bitIx_iff_of_isBlockSet hgpos hB p).mpr ⟨⟨k + 1, hp⟩, hplow⟩
      have hp₀B : BitIx p₀ B := (bitIx_iff_of_isBlockSet hgpos hB p₀).mpr ⟨⟨k, hp₀⟩, hp₀low⟩
      -- the windows at the boundary below, and the counter here
      obtain ⟨r₀, hr₀⟩ := exists_windowAt (b := p₀) (e := p) (x := R) (w := orank g)
        (by omega)
      obtain ⟨t, ht⟩ := exists_windowAt (b := p) (e := p') (x := C) (w := orank g)
        (by omega)
      have htval : orank t = k + 1 := by
        have hcnt := counter_eq hgpos hB hC p p' t hpB (by omega) hp'low ht
        refine Nat.eq_of_mul_eq_mul_left hgpos ?_
        omega
      -- the column
      have hjlt : orank a + orank t < Nat.card A := by
        have h1 := orank_lt_card e
        have h2 : orank ttop + 1 ≤ orank mtop := by omega
        rw [htval]
        omega
      obtain ⟨j, hj⟩ := exists_orank_eq (A := A) hjlt
      have hjv : orank j = orank a + (k + 1) := by rw [hj, htval]
      obtain ⟨n, hcol, hse⟩ := hstep p₀ p p' r₀ r t j hp₀B (by omega) (by omega) hp'low
        hr₀ hwin ht (by omega)
        (lt_of_orank_lt (by rw [hjv]; omega))
      have hn := colCount_sound hcol
      rw [hjv] at hn
      have hs := stepEq_sound hse
      rw [htval] at hs
      -- assemble
      have hih := ih (by omega) p₀ p r₀ hp₀ hp₀sum hr₀
      have hmodsucc := mod_two_pow_succ (orank V) (k + 1)
      have hsum := intervalSum_succ (colCountN (orank x) (orank y) (posCount A))
        (orank a) (k + 1)
      rw [← hn] at hsum
      have hE : (orank r₀ + orank n) * 2 ^ (k + 1)
          = (2 * orank r + ((orank V).testBit (k + 1)).toNat) * 2 ^ (k + 1) := by rw [hs]
      have hE1 : (orank r₀ + orank n) * 2 ^ (k + 1)
          = orank r₀ * 2 ^ (k + 1) + orank n * 2 ^ (k + 1) := Nat.add_mul _ _ _
      have hE2 : (2 * orank r + ((orank V).testBit (k + 1)).toNat) * 2 ^ (k + 1)
          = orank r * 2 ^ (k + 1 + 1) + ((orank V).testBit (k + 1)).toNat * 2 ^ (k + 1) := by
        rw [pow_succ]
        ring
      omega
  -- read the top
  have hmval : orank mtop = orank ttop + 1 := by omega
  have hkey := key (orank ttop) (by omega) ptop ptop' rtop (by omega) (by omega) hrtop
  have hVdiv : orank rtop = orank V / 2 ^ (orank ttop + 1) % 2 ^ orank g := by
    have := (windowAt_iff (b := mtop) (e := qtop) (x := V) (m := rtop)
      (w := orank g) (by omega)).mp hVwin
    rw [hmval] at this
    exact this
  have hVhigh' : ∀ i : ℕ, orank ttop + 1 + orank g ≤ i → (orank V).testBit i = false := by
    intro i hi
    by_cases hic : i < Nat.card A
    · obtain ⟨î, hî⟩ := exists_orank_eq (A := A) hic
      have hq : qtop ≤ î := orank_le_iff.mp (by omega)
      have := hVhigh î hq
      rw [bitIx_iff, hî, Bool.not_eq_true] at this
      exact this
    · exact testBit_orank_eq_false (le_trans (le_of_lt posCount_lt_card) (by omega))
  have hVlt : orank V < 2 ^ (orank ttop + 1 + orank g) := lt_two_pow_of_high_bits hVhigh'
  have hVdivlt : orank V / 2 ^ (orank ttop + 1) < 2 ^ orank g := by
    refine (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr ?_
    have hpp : (2 : ℕ) ^ orank g * 2 ^ (orank ttop + 1)
        = 2 ^ (orank ttop + 1 + orank g) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpp]
    exact hVlt
  have hVdiv' : orank V / 2 ^ (orank ttop + 1) = orank rtop := by
    rw [hVdiv, Nat.mod_eq_of_lt hVdivlt]
  have hsplit := Nat.div_add_mod (orank V) (2 ^ (orank ttop + 1))
  have hcomm2 : 2 ^ (orank ttop + 1) * (orank V / 2 ^ (orank ttop + 1))
      = orank rtop * 2 ^ (orank ttop + 1) := by
    rw [hVdiv', Nat.mul_comm]
  exact ⟨orank ttop + 1, by omega, by omega, by omega⟩

/-- **The certificate exists, for the true sum**: with any gap wide enough to
hold a column count in one field and short enough for the chain to fit on the
tape, the remainders of `DescriptiveComplexity.BitSum.carryChain` are packed
into one element and every condition holds by the corresponding chain
equation. -/
theorem rangeSum_of_eq [Nonempty A] {x y a e V : A} {Gv m : ℕ}
    (hP : 2 ^ 20 ≤ posCount A) (hGpos : 0 < Gv) (hPG : posCount A < 2 ^ Gv)
    (hm : 0 < m) (hae : orank a + m = orank e) (hroom : Gv * m + 1 < posCount A)
    (hV : orank V
      = intervalSum (colCountN (orank x) (orank y) (posCount A)) (orank a) m) :
    RangeSum x y a e V := by
  classical
  have hcard := posCount_lt_card (A := A)
  have h2P := two_posCount_lt_card hP
  have hGle : Gv ≤ Gv * m := Nat.le_mul_of_pos_right _ hm
  have hmle : m ≤ Gv * m := Nat.le_mul_of_pos_left _ hGpos
  have hcle : ∀ u : ℕ,
      colCountN (orank x) (orank y) (posCount A) u < posCount A + 1 := fun u => by
    have := colCountN_le (orank x) (orank y) (posCount A) u
    omega
  -- the gap, as an element
  obtain ⟨g, hgr⟩ := exists_orank_eq (A := A) (m := Gv) (by omega)
  have hgpos : 0 < orank g := by omega
  obtain ⟨B, hB⟩ := exists_isBlockSet (A := A) (g := g) (by omega)
  have hcap : posCount A ≤ orank g * 2 ^ orank g := by
    have h1 : (2 : ℕ) ^ Gv ≤ Gv * 2 ^ Gv := Nat.le_mul_of_pos_left _ (by omega)
    rw [hgr]
    omega
  obtain ⟨C, hC⟩ := exists_isCounter hgpos hB hcap
  -- the chain, packed into one element
  have hchain_lt : ∀ t : ℕ,
      carryChain (colCountN (orank x) (orank y) (posCount A)) (orank a) t
        < posCount A + 1 :=
    fun t => carryChain_lt (by omega) fun u _ => hcle _
  have hfields : ∀ t, t < m →
      carryChain (colCountN (orank x) (orank y) (posCount A)) (orank a) t
        < 2 ^ orank g := fun t _ => by
    have := hchain_lt t
    rw [hgr]
    omega
  have hpack_lt : packVal (orank g)
      (fun t => carryChain (colCountN (orank x) (orank y) (posCount A)) (orank a) t) m
        < Nat.card A := by
    refine lt_of_lt_of_le (packVal_lt hfields) ?_
    have hmG : m * orank g ≤ posCount A - 1 := by
      have hc : m * Gv = Gv * m := Nat.mul_comm _ _
      rw [hgr]
      omega
    calc (2 : ℕ) ^ (m * orank g) ≤ 2 ^ (posCount A - 1) :=
          Nat.pow_le_pow_right (by norm_num) hmG
      _ ≤ Nat.card A :=
          le_of_lt ((two_pow_lt_card_iff_lt_posCount _).mpr (by omega))
  obtain ⟨R, hRr⟩ := exists_orank_eq (A := A) hpack_lt
  -- reading a field of the chain
  have hRwin : ∀ (k : ℕ) (p p' r : A), k < m → orank p = orank g * k →
      orank p + orank g = orank p' → WindowAt p p' R r →
        orank r = carryChain (colCountN (orank x) (orank y) (posCount A)) (orank a) k := by
    intro k p p' r hk hp hpp hwin
    rw [(windowAt_iff (w := orank g) (by omega)).mp hwin, hRr, hp,
      Nat.mul_comm (orank g) k]
    exact packVal_window hfields hk
  refine ⟨g, B, C, R, by omega, hB, hC, ?_, ?_, ?_⟩
  · -- the base
    intro p p' r hp0 hpp hwin
    obtain ⟨n, hcol⟩ := exists_colCount (x := x) (y := y) (j := a) hP
    have hn := colCount_sound hcol
    have hnb := hcle (orank a)
    have hrval := hRwin 0 p p' r hm (by omega) hpp hwin
    have hrb := hchain_lt 0
    have hbase0 := carryChain_base
      (h := colCountN (orank x) (orank y) (posCount A)) (a := orank a) hm
    rw [← hV] at hbase0
    refine ⟨n, hcol, stepEq_intro (by omega) (by omega) ?_⟩
    rw [hp0]
    omega
  · -- the step
    intro p p' p'' r r' t j hpB hpp hp'p'' hlow'' hwr hwr' hwc hplus hjlt
    obtain ⟨⟨k, hk⟩, hplow⟩ := (bitIx_iff_of_isBlockSet hgpos hB p).mp hpB
    have hp'low : IsLowIx p' := by
      rw [IsLowIx] at hlow'' ⊢
      omega
    have hp'B : BitIx p' B := hB.2.2.1 p p' hpB (by omega) hp'low
    have hp'val : orank p' = orank g * (k + 1) := by rw [Nat.mul_succ]; omega
    have htval : orank t = k + 1 := by
      have hcnt := counter_eq hgpos hB hC p' p'' t hp'B (by omega) hlow'' hwc
      refine Nat.eq_of_mul_eq_mul_left hgpos ?_
      omega
    have hjv : orank j = orank a + (k + 1) := by rw [← hplus, htval]
    have hkm : k + 1 < m := by
      have := orank_lt_orank hjlt
      omega
    have hrval := hRwin k p p' r (by omega) hk (by omega) hwr
    have hr'val := hRwin (k + 1) p' p'' r' hkm hp'val (by omega) hwr'
    have hrb := hchain_lt k
    have hr'b := hchain_lt (k + 1)
    obtain ⟨n, hcol⟩ := exists_colCount (x := x) (y := y) (j := j) hP
    have hn := colCount_sound hcol
    rw [hjv] at hn
    have hnb := hcle (orank a + (k + 1))
    have hstep := carryChain_step
      (h := colCountN (orank x) (orank y) (posCount A)) (a := orank a) hkm
    rw [← hV] at hstep
    refine ⟨n, hcol, stepEq_intro (by omega) (by omega) ?_⟩
    rw [htval, hrval, hr'val, hn]
    exact hstep
  · -- the top
    have hGm : orank g * (m - 1) + orank g = orank g * m := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hGmP : orank g * m + 1 < posCount A := by rw [hgr]; omega
    obtain ⟨p, hpr⟩ := exists_orank_eq (A := A) (m := orank g * (m - 1)) (by
      have hmono : orank g * (m - 1) ≤ orank g * m := Nat.mul_le_mul_left _ (by omega)
      omega)
    obtain ⟨p', hp'r⟩ := exists_orank_eq (A := A) (m := orank g * m) (by omega)
    have hplow : IsLowIx p := by
      rw [IsLowIx, hpr]
      have hmono : orank g * (m - 1) ≤ orank g * m := Nat.mul_le_mul_left _ (by omega)
      omega
    have hp'low : IsLowIx p' := by
      rw [IsLowIx, hp'r]
      omega
    have hpB : BitIx p B := (bitIx_iff_of_isBlockSet hgpos hB p).mpr ⟨⟨m - 1, hpr⟩, hplow⟩
    obtain ⟨t, ht⟩ := exists_windowAt (b := p) (e := p') (x := C) (w := orank g)
      (by omega)
    have htval : orank t = m - 1 := by
      have hcnt := counter_eq hgpos hB hC p p' t hpB (by omega) hp'low ht
      refine Nat.eq_of_mul_eq_mul_left hgpos ?_
      omega
    obtain ⟨r, hr⟩ := exists_windowAt (b := p) (e := p') (x := R) (w := orank g)
      (by omega)
    have hrval := hRwin (m - 1) p p' r (by omega) hpr (by omega) hr
    obtain ⟨mtop, hmr⟩ := exists_orank_eq (A := A) (m := m) (by omega)
    obtain ⟨q, hq⟩ := exists_orank_eq (A := A) (m := m + orank g) (by rw [hgr]; omega)
    have hVwin : WindowAt mtop q V r := by
      refine (windowAt_iff (w := orank g) (by omega)).mpr ?_
      rw [hrval, hmr, hV, carryChain_last hm,
        Nat.mod_eq_of_lt (hfields (m - 1) (by omega))]
    have hVlt : orank V < 2 ^ (m + orank g) := by
      rw [hV, pow_add]
      refine lt_of_lt_of_le (intervalSum_lt (H := posCount A + 1) (by omega)
        fun u _ => hcle _) ?_
      have h1 : posCount A + 1 ≤ 2 ^ orank g := by rw [hgr]; omega
      have h2 : (posCount A + 1) * 2 ^ m ≤ 2 ^ orank g * 2 ^ m :=
        Nat.mul_le_mul_right _ h1
      have h3 : (2 : ℕ) ^ orank g * 2 ^ m = 2 ^ m * 2 ^ orank g := Nat.mul_comm _ _
      omega
    refine ⟨p, p', t, r, mtop, q, hpB, by omega, hp'low, ht, hr, by omega, by omega,
      by omega, hVwin, ?_⟩
    intro i hqi
    rw [bitIx_iff]
    intro hbit
    have hge : orank q ≤ orank i := orank_le_iff.mpr hqi
    have hfalse : (orank V).testBit (orank i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hVlt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hfalse] at hbit
    exact absurd hbit (by simp)

end Range

/-! ### The product -/

section Times

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The whole certificate for `orank x * orank y = orank z`**: the columns of
the schoolbook product, cut into blocks at a guessed gap; the block sums of the
even blocks written in the tiling fields of one element, those of the odd
blocks in another, each field certified by a carry chain; the columns from the
last boundary to the top of the tape as one more range; and two additions
putting the three parts together. The no-overflow clause keeps every column on
the tape, which is what makes the three parts everything there is. -/
def TimesCert (x y z : A) : Prop :=
  ∃ g g₂ B₂ bl blg bE bO T T' u e' : A,
    orank g ≠ 0 ∧ orank g + orank g = orank g₂ ∧ IsBlockSet g₂ B₂ ∧
      (∀ i d : A, BitIx i y → BitIx d x →
        ∃ jc : A, orank i + orank d = orank jc ∧ (IsLowIx jc ∨ IsTopIx jc)) ∧
      BitIx bl B₂ ∧
      (∀ β β' βe : A, BitIx β B₂ → β < bl → orank β + orank g₂ = orank β' →
        orank β + orank g = orank βe →
          ∃ VE : A, WindowAt β β' bE VE ∧ RangeSum x y β βe VE) ∧
      (∀ i : A, bl ≤ i → ¬ BitIx i bE) ∧
      (∀ β β' βo βo3 : A, BitIx β B₂ → β < bl → orank β + orank g₂ = orank β' →
        orank β + orank g = orank βo → orank βo + orank g₂ = orank βo3 →
          ∃ VO : A, WindowAt βo βo3 bO VO ∧ RangeSum x y βo β' VO) ∧
      (∀ i : A, i < g → ¬ BitIx i bO) ∧
      orank bl + orank g = orank blg ∧
      (∀ i : A, blg ≤ i → ¬ BitIx i bO) ∧
      (∃ tp : A, IsTopIx tp ∧ orank tp + 1 = orank e') ∧
      RangeSum x y bl e' T ∧
      (∀ i : A, i < bl → ¬ BitIx i T') ∧
      (∀ k k' : A, orank bl + orank k = orank k' → (BitIx k' T' ↔ BitIx k T)) ∧
      orank bO + orank T' = orank u ∧ orank bE + orank u = orank z

/-- **The certificate is sound**: above the threshold, whatever was guessed,
the three parts assemble to the product of the ranks. -/
theorem timesCert_sound [Nonempty A] {x y z : A} (hP : 2 ^ 20 ≤ posCount A)
    (h : TimesCert x y z) : orank x * orank y = orank z := by
  obtain ⟨g, g₂, B₂, bl, blg, bE, bO, T, T', u, e', hg0, hg₂, hB₂, hover, hblB, heven,
    hEhigh, hodd, hOlow, hblg, hOhigh, ⟨tp, htp, htpe⟩, htail, hT'low, hT'link, hu, huz⟩ := h
  have h2P := two_posCount_lt_card hP
  have hcard := posCount_lt_card (A := A)
  have hg₂pos : 0 < orank g₂ := by omega
  obtain ⟨⟨M, hM⟩, hbllow⟩ := (bitIx_iff_of_isBlockSet hg₂pos hB₂ bl).mp hblB
  rw [IsLowIx] at hbllow
  have hblval : orank bl = M * (2 * orank g) := by
    have : orank g₂ * M = M * (2 * orank g) := by
      have h1 : orank g₂ = 2 * orank g := by omega
      rw [h1]
      ring
    omega
  -- reading the even element
  have hEwin : ∀ mm, mm < M →
      orank bE / 2 ^ (mm * (2 * orank g)) % 2 ^ (2 * orank g)
        = intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * orank g)) (orank g) := by
    intro mm hmm
    have hmmlt : mm * (2 * orank g) < orank bl := by
      rw [hblval]
      exact (Nat.mul_lt_mul_right (by omega : 0 < 2 * orank g)).mpr hmm
    obtain ⟨β, hβ⟩ := exists_orank_eq (A := A) (m := mm * (2 * orank g))
      (lt_trans hmmlt (orank_lt_card bl))
    have hβlow : IsLowIx β := by
      rw [IsLowIx]
      omega
    have hgg : orank g₂ * mm = mm * (2 * orank g) := by
      have h1 : orank g₂ = 2 * orank g := by omega
      rw [h1]
      ring
    have hβB : BitIx β B₂ := (bitIx_iff_of_isBlockSet hg₂pos hB₂ β).mpr
      ⟨⟨mm, by omega⟩, hβlow⟩
    have hnext : (mm + 1) * (2 * orank g) ≤ M * (2 * orank g) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (mm + 1) * (2 * orank g) = mm * (2 * orank g) + 2 * orank g := by ring
    obtain ⟨β', hβ'⟩ := exists_orank_eq (A := A) (m := orank β + orank g₂) (by
      have := orank_lt_card bl
      omega)
    obtain ⟨βe, hβe⟩ := exists_orank_eq (A := A) (m := orank β + orank g) (by
      have := orank_lt_card bl
      omega)
    obtain ⟨VE, hwinVE, hrsVE⟩ := heven β β' βe hβB (lt_of_orank_lt (by omega))
      (by omega) (by omega)
    obtain ⟨mr, hmr0, hmre, hmrV⟩ := rangeSum_sound hrsVE
    have hmrG : mr = orank g := by omega
    have hval := (windowAt_iff (b := β) (e := β') (x := bE) (m := VE)
      (w := 2 * orank g) (by omega)).mp hwinVE
    rw [hβ] at hval
    rw [← hval, hmrV, hmrG, hβ]
  -- the even element is the packing of the even block sums
  have hbEval : orank bE = packVal (2 * orank g)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * orank g)) (orank g)) M := by
    refine eq_packVal_of_windows (by omega) ?_ hEwin ?_
    · intro mm hmm
      rw [← hEwin mm hmm]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro i hi
      by_cases hic : i < Nat.card A
      · obtain ⟨î, hî⟩ := exists_orank_eq (A := A) hic
        have hle : bl ≤ î := orank_le_iff.mp (by omega)
        have := hEhigh î hle
        rw [bitIx_iff, hî, Bool.not_eq_true] at this
        exact this
      · exact testBit_orank_eq_false (by omega)
  -- reading the odd element, above its shift
  have hOwin : ∀ mm, mm < M →
      (orank bO / 2 ^ orank g) / 2 ^ (mm * (2 * orank g)) % 2 ^ (2 * orank g)
        = intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * orank g) + orank g) (orank g) := by
    intro mm hmm
    have hmmlt : mm * (2 * orank g) < orank bl := by
      rw [hblval]
      exact (Nat.mul_lt_mul_right (by omega : 0 < 2 * orank g)).mpr hmm
    obtain ⟨β, hβ⟩ := exists_orank_eq (A := A) (m := mm * (2 * orank g))
      (lt_trans hmmlt (orank_lt_card bl))
    have hβlow : IsLowIx β := by
      rw [IsLowIx]
      omega
    have hgg : orank g₂ * mm = mm * (2 * orank g) := by
      have h1 : orank g₂ = 2 * orank g := by omega
      rw [h1]
      ring
    have hβB : BitIx β B₂ := (bitIx_iff_of_isBlockSet hg₂pos hB₂ β).mpr
      ⟨⟨mm, by omega⟩, hβlow⟩
    have hnext : (mm + 1) * (2 * orank g) ≤ M * (2 * orank g) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (mm + 1) * (2 * orank g) = mm * (2 * orank g) + 2 * orank g := by ring
    obtain ⟨β', hβ'⟩ := exists_orank_eq (A := A) (m := orank β + orank g₂) (by
      have := orank_lt_card bl
      omega)
    obtain ⟨βo, hβo⟩ := exists_orank_eq (A := A) (m := orank β + orank g) (by
      have := orank_lt_card bl
      omega)
    obtain ⟨βo3, hβo3⟩ := exists_orank_eq (A := A) (m := orank βo + orank g₂) (by
      have h1 := hbllow
      have h2 := two_posCount_lt_card hP
      have := orank_lt_card bl
      omega)
    obtain ⟨VO, hwinVO, hrsVO⟩ := hodd β β' βo βo3 hβB (lt_of_orank_lt (by omega))
      (by omega) (by omega) (by omega)
    obtain ⟨mr, hmr0, hmre, hmrV⟩ := rangeSum_sound hrsVO
    have hmrG : mr = orank g := by omega
    have hval := (windowAt_iff (b := βo) (e := βo3) (x := bO) (m := VO)
      (w := 2 * orank g) (by omega)).mp hwinVO
    have hdd : orank bO / 2 ^ orank g / 2 ^ (mm * (2 * orank g))
        = orank bO / 2 ^ orank βo := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, hβo, hβ]
      congr 2
      omega
    rw [hdd, ← hval, hmrV, hmrG, hβo, hβ]
  -- the odd element is the shifted packing of the odd block sums
  have hbOdiv : orank bO / 2 ^ orank g = packVal (2 * orank g)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * orank g) + orank g) (orank g)) M := by
    refine eq_packVal_of_windows (by omega) ?_ hOwin ?_
    · intro mm hmm
      rw [← hOwin mm hmm]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro i hi
      rw [Nat.testBit_div_two_pow]
      by_cases hic : i + orank g < Nat.card A
      · obtain ⟨î, hî⟩ := exists_orank_eq (A := A) hic
        have hle : blg ≤ î := orank_le_iff.mp (by omega)
        have := hOhigh î hle
        rw [bitIx_iff, hî, Bool.not_eq_true] at this
        exact this
      · exact testBit_orank_eq_false (by omega)
  have hbOval : orank bO = 2 ^ orank g * (orank bO / 2 ^ orank g) := by
    refine eq_two_pow_mul_div fun i hi => ?_
    obtain ⟨iw, hiw⟩ := exists_orank_eq (A := A) (m := i) (lt_trans hi (orank_lt_card g))
    have := hOlow iw (lt_of_orank_lt (by omega))
    rw [bitIx_iff, hiw, Bool.not_eq_true] at this
    exact this
  rw [hbOdiv] at hbOval
  -- the tail
  obtain ⟨mT, hmT0, hmTe, hmTV⟩ := rangeSum_sound htail
  have he'P : orank e' = posCount A := by
    rw [IsTopIx] at htp
    omega
  have hblP : orank bl < posCount A := by omega
  have hT'val : orank T' = 2 ^ orank bl * orank T := by
    refine eq_two_pow_mul_of_testBit (fun i hi => ?_) (fun k => ?_)
    · obtain ⟨iw, hiw⟩ := exists_orank_eq (A := A) (m := i)
        (lt_trans hi (orank_lt_card bl))
      have := hT'low iw (lt_of_orank_lt (by omega))
      rw [bitIx_iff, hiw, Bool.not_eq_true] at this
      exact this
    · by_cases hkc : orank bl + k < Nat.card A
      · obtain ⟨kw, hkw⟩ := exists_orank_eq (A := A) (m := k) (by omega)
        obtain ⟨kw', hkw'⟩ := exists_orank_eq (A := A) hkc
        have hlink := hT'link kw kw' (by omega)
        rw [bitIx_iff, bitIx_iff, hkw, hkw'] at hlink
        exact Bool.eq_iff_iff.mpr hlink
      · have h1 : (orank T').testBit (orank bl + k) = false :=
          testBit_orank_eq_false (by omega)
        have h2 : (orank T).testBit k = false := testBit_orank_eq_false (by omega)
        rw [h1, h2]
  -- assemble the three parts
  have hEO := packVal_evenOdd (colCountN (orank x) (orank y) (posCount A)) (orank g) M
  have happend := intervalSum_append (colCountN (orank x) (orank y) (posCount A)) 0
    (M * (2 * orank g)) mT
  rw [Nat.zero_add] at happend
  have htotal : M * (2 * orank g) + mT = posCount A := by omega
  rw [htotal] at happend
  have hover' : ∀ i d : ℕ, (orank y).testBit i = true → (orank x).testBit d = true →
      i + d < posCount A := by
    intro i d hyi hxd
    have hiP : i < posCount A := by
      by_contra hc
      rw [testBit_orank_eq_false (by omega)] at hyi
      exact absurd hyi (by simp)
    have hdP : d < posCount A := by
      by_contra hc
      rw [testBit_orank_eq_false (by omega)] at hxd
      exact absurd hxd (by simp)
    obtain ⟨iw, hiw⟩ := exists_orank_eq (A := A) (m := i) (by omega)
    obtain ⟨dw, hdw⟩ := exists_orank_eq (A := A) (m := d) (by omega)
    obtain ⟨jc, hjc, hjclow⟩ := hover iw dw (by rw [bitIx_iff, hiw]; exact hyi)
      (by rw [bitIx_iff, hdw]; exact hxd)
    rw [IsLowIx, IsTopIx] at hjclow
    omega
  have hmul := mul_eq_colSum (x := orank x) (y := orank y) (P := posCount A)
    (lt_of_lt_of_le (orank_lt_card x) card_le_two_pow_posCount)
    (lt_of_lt_of_le (orank_lt_card y) card_le_two_pow_posCount) hover'
  rw [hblval] at hmTV
  have h2bl : (2 : ℕ) ^ orank bl = 2 ^ (M * (2 * orank g)) := by rw [hblval]
  rw [h2bl, hmTV] at hT'val
  omega

/-- **The certificate exists for the product**: the gap of
`LogTime/BitSum/Sizes`, the boundaries of the even/odd split at twice that gap,
a last boundary two blocks and change below the top, the block sums packed by
`DescriptiveComplexity.BitSum.packVal`, and the tail; every window is a field
of a packing and every range is `DescriptiveComplexity.BitSum.rangeSum_of_eq`. -/
theorem timesCert_of_eq [Nonempty A] {x y z : A} (hP : 2 ^ 20 ≤ posCount A)
    (hz : orank x * orank y = orank z) : TimesCert x y z := by
  classical
  have hcard := posCount_lt_card (A := A)
  have h2P := two_posCount_lt_card hP
  -- the gap, abstracted from `Sizes`
  obtain ⟨G, hG2, hGP, hPG, hroomG⟩ : ∃ G : ℕ, 2 ≤ G ∧ G < posCount A ∧
      posCount A < 2 ^ G ∧ G * (4 * G + 2) + 2 < posCount A :=
    ⟨lvl1Block (posCount A), two_le_lvl1Block hP, lvl1Block_lt hP,
      lt_two_pow_lvl1Block _, chain_room hP⟩
  have hGles : 2 * G ≤ G * (4 * G + 2) := by
    have h1 : G * 2 ≤ G * (4 * G + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- the number of double blocks below the last boundary, and the tail's width
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, M * (2 * G) ≤ posCount A - 2 - 2 * G ∧
      posCount A - 2 - 2 * G < M * (2 * G) + 2 * G := by
    refine ⟨(posCount A - 2 - 2 * G) / (2 * G), Nat.div_mul_le_self _ _, ?_⟩
    have hdm := Nat.div_add_mod (posCount A - 2 - 2 * G) (2 * G)
    have hmod : (posCount A - 2 - 2 * G) % (2 * G) < 2 * G := Nat.mod_lt _ (by omega)
    have hc : 2 * G * ((posCount A - 2 - 2 * G) / (2 * G))
        = (posCount A - 2 - 2 * G) / (2 * G) * (2 * G) := Nat.mul_comm _ _
    omega
  set mT := posCount A - M * (2 * G) with hmTdef
  have hmT1 : 2 * G + 2 ≤ mT := by omega
  have hmT2 : mT ≤ 4 * G + 2 := by omega
  have htotal : M * (2 * G) + mT = posCount A := by omega
  -- no pair of set bits reaches the top position
  have hover' : ∀ i d : ℕ, (orank y).testBit i = true → (orank x).testBit d = true →
      i + d < posCount A := by
    intro i d hyi hxd
    have h2i : 2 ^ i ≤ orank y := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (by omega)] at hyi
      exact absurd hyi (by simp)
    have h2d : 2 ^ d ≤ orank x := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (by omega)] at hxd
      exact absurd hxd (by simp)
    by_contra hc
    have hpow : (2 : ℕ) ^ posCount A ≤ 2 ^ (i + d) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hprod : 2 ^ (i + d) ≤ orank x * orank y := by
      rw [pow_add]
      calc 2 ^ i * 2 ^ d ≤ orank y * orank x := Nat.mul_le_mul h2i h2d
        _ = orank x * orank y := Nat.mul_comm _ _
    have hzc := orank_lt_card z
    have hcle := card_le_two_pow_posCount (A := A)
    omega
  have hmul := mul_eq_colSum (x := orank x) (y := orank y) (P := posCount A)
    (lt_of_lt_of_le (orank_lt_card x) card_le_two_pow_posCount)
    (lt_of_lt_of_le (orank_lt_card y) card_le_two_pow_posCount) hover'
  -- the three parts and their sum
  have hcle : ∀ u : ℕ,
      colCountN (orank x) (orank y) (posCount A) u < posCount A + 1 := fun u => by
    have := colCountN_le (orank x) (orank y) (posCount A) u
    omega
  have hfAll : ∀ a' : ℕ,
      intervalSum (colCountN (orank x) (orank y) (posCount A)) a' G < 2 ^ (2 * G) :=
    fun a' => by
      have h1 := intervalSum_lt (H := posCount A + 1) (by omega)
        (h := colCountN (orank x) (orank y) (posCount A)) (a := a') (m := G)
        fun u _ => hcle _
      have h2 : (posCount A + 1) * 2 ^ G ≤ 2 ^ G * 2 ^ G :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (2 : ℕ) ^ (2 * G) = 2 ^ G * 2 ^ G := by
        rw [← pow_add]
        congr 1
        omega
      omega
  have hpackE_lt : packVal (2 * G)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G)) G) M < 2 ^ (M * (2 * G)) :=
    packVal_lt fun mm _ => hfAll _
  have hpackO_lt : packVal (2 * G)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G) + G) G) M < 2 ^ (M * (2 * G)) :=
    packVal_lt fun mm _ => hfAll _
  have hEO := packVal_evenOdd (colCountN (orank x) (orank y) (posCount A)) G M
  have happend := intervalSum_append (colCountN (orank x) (orank y) (posCount A)) 0
    (M * (2 * G)) mT
  rw [Nat.zero_add, htotal] at happend
  have hparts : packVal (2 * G)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G)) G) M
      + 2 ^ G * packVal (2 * G)
          (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * G) + G) G) M
      + 2 ^ (M * (2 * G))
          * intervalSum (colCountN (orank x) (orank y) (posCount A))
              (M * (2 * G)) mT = orank z := by
    omega
  have htail_le : intervalSum (colCountN (orank x) (orank y) (posCount A))
      (M * (2 * G)) mT ≤ 2 ^ (M * (2 * G))
        * intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  -- the elements
  obtain ⟨g, hgr⟩ := exists_orank_eq (A := A) (m := G) (by omega)
  obtain ⟨g₂, hg₂r⟩ := exists_orank_eq (A := A) (m := 2 * G) (by omega)
  have hg₂pos : 0 < orank g₂ := by omega
  obtain ⟨B₂, hB₂⟩ := exists_isBlockSet (A := A) (g := g₂) (by omega)
  obtain ⟨bl, hblr⟩ := exists_orank_eq (A := A) (m := M * (2 * G)) (by omega)
  obtain ⟨blg, hblgr⟩ := exists_orank_eq (A := A) (m := M * (2 * G) + G) (by omega)
  obtain ⟨tp, htpr⟩ := exists_orank_eq (A := A) (m := posCount A - 1) (by omega)
  obtain ⟨e', he'r⟩ := exists_orank_eq (A := A) (m := posCount A) (by omega)
  obtain ⟨bE, hbEr⟩ := exists_orank_eq (A := A) (m := packVal (2 * G)
    (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
      (mm * (2 * G)) G) M) (by
        have := orank_lt_card z
        omega)
  obtain ⟨bO, hbOr⟩ := exists_orank_eq (A := A) (m := 2 ^ G * packVal (2 * G)
    (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
      (mm * (2 * G) + G) G) M) (by
        have := orank_lt_card z
        omega)
  obtain ⟨T, hTr⟩ := exists_orank_eq (A := A)
    (m := intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT) (by
      have := orank_lt_card z
      omega)
  obtain ⟨T', hT'r⟩ := exists_orank_eq (A := A)
    (m := 2 ^ (M * (2 * G))
      * intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT) (by
      have := orank_lt_card z
      omega)
  obtain ⟨u, hur⟩ := exists_orank_eq (A := A)
    (m := 2 ^ G * packVal (2 * G)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G) + G) G) M
      + 2 ^ (M * (2 * G))
          * intervalSum (colCountN (orank x) (orank y) (posCount A))
              (M * (2 * G)) mT) (by
      have := orank_lt_card z
      omega)
  refine ⟨g, g₂, B₂, bl, blg, bE, bO, T, T', u, e', by omega, by omega, hB₂,
    ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ⟨tp, ?_, by omega⟩, ?_, ?_, ?_,
    by omega, by omega⟩
  · -- no overflow
    intro i d hyi hxd
    rw [bitIx_iff] at hyi hxd
    have hsum := hover' (orank i) (orank d) hyi hxd
    obtain ⟨jc, hjcr⟩ := exists_orank_eq (A := A) (m := orank i + orank d) (by omega)
    refine ⟨jc, by omega, ?_⟩
    rw [IsLowIx, IsTopIx]
    omega
  · -- the last boundary is a boundary
    exact (bitIx_iff_of_isBlockSet hg₂pos hB₂ bl).mpr
      ⟨⟨M, by rw [hblr, hg₂r]; ring⟩, by rw [IsLowIx]; omega⟩
  · -- the even windows
    intro β β' βe hβB hβlt hβ' hβe
    obtain ⟨⟨mm, hmm⟩, hβlow⟩ := (bitIx_iff_of_isBlockSet hg₂pos hB₂ β).mp hβB
    have hβval : orank β = mm * (2 * G) := by rw [hmm, hg₂r]; ring
    have hmmM : mm < M := by
      have hlt := orank_lt_orank hβlt
      rw [hβval, hblr] at hlt
      exact (Nat.mul_lt_mul_right (by omega : 0 < 2 * G)).mp hlt
    obtain ⟨VE, hVEr⟩ := exists_orank_eq (A := A)
      (m := intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G)) G) (by
          have h1 := hfAll (mm * (2 * G))
          have hp2 : (2 : ℕ) ^ (2 * G) ≤ 2 ^ (posCount A - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have hp3 : 2 ^ (posCount A - 1) < Nat.card A :=
            (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
          omega)
    refine ⟨VE, ?_, ?_⟩
    · refine (windowAt_iff (w := 2 * G) (by omega)).mpr ?_
      rw [hVEr, hbEr, hβval]
      exact (packVal_window (g := 2 * G)
        (f := fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
          (mm * (2 * G)) G) (fun q _ => hfAll _) hmmM).symm
    · refine rangeSum_of_eq hP (by omega) hPG (by omega : 0 < G) (by omega) ?_ ?_
      · have h1 : G * G ≤ G * (4 * G + 2) := Nat.mul_le_mul_left _ (by omega)
        omega
      · rw [hVEr, hβval]
  · -- nothing above the last boundary in the even element
    intro i hi
    have hge : orank bl ≤ orank i := orank_le_iff.mpr hi
    rw [bitIx_iff, hbEr]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hpackE_lt
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp
  · -- the odd windows
    intro β β' βo βo3 hβB hβlt hβ' hβo hβo3
    obtain ⟨⟨mm, hmm⟩, hβlow⟩ := (bitIx_iff_of_isBlockSet hg₂pos hB₂ β).mp hβB
    have hβval : orank β = mm * (2 * G) := by rw [hmm, hg₂r]; ring
    have hmmM : mm < M := by
      have hlt := orank_lt_orank hβlt
      rw [hβval, hblr] at hlt
      exact (Nat.mul_lt_mul_right (by omega : 0 < 2 * G)).mp hlt
    have hβoval : orank βo = mm * (2 * G) + G := by omega
    obtain ⟨VO, hVOr⟩ := exists_orank_eq (A := A)
      (m := intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G) + G) G) (by
          have h1 := hfAll (mm * (2 * G) + G)
          have hp2 : (2 : ℕ) ^ (2 * G) ≤ 2 ^ (posCount A - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have hp3 : 2 ^ (posCount A - 1) < Nat.card A :=
            (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
          omega)
    refine ⟨VO, ?_, ?_⟩
    · refine (windowAt_iff (w := 2 * G) (by omega)).mpr ?_
      rw [hVOr, hbOr, hβoval]
      have hdd : 2 ^ G * packVal (2 * G)
          (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * G) + G) G) M / 2 ^ (mm * (2 * G) + G)
          = packVal (2 * G)
              (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
                (mm * (2 * G) + G) G) M / 2 ^ (mm * (2 * G)) := by
        rw [pow_add, Nat.mul_comm (2 ^ (mm * (2 * G))) (2 ^ G)]
        exact Nat.mul_div_mul_left _ _ (Nat.two_pow_pos G)
      rw [hdd]
      exact (packVal_window (g := 2 * G)
        (f := fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
          (mm * (2 * G) + G) G) (fun q _ => hfAll _) hmmM).symm
    · refine rangeSum_of_eq hP (by omega) hPG (by omega : 0 < G) (by omega) ?_ ?_
      · have h1 : G * G ≤ G * (4 * G + 2) := Nat.mul_le_mul_left _ (by omega)
        omega
      · rw [hVOr, hβoval]
  · -- nothing below the shift in the odd element
    intro i hig
    have hlt : orank i < G := by
      have := orank_lt_orank hig
      omega
    rw [bitIx_iff, hbOr, show 2 ^ G * packVal (2 * G)
      (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
        (mm * (2 * G) + G) G) M
      = packVal (2 * G)
          (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * G) + G) G) M <<< G by rw [Nat.shiftLeft_eq]; ring,
      Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ orank i ≥ G)]
    simp
  · -- nothing above the last boundary's field in the odd element
    intro i hi
    have hge : orank blg ≤ orank i := orank_le_iff.mpr hi
    have hbOlt : 2 ^ G * packVal (2 * G)
        (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
          (mm * (2 * G) + G) G) M < 2 ^ (M * (2 * G) + G) := by
      have h1 : 2 ^ G * packVal (2 * G)
          (fun mm => intervalSum (colCountN (orank x) (orank y) (posCount A))
            (mm * (2 * G) + G) G) M < 2 ^ G * 2 ^ (M * (2 * G)) :=
        (Nat.mul_lt_mul_left (Nat.two_pow_pos G)).mpr hpackO_lt
      have h2 : (2 : ℕ) ^ G * 2 ^ (M * (2 * G)) = 2 ^ (M * (2 * G) + G) := by
        rw [← pow_add]
        congr 1
        omega
      omega
    rw [bitIx_iff, hbOr]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hbOlt
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp
  · -- the top index
    rw [IsTopIx, htpr]
    omega
  · -- the tail range
    refine rangeSum_of_eq hP (by omega) hPG (by omega : 0 < mT) (by omega) ?_ ?_
    · have h1 : G * mT ≤ G * (4 * G + 2) := Nat.mul_le_mul_left _ hmT2
      omega
    · rw [hTr, hblr]
  · -- nothing below the shift in the tail element
    intro i hil
    have hlt : orank i < M * (2 * G) := by
      have := orank_lt_orank hil
      omega
    rw [bitIx_iff, hT'r, show 2 ^ (M * (2 * G))
      * intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT
      = intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT
          <<< (M * (2 * G)) by rw [Nat.shiftLeft_eq]; ring,
      Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ orank i ≥ M * (2 * G))]
    simp
  · -- the link between the tail and its shift
    intro k k' hplus
    rw [bitIx_iff, bitIx_iff, hT'r, hTr, show 2 ^ (M * (2 * G))
      * intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT
      = intervalSum (colCountN (orank x) (orank y) (posCount A)) (M * (2 * G)) mT
          <<< (M * (2 * G)) by rw [Nat.shiftLeft_eq]; ring,
      Nat.testBit_shiftLeft, decide_eq_true (by omega : orank k' ≥ M * (2 * G)),
      Bool.true_and, show orank k' - M * (2 * G) = orank k by omega]

/-- **The multiplication of ranks, characterized**: above the threshold, the
certificate holds exactly for the products. -/
theorem timesCert_iff [Nonempty A] {x y z : A} (hP : 2 ^ 20 ≤ posCount A) :
    TimesCert x y z ↔ orank x * orank y = orank z :=
  ⟨timesCert_sound hP, timesCert_of_eq hP⟩

end Times

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **The successor of a rank is first-order in the bit logic**: one guessed
element of rank one. -/
theorem bitDef_succ (x y : α) :
    BitDef (L := L) fun _ _ _ _ _ v => orank (v x) + 1 = orank (v y) := by
  refine (((bitDef_isOne (L := L) (α := α ⊕ Fin 1) (Sum.inr 0)).and
    (bitDef_plus (Sum.inl x) (Sum.inr 0) (Sum.inl y))).ex).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨o, ho, hsum⟩
    omega
  · intro h
    have hone : (1 : ℕ) < Nat.card A := lt_of_le_of_lt (by omega) (orank_lt_card (v y))
    obtain ⟨o, ho⟩ := exists_orank_eq (A := A) (m := 1) hone
    exact ⟨o, ho, by omega⟩

/-- **The column word is a formula**: one universal index, one addition, three
bit reads. -/
theorem bitDef_colWord (x y j w : α) :
    BitDef (L := L) fun _ _ _ _ _ v => ColWord (v x) (v y) (v j) (v w) := by
  refine (((bitDef_bit (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl w)).iff
    ((bitDef_bit (Sum.inr 0) (Sum.inl y)).and
      (((bitDef_plus (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1) (Sum.inl (Sum.inr 0))
        (Sum.inr 0) (Sum.inl (Sum.inl j))).and
          (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl x)))).ex))).all).congr
    fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

/-- **The column count is a formula**: the column word, handed to the Bit Sum
Lemma. -/
theorem bitDef_colCount (x y j n : α) :
    BitDef (L := L) fun _ _ _ _ _ v => ColCount (v x) (v y) (v j) (v n) := by
  refine (((bitDef_colWord (Sum.inl x) (Sum.inl y) (Sum.inl j) (Sum.inr 0)).and
    (bitDef_popAll (Sum.inr 0) (Sum.inl n))).ex).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

/-- **A chain step is a formula**: two additions, a successor, a bit read and
an equality, under two guessed intermediate sums. -/
theorem bitDef_stepEq (n r r' t V : α) :
    BitDef (L := L) fun _ _ _ _ _ v => StepEq (v n) (v r) (v r') (v t) (v V) := by
  have hbody : BitDef (L := L) (α := α ⊕ Fin 2) (fun A _ _ _ _ u =>
      orank (u (Sum.inl r)) + orank (u (Sum.inl n)) = orank (u (Sum.inr 0)) ∧
        orank (u (Sum.inl r')) + orank (u (Sum.inl r')) = orank (u (Sum.inr 1)) ∧
          ((BitIx (u (Sum.inl t)) (u (Sum.inl V)) ∧
              orank (u (Sum.inr 1)) + 1 = orank (u (Sum.inr 0))) ∨
            (¬ BitIx (u (Sum.inl t)) (u (Sum.inl V)) ∧ u (Sum.inr 1) = u (Sum.inr 0)))) :=
    (bitDef_plus (Sum.inl r) (Sum.inl n) (Sum.inr 0)).and <|
      (bitDef_plus (Sum.inl r') (Sum.inl r') (Sum.inr 1)).and <|
        ((bitDef_bit (Sum.inl t) (Sum.inl V)).and (bitDef_succ (Sum.inr 1) (Sum.inr 0))).or
          (((bitDef_bit (Sum.inl t) (Sum.inl V)).not).and
            (bitDef_eq (Sum.inr 1) (Sum.inr 0)))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨uu, h⟩
    exact ⟨uu 0, uu 1, h⟩
  · rintro ⟨s, d, h⟩
    exact ⟨![s, d], h⟩

/-- **A range of columns is a formula**: the boundary set, the counter, the
packed chain, and the three conditions – each a block of quantified indices
over windows, the counts entering through
`DescriptiveComplexity.BitSum.bitDef_colCount`. -/
theorem bitDef_rangeSum (x y a e V : α) :
    BitDef (L := L) fun _ _ _ _ _ v => RangeSum (v x) (v y) (v a) (v e) (v V) := by
  have hbase : BitDef (L := L) (α := α ⊕ Fin 4) (fun A _ _ _ _ u =>
      ∀ p p' r : A, orank p = 0 → orank p + orank (u (Sum.inr 0)) = orank p' →
        WindowAt p p' (u (Sum.inr 3)) r →
          ∃ n : A, ColCount (u (Sum.inl x)) (u (Sum.inl y)) (u (Sum.inl a)) n ∧
            StepEq n p r p (u (Sum.inl V))) := by
    have hinner : BitDef (L := L) (α := ((α ⊕ Fin 4) ⊕ Fin 3) ⊕ Fin 1)
        (fun A _ _ _ _ w =>
          ColCount (w (Sum.inl (Sum.inl (Sum.inl x)))) (w (Sum.inl (Sum.inl (Sum.inl y))))
              (w (Sum.inl (Sum.inl (Sum.inl a)))) (w (Sum.inr 0)) ∧
            StepEq (w (Sum.inr 0)) (w (Sum.inl (Sum.inr 0))) (w (Sum.inl (Sum.inr 2)))
              (w (Sum.inl (Sum.inr 0))) (w (Sum.inl (Sum.inl (Sum.inl V))))) :=
      (bitDef_colCount (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl y)))
        (Sum.inl (Sum.inl (Sum.inl a))) (Sum.inr 0)).and
        (bitDef_stepEq (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 2))
          (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inl (Sum.inl V))))
    refine (((bitDef_isZero (L := L) (α := (α ⊕ Fin 4) ⊕ Fin 3) (Sum.inr 0)).imp <|
      (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 1)).imp <|
        (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 3)) (Sum.inr 2)).imp
          hinner.ex).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h p p' r => h ![p, p', r], fun h w => h (w 0) (w 1) (w 2)⟩
  have hstep : BitDef (L := L) (α := α ⊕ Fin 4) (fun A _ _ _ _ u =>
      ∀ p p' p'' r r' t j : A, BitIx p (u (Sum.inr 1)) →
        orank p + orank (u (Sum.inr 0)) = orank p' →
          orank p' + orank (u (Sum.inr 0)) = orank p'' → IsLowIx p'' →
            WindowAt p p' (u (Sum.inr 3)) r → WindowAt p' p'' (u (Sum.inr 3)) r' →
              WindowAt p' p'' (u (Sum.inr 2)) t →
                orank (u (Sum.inl a)) + orank t = orank j → j < u (Sum.inl e) →
                  ∃ n : A, ColCount (u (Sum.inl x)) (u (Sum.inl y)) j n ∧
                    StepEq n r r' t (u (Sum.inl V))) := by
    have hinner : BitDef (L := L) (α := ((α ⊕ Fin 4) ⊕ Fin 7) ⊕ Fin 1)
        (fun A _ _ _ _ w =>
          ColCount (w (Sum.inl (Sum.inl (Sum.inl x)))) (w (Sum.inl (Sum.inl (Sum.inl y))))
              (w (Sum.inl (Sum.inr 6))) (w (Sum.inr 0)) ∧
            StepEq (w (Sum.inr 0)) (w (Sum.inl (Sum.inr 3))) (w (Sum.inl (Sum.inr 4)))
              (w (Sum.inl (Sum.inr 5))) (w (Sum.inl (Sum.inl (Sum.inl V))))) :=
      (bitDef_colCount (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl y)))
        (Sum.inl (Sum.inr 6)) (Sum.inr 0)).and
        (bitDef_stepEq (Sum.inr 0) (Sum.inl (Sum.inr 3)) (Sum.inl (Sum.inr 4))
          (Sum.inl (Sum.inr 5)) (Sum.inl (Sum.inl (Sum.inl V))))
    refine (((bitDef_bit (L := L) (α := (α ⊕ Fin 4) ⊕ Fin 7) (Sum.inr 0)
      (Sum.inl (Sum.inr 1))).imp <|
      (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 1)).imp <|
        (bitDef_plus (Sum.inr 1) (Sum.inl (Sum.inr 0)) (Sum.inr 2)).imp <|
          (bitDef_isLowIx (Sum.inr 2)).imp <|
            (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 3)) (Sum.inr 3)).imp <|
              (bitDef_windowAt (Sum.inr 1) (Sum.inr 2) (Sum.inl (Sum.inr 3))
                (Sum.inr 4)).imp <|
                (bitDef_windowAt (Sum.inr 1) (Sum.inr 2) (Sum.inl (Sum.inr 2))
                  (Sum.inr 5)).imp <|
                  (bitDef_plus (Sum.inl (Sum.inl a)) (Sum.inr 5) (Sum.inr 6)).imp <|
                    (bitDef_lt (Sum.inr 6) (Sum.inl (Sum.inl e))).imp
                      hinner.ex).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h p p' p'' r r' t j => h ![p, p', p'', r, r', t, j],
      fun h w => h (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)⟩
  have htop : BitDef (L := L) (α := α ⊕ Fin 4) (fun A _ _ _ _ u =>
      ∃ p p' t r m q : A, BitIx p (u (Sum.inr 1)) ∧
        orank p + orank (u (Sum.inr 0)) = orank p' ∧ IsLowIx p' ∧
          WindowAt p p' (u (Sum.inr 2)) t ∧ WindowAt p p' (u (Sum.inr 3)) r ∧
            orank t + 1 = orank m ∧
              orank (u (Sum.inl a)) + orank m = orank (u (Sum.inl e)) ∧
                orank m + orank (u (Sum.inr 0)) = orank q ∧
                  WindowAt m q (u (Sum.inl V)) r ∧
                    ∀ i : A, q ≤ i → ¬ BitIx i (u (Sum.inl V))) := by
    have hhigh : BitDef (L := L) (α := (α ⊕ Fin 4) ⊕ Fin 6) (fun A _ _ _ _ w =>
        ∀ i : A, w (Sum.inr 5) ≤ i → ¬ BitIx i (w (Sum.inl (Sum.inl V)))) :=
      ((bitDef_le (L := L) (α := ((α ⊕ Fin 4) ⊕ Fin 6) ⊕ Fin 1)
        (Sum.inl (Sum.inr 5)) (Sum.inr 0)).imp
        (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl V)))).not).all
    have hbody : BitDef (L := L) (α := (α ⊕ Fin 4) ⊕ Fin 6) (fun A _ _ _ _ w =>
        BitIx (w (Sum.inr 0)) (w (Sum.inl (Sum.inr 1))) ∧
          orank (w (Sum.inr 0)) + orank (w (Sum.inl (Sum.inr 0))) = orank (w (Sum.inr 1)) ∧
            IsLowIx (w (Sum.inr 1)) ∧
              WindowAt (w (Sum.inr 0)) (w (Sum.inr 1)) (w (Sum.inl (Sum.inr 2)))
                  (w (Sum.inr 2)) ∧
                WindowAt (w (Sum.inr 0)) (w (Sum.inr 1)) (w (Sum.inl (Sum.inr 3)))
                    (w (Sum.inr 3)) ∧
                  orank (w (Sum.inr 2)) + 1 = orank (w (Sum.inr 4)) ∧
                    orank (w (Sum.inl (Sum.inl a))) + orank (w (Sum.inr 4))
                        = orank (w (Sum.inl (Sum.inl e))) ∧
                      orank (w (Sum.inr 4)) + orank (w (Sum.inl (Sum.inr 0)))
                          = orank (w (Sum.inr 5)) ∧
                        WindowAt (w (Sum.inr 4)) (w (Sum.inr 5))
                            (w (Sum.inl (Sum.inl V))) (w (Sum.inr 3)) ∧
                          ∀ i : A, w (Sum.inr 5) ≤ i →
                            ¬ BitIx i (w (Sum.inl (Sum.inl V)))) :=
      (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 1))).and <|
        (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 1)).and <|
          (bitDef_isLowIx (Sum.inr 1)).and <|
            (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 2))
              (Sum.inr 2)).and <|
              (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 3))
                (Sum.inr 3)).and <|
                (bitDef_succ (Sum.inr 2) (Sum.inr 4)).and <|
                  (bitDef_plus (Sum.inl (Sum.inl a)) (Sum.inr 4)
                    (Sum.inl (Sum.inl e))).and <|
                    (bitDef_plus (Sum.inr 4) (Sum.inl (Sum.inr 0)) (Sum.inr 5)).and <|
                      (bitDef_windowAt (Sum.inr 4) (Sum.inr 5) (Sum.inl (Sum.inl V))
                        (Sum.inr 3)).and hhigh
    refine hbody.exs.congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨w, h⟩
      exact ⟨w 0, w 1, w 2, w 3, w 4, w 5, h⟩
    · rintro ⟨p, p', t, r, m, q, h⟩
      exact ⟨![p, p', t, r, m, q], h⟩
  have hbody : BitDef (L := L) (α := α ⊕ Fin 4) (fun A _ _ _ _ u =>
      orank (u (Sum.inr 0)) ≠ 0 ∧ IsBlockSet (u (Sum.inr 0)) (u (Sum.inr 1)) ∧
        IsCounter (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inr 2)) ∧
          (∀ p p' r : A, orank p = 0 → orank p + orank (u (Sum.inr 0)) = orank p' →
            WindowAt p p' (u (Sum.inr 3)) r →
              ∃ n : A, ColCount (u (Sum.inl x)) (u (Sum.inl y)) (u (Sum.inl a)) n ∧
                StepEq n p r p (u (Sum.inl V))) ∧
          (∀ p p' p'' r r' t j : A, BitIx p (u (Sum.inr 1)) →
            orank p + orank (u (Sum.inr 0)) = orank p' →
              orank p' + orank (u (Sum.inr 0)) = orank p'' → IsLowIx p'' →
                WindowAt p p' (u (Sum.inr 3)) r → WindowAt p' p'' (u (Sum.inr 3)) r' →
                  WindowAt p' p'' (u (Sum.inr 2)) t →
                    orank (u (Sum.inl a)) + orank t = orank j → j < u (Sum.inl e) →
                      ∃ n : A, ColCount (u (Sum.inl x)) (u (Sum.inl y)) j n ∧
                        StepEq n r r' t (u (Sum.inl V))) ∧
          (∃ p p' t r m q : A, BitIx p (u (Sum.inr 1)) ∧
            orank p + orank (u (Sum.inr 0)) = orank p' ∧ IsLowIx p' ∧
              WindowAt p p' (u (Sum.inr 2)) t ∧ WindowAt p p' (u (Sum.inr 3)) r ∧
                orank t + 1 = orank m ∧
                  orank (u (Sum.inl a)) + orank m = orank (u (Sum.inl e)) ∧
                    orank m + orank (u (Sum.inr 0)) = orank q ∧
                      WindowAt m q (u (Sum.inl V)) r ∧
                        ∀ i : A, q ≤ i → ¬ BitIx i (u (Sum.inl V)))) :=
    (bitDef_isZero (Sum.inr 0)).not.and <|
      (bitDef_isBlockSet (Sum.inr 0) (Sum.inr 1)).and <|
        (bitDef_isCounter (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).and <|
          hbase.and <| hstep.and htop
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, h⟩
    exact ⟨w 0, w 1, w 2, w 3, h⟩
  · rintro ⟨g, B, C, R, h⟩
    exact ⟨![g, B, C, R], h⟩

/-- **The whole certificate is a formula**: eleven guessed elements and the
conditions, every one of them built from the pieces above. -/
theorem bitDef_timesCert (x y z : α) :
    BitDef (L := L) fun _ _ _ _ _ v => TimesCert (v x) (v y) (v z) := by
  have hover : BitDef (L := L) (α := α ⊕ Fin 11) (fun A _ _ _ _ u =>
      ∀ i d : A, BitIx i (u (Sum.inl y)) → BitIx d (u (Sum.inl x)) →
        ∃ jc : A, orank i + orank d = orank jc ∧ (IsLowIx jc ∨ IsTopIx jc)) := by
    refine (((bitDef_bit (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 2) (Sum.inr 0)
      (Sum.inl (Sum.inl y))).imp <|
      (bitDef_bit (Sum.inr 1) (Sum.inl (Sum.inl x))).imp <|
        ((bitDef_plus (L := L) (α := ((α ⊕ Fin 11) ⊕ Fin 2) ⊕ Fin 1)
          (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)) (Sum.inr 0)).and
          ((bitDef_isLowIx (Sum.inr 0)).or (bitDef_isTopIx (Sum.inr 0)))).ex).alls).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h i d => h ![i, d], fun h w => h (w 0) (w 1)⟩
  have heven : BitDef (L := L) (α := α ⊕ Fin 11) (fun A _ _ _ _ u =>
      ∀ β β' βe : A, BitIx β (u (Sum.inr 2)) → β < u (Sum.inr 3) →
        orank β + orank (u (Sum.inr 1)) = orank β' →
          orank β + orank (u (Sum.inr 0)) = orank βe →
            ∃ VE : A, WindowAt β β' (u (Sum.inr 5)) VE ∧
              RangeSum (u (Sum.inl x)) (u (Sum.inl y)) β βe VE) := by
    refine (((bitDef_bit (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 3) (Sum.inr 0)
      (Sum.inl (Sum.inr 2))).imp <|
      (bitDef_lt (Sum.inr 0) (Sum.inl (Sum.inr 3))).imp <|
        (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 1)) (Sum.inr 1)).imp <|
          (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 2)).imp <|
            ((bitDef_windowAt (L := L) (α := ((α ⊕ Fin 11) ⊕ Fin 3) ⊕ Fin 1)
              (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
              (Sum.inl (Sum.inl (Sum.inr 5))) (Sum.inr 0)).and
              (bitDef_rangeSum (Sum.inl (Sum.inl (Sum.inl x)))
                (Sum.inl (Sum.inl (Sum.inl y))) (Sum.inl (Sum.inr 0))
                (Sum.inl (Sum.inr 2)) (Sum.inr 0))).ex).alls).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h β β' βe => h ![β, β', βe], fun h w => h (w 0) (w 1) (w 2)⟩
  have hodd : BitDef (L := L) (α := α ⊕ Fin 11) (fun A _ _ _ _ u =>
      ∀ β β' βo βo3 : A, BitIx β (u (Sum.inr 2)) → β < u (Sum.inr 3) →
        orank β + orank (u (Sum.inr 1)) = orank β' →
          orank β + orank (u (Sum.inr 0)) = orank βo →
            orank βo + orank (u (Sum.inr 1)) = orank βo3 →
              ∃ VO : A, WindowAt βo βo3 (u (Sum.inr 6)) VO ∧
                RangeSum (u (Sum.inl x)) (u (Sum.inl y)) βo β' VO) := by
    refine (((bitDef_bit (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 4) (Sum.inr 0)
      (Sum.inl (Sum.inr 2))).imp <|
      (bitDef_lt (Sum.inr 0) (Sum.inl (Sum.inr 3))).imp <|
        (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 1)) (Sum.inr 1)).imp <|
          (bitDef_plus (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 2)).imp <|
            (bitDef_plus (Sum.inr 2) (Sum.inl (Sum.inr 1)) (Sum.inr 3)).imp <|
              ((bitDef_windowAt (L := L) (α := ((α ⊕ Fin 11) ⊕ Fin 4) ⊕ Fin 1)
                (Sum.inl (Sum.inr 2)) (Sum.inl (Sum.inr 3))
                (Sum.inl (Sum.inl (Sum.inr 6))) (Sum.inr 0)).and
                (bitDef_rangeSum (Sum.inl (Sum.inl (Sum.inl x)))
                  (Sum.inl (Sum.inl (Sum.inl y))) (Sum.inl (Sum.inr 2))
                  (Sum.inl (Sum.inr 1)) (Sum.inr 0))).ex).alls).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h β β' βo βo3 => h ![β, β', βo, βo3],
      fun h w => h (w 0) (w 1) (w 2) (w 3)⟩
  have hlink : BitDef (L := L) (α := α ⊕ Fin 11) (fun A _ _ _ _ u =>
      ∀ k k' : A, orank (u (Sum.inr 3)) + orank k = orank k' →
        (BitIx k' (u (Sum.inr 8)) ↔ BitIx k (u (Sum.inr 7)))) := by
    refine (((bitDef_plus (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 2) (Sum.inl (Sum.inr 3))
      (Sum.inr 0) (Sum.inr 1)).imp
      ((bitDef_bit (Sum.inr 1) (Sum.inl (Sum.inr 8))).iff
        (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 7))))).alls).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h k k' => h ![k, k'], fun h w => h (w 0) (w 1)⟩
  have hbody := (bitDef_isZero (L := L) (α := α ⊕ Fin 11) (Sum.inr 0)).not.and <|
    (bitDef_plus (Sum.inr 0) (Sum.inr 0) (Sum.inr 1)).and <|
      (bitDef_isBlockSet (Sum.inr 1) (Sum.inr 2)).and <|
        hover.and <|
          (bitDef_bit (Sum.inr 3) (Sum.inr 2)).and <|
            heven.and <|
              (((bitDef_le (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 1) (Sum.inl (Sum.inr 3))
                (Sum.inr 0)).imp
                (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 5))).not).all).and <|
                hodd.and <|
                  (((bitDef_lt (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 1) (Sum.inr 0)
                    (Sum.inl (Sum.inr 0))).imp
                    (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 6))).not).all).and <|
                    (bitDef_plus (Sum.inr 3) (Sum.inr 0) (Sum.inr 4)).and <|
                      (((bitDef_le (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 1)
                        (Sum.inl (Sum.inr 4)) (Sum.inr 0)).imp
                        (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 6))).not).all).and <|
                        (((bitDef_isTopIx (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 1)
                          (Sum.inr 0)).and
                          (bitDef_succ (Sum.inr 0) (Sum.inl (Sum.inr 10)))).ex).and <|
                          (bitDef_rangeSum (Sum.inl x) (Sum.inl y) (Sum.inr 3)
                            (Sum.inr 10) (Sum.inr 7)).and <|
                            (((bitDef_lt (L := L) (α := (α ⊕ Fin 11) ⊕ Fin 1) (Sum.inr 0)
                              (Sum.inl (Sum.inr 3))).imp
                              (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 8))).not).all).and <|
                              hlink.and <|
                                (bitDef_plus (Sum.inr 6) (Sum.inr 8) (Sum.inr 9)).and
                                  (bitDef_plus (Sum.inr 5) (Sum.inr 9) (Sum.inl z))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, h⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, h⟩
  · rintro ⟨g, g₂, B₂, bl, blg, bE, bO, T, T', uu, e', h⟩
    exact ⟨![g, g₂, B₂, bl, blg, bE, bO, T, T', uu, e'], h⟩

/-- **Multiplication of ranks is bit-definable** – the missing half of
[Immerman 1999][immerman1999descriptive] Thm 1.17(1), assembled: the
certificate is a formula, it characterizes the products above the threshold,
and `DescriptiveComplexity.BitDef.of_large` absorbs the threshold, the
relation being numeric. Stated first on three named variables, then relabelled
to any layout. -/
theorem bitDef_times (x y z : α) :
    BitDef (L := L) fun _ _ _ _ _ v => orank (v x) * orank (v y) = orank (v z) := by
  have h3 : BitDef (L := L) (α := Fin 3) fun A _ _ _ _ v =>
      orank (v 0) * orank (v 1) = orank (v 2) := by
    refine BitDef.of_large (2 ^ (2 ^ 20 - 1))
      (isNumeric_of_ranks (f := fun _ r => r 0 * r 1 = r 2)) ?_
    refine ((bitDef_cardGt (2 ^ (2 ^ 20 - 1))).and (bitDef_timesCert 0 1 2)).congr
      fun A _ _ _ _ v => ?_
    constructor
    · rintro ⟨hcard, hcert⟩
      exact ⟨hcard, timesCert_sound (le_posCount_of_card hcard) hcert⟩
    · rintro ⟨hcard, heq⟩
      exact ⟨hcard, timesCert_of_eq (le_posCount_of_card hcard) heq⟩
  exact (h3.relabel ![x, y, z]).congr fun A _ _ _ _ v => Iff.rfl

end Definability

end BitSum

end DescriptiveComplexity
