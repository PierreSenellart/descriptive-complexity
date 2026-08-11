/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Table

/-!
# The running sum: counting a long word by counting its chunks

Levels 1 and 2 of the Bit Sum Lemma are the *same* construction at two sizes:
cut a
word into chunks, keep in each chunk the number of ones below it, and verify one
step by counting the ones of a single chunk – which is what the level below is
for. So it is written once here, with the chunk counter as a parameter:

> `DescriptiveComplexity.BitSum.SumOk c B x S Cnt`: `B` delimits the chunks of
> length `c`, and the window of `S` in each chunk holds the number of ones of `x`
> below that chunk – pinned by “`0` at the first chunk” and “one step adds the
> count of the chunk just passed”, the count being supplied by `Cnt`.

Level 2 instantiates `Cnt` with `DescriptiveComplexity.BitSum.PopShort` (the
table), level 1 with level 2. Nothing else changes, and neither level ever has to
know how the level below counts.

## What the soundness needs of the level below

Two things only, and both are statements, not constructions: that `Cnt` is
*sound* (its second argument is the number of ones of its first) and that it is
*total* (every word has a count). `DescriptiveComplexity.BitSum.sum_eq` then
gives the running sums their meaning by an induction on the chunk index, exactly
as `DescriptiveComplexity.BitSum.counter_eq` does for the counter – of which this
is the general form, a counter being the running sum of the constant word `1`.

## The arithmetic underneath

One identity carries the whole thing:
`DescriptiveComplexity.BitSum.onesBelow_add` – the ones below `k + c` are those
below `k` plus those of the chunk starting at `k`. The chunk is read with
`DescriptiveComplexity.BitSum.WindowAt`, whose value is `x / 2 ^ k % 2 ^ c`, and
the truncation is harmless because a window's own count ignores what was cut off
(`DescriptiveComplexity.BitSum.onesBelow_mod`).
-/

namespace DescriptiveComplexity

namespace BitSum

open Finset

/-! ### Splitting a count -/

/-- One more position, one more one to count if it is set. -/
theorem onesBelow_succ (x w : ℕ) :
    onesBelow x (w + 1) = onesBelow x w + (if x.testBit w = true then 1 else 0) := by
  classical
  rw [onesBelow, onesBelow, Finset.range_add_one, filter_insert]
  by_cases h : x.testBit w = true
  · rw [if_pos h, if_pos h, card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- The count only looks at the bits it counts. -/
theorem onesBelow_congr {x y w : ℕ} (h : ∀ i, i < w → x.testBit i = y.testBit i) :
    onesBelow x w = onesBelow y w := by
  rw [onesBelow, onesBelow]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  exact ⟨fun hi => ⟨hi.1, by rw [← h i hi.1]; exact hi.2⟩,
    fun hi => ⟨hi.1, by rw [h i hi.1]; exact hi.2⟩⟩

/-- **Cutting a count in two**: the ones below `k + c` are those below `k`,
plus those of the chunk that starts at `k`. This is the whole of the running
sum's step. -/
theorem onesBelow_add (x k : ℕ) : ∀ c : ℕ,
    onesBelow x (k + c) = onesBelow x k + onesBelow (x / 2 ^ k) c := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    have hk : k + (c + 1) = (k + c) + 1 := by omega
    have hbit : (x / 2 ^ k).testBit c = x.testBit (k + c) := by
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    rw [hk, onesBelow_succ, ih, onesBelow_succ, hbit]
    omega

/-- A window's own count does not see what the window cut off. -/
theorem onesBelow_mod (x c : ℕ) : onesBelow (x % 2 ^ c) c = onesBelow x c :=
  onesBelow_congr fun i hi => by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

/-! ### The running sum of a chunked word -/

section Sum

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The running sums of `x` along the chunks of length `c`**: `0` at the first
chunk, and one step adds the number of ones of the chunk just passed, as counted
by `Cnt`. The step is guarded like the counter's, and for the same reason. -/
def SumOk (c B x S : A) (Cnt : A → A → Prop) : Prop :=
  (∀ z b' s : A, orank z = 0 → orank z + orank c = orank b' → WindowAt z b' S s →
      orank s = 0) ∧
    ∀ b b' b'' s s' w : A, BitIx b B → orank b + orank c = orank b' →
      orank b' + orank c = orank b'' → IsLowIx b'' →
        WindowAt b b' S s → WindowAt b' b'' S s' → WindowAt b b' x w →
          ∃ n : A, Cnt w n ∧ orank s + orank n = orank s'

/-- **What the running sum says**: at the chunk starting at `b`, the window of
`S` holds the number of ones of `x` below `b`. The level below is used only
through its soundness and its totality. -/
theorem sum_eq {c B x S : A} {Cnt : A → A → Prop} (hc : 0 < orank c) (hB : IsBlockSet c B)
    (hS : SumOk c B x S Cnt)
    (hsound : ∀ w n : A, orank w < 2 ^ orank c → Cnt w n →
      orank n = onesBelow (orank w) (orank c)) :
    ∀ j : ℕ, ∀ b b' s : A, orank b = orank c * j → BitIx b B →
      orank b + orank c = orank b' → IsLowIx b' → WindowAt b b' S s →
        orank s = onesBelow (orank x) (orank b) := by
  intro j
  induction j with
  | zero =>
    intro b b' s hb _ hsum _ hwin
    rw [hS.1 b b' s (by omega) hsum hwin, hb]
    simp [onesBelow]
  | succ j ih =>
    intro b b' s hb hbit hsum hlow hwin
    -- the chunk below
    have hprev : orank c * j < Nat.card A := by
      have hmono : orank c * j ≤ orank c * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      have := orank_lt_card b
      omega
    obtain ⟨b₀, hb₀⟩ := exists_orank_eq (A := A) hprev
    have hb₀sum : orank b₀ + orank c = orank b := by
      rw [hb₀, hb, Nat.mul_succ]
    have hblow : IsLowIx b := by
      rw [IsLowIx] at hlow ⊢
      omega
    have hb₀bit : BitIx b₀ B :=
      (bitIx_iff_of_isBlockSet hc hB b₀).mpr ⟨⟨j, hb₀⟩, by
        rw [IsLowIx] at hblow ⊢
        omega⟩
    -- the running sum and the chunk value below
    obtain ⟨s₀, hs₀⟩ := exists_windowAt (b := b₀) (e := b) (x := S) (w := orank c) (by omega)
    obtain ⟨w, hw⟩ := exists_windowAt (b := b₀) (e := b) (x := x) (w := orank c) (by omega)
    obtain ⟨n, hn, hstep⟩ := hS.2 b₀ b b' s₀ s w hb₀bit hb₀sum hsum hlow hs₀ hwin hw
    have hih := ih b₀ b s₀ hb₀ hb₀bit hb₀sum hblow hs₀
    -- the chunk's count is the count of its window value
    have hwval : orank w = orank x / 2 ^ orank b₀ % 2 ^ orank c :=
      (windowAt_iff (by omega)).mp hw
    have hcount : orank n = onesBelow (orank x / 2 ^ orank b₀) (orank c) := by
      rw [hsound w n (by rw [hwval]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) hn, hwval,
        onesBelow_mod]
    have hsplit : onesBelow (orank x) (orank b) =
        onesBelow (orank x) (orank b₀) + onesBelow (orank x / 2 ^ orank b₀) (orank c) := by
      rw [← onesBelow_add]
      congr 1
      omega
    omega

/-- The count only grows with the window it is taken over. -/
theorem onesBelow_mono {x k k' : ℕ} (h : k ≤ k') : onesBelow x k ≤ onesBelow x k' :=
  Finset.card_le_card fun i hi => by
    simp only [mem_filter, mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩

/-- **A rank has no more ones than the universe has positions** – so a running
sum always fits in a field wide enough to hold `posCount`. -/
theorem onesBelow_orank_le (x : A) (k : ℕ) : onesBelow (orank x) k ≤ posCount A := by
  rcases Nat.le_total k (posCount A) with h | h
  · exact le_trans (onesBelow_le _ _) h
  · have hcut : onesBelow (orank x) k = onesBelow (orank x) (posCount A) := by
      rw [onesBelow, onesBelow]
      congr 1
      ext i
      simp only [mem_filter, mem_range]
      refine ⟨fun hi => ⟨?_, hi.2⟩, fun hi => ⟨by omega, hi.2⟩⟩
      by_contra hc
      rw [testBit_orank_eq_false (by omega)] at hi
      exact absurd hi.2 (by simp)
    rw [hcut]
    exact onesBelow_le _ _

/-- **The running sums exist**: the counts below the boundaries, packed into the
fields those boundaries delimit. The one capacity condition is that a field hold
a count of ones *of the word being counted* – weaker than the counter's, whose
values run to the number of chunks – and the layout is
`DescriptiveComplexity.BitSum.packVal`. -/
theorem exists_sumOk [Nonempty A] {c B x : A} {Cnt : A → A → Prop} (hc : 0 < orank c)
    (hB : IsBlockSet c B)
    (hsound : ∀ w n : A, orank w < 2 ^ orank c → Cnt w n →
      orank n = onesBelow (orank w) (orank c))
    (hcomp : ∀ w : A, orank w < 2 ^ orank c → ∃ n : A, Cnt w n)
    (hwide : ∀ k : ℕ, onesBelow (orank x) k < 2 ^ orank c) :
    ∃ S : A, SumOk c B x S Cnt := by
  set m := (posCount A - 1) / orank c with hm
  set f : ℕ → ℕ := fun j => onesBelow (orank x) (orank c * j) with hf
  have hffit : ∀ j, j < m → f j < 2 ^ orank c := fun j _ => hwide _
  have hPpos : 0 < posCount A := by
    rw [← two_pow_lt_card_iff_lt_posCount]
    have := orank_lt_card c
    simpa using by omega
  have hmg : m * orank c ≤ posCount A - 1 := by
    rw [hm]
    exact Nat.div_mul_le_self _ _
  have hcard : 2 ^ (posCount A - 1) < Nat.card A :=
    (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
  have hlt : packVal (orank c) f m < Nat.card A :=
    lt_of_lt_of_le (packVal_lt hffit)
      (le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hmg) hcard))
  obtain ⟨S, hS⟩ := exists_orank_eq (A := A) hlt
  -- every window of `S` at a chunk below `m` reads that chunk's count
  have hread : ∀ b b' s : A, ∀ j : ℕ, orank b = orank c * j → j < m →
      orank b + orank c = orank b' → WindowAt b b' S s → orank s = f j := by
    intro b b' s j hb hj hsum hwin
    rw [(windowAt_iff (w := orank c) (by omega)).mp hwin, hS, hb, Nat.mul_comm]
    exact packVal_window hffit hj
  refine ⟨S, fun z b' s hz hsum hwin => ?_, fun b b' b'' s s' w hbit hs1 hs2 hlow
    hw1 hw2 hw => ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [(windowAt_iff (w := orank c) (by omega)).mp hwin, hS, hm0]
      simp [packVal]
    · rw [hread z b' s 0 (by omega) hmpos hsum hwin, hf]
      simp
  · -- one step adds the count of the chunk just passed
    have hwval : orank w = orank x / 2 ^ orank b % 2 ^ orank c :=
      (windowAt_iff (by omega)).mp hw
    obtain ⟨n, hn⟩ := hcomp w (by rw [hwval]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    refine ⟨n, hn, ?_⟩
    obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hc hB b).mp hbit
    have hjm : j + 2 ≤ m := by
      rw [IsLowIx] at hlow
      rw [hm]
      refine Nat.le_div_iff_mul_le hc |>.mpr ?_
      have hcomm : (j + 2) * orank c = orank c * (j + 2) := Nat.mul_comm _ _
      have hb'' : orank c * (j + 2) = orank c * j + orank c + orank c := by ring
      omega
    have hb' : orank b' = orank c * (j + 1) := by rw [Nat.mul_succ]; omega
    rw [hread b b' s j hj (by omega) hs1 hw1, hread b' b'' s' (j + 1) hb' (by omega) hs2 hw2]
    have hcount : orank n = onesBelow (orank x / 2 ^ orank b) (orank c) := by
      rw [hsound w n (by rw [hwval]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) hn, hwval,
        onesBelow_mod]
    have hsplit : f (j + 1) = f j + onesBelow (orank x / 2 ^ orank b) (orank c) := by
      rw [hf]
      simp only
      rw [← hj, ← onesBelow_add]
      congr 1
      omega
    omega

end Sum

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **The running sum is first-order in the bit logic**, given that the level
below is: the parameter `Cnt` is a family of relations with one distinguished
variable – the size the level below works at – which is what both instantiations
need. -/
theorem bitDef_sumOk
    {Cnt : ∀ (A : Type) [LinearOrder A] [Finite A], A → A → A → Prop}
    (hCnt : ∀ {β : Type} (p w n : β), BitDef (L := L) (α := β)
      fun A _ _ _ _ v => Cnt A (v p) (v w) (v n))
    (p c B x S : α) :
    BitDef (L := L) (α := α)
      fun A _ _ _ _ v => SumOk (v c) (v B) (v x) (v S) (Cnt A (v p)) := by
  have hbase : BitDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ z b' s : A,
      orank z = 0 → orank z + orank (v c) = orank b' → WindowAt z b' (v S) s →
        orank s = 0) := by
    refine (((bitDef_isZero (L := L) (α := α ⊕ Fin 3) (Sum.inr 0)).imp <|
      (bitDef_plus (Sum.inr 0) (Sum.inl c) (Sum.inr 1)).imp <|
        (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl S) (Sum.inr 2)).imp <|
          bitDef_isZero (Sum.inr 2)).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h z b' s => h ![z, b', s], fun h u => h (u 0) (u 1) (u 2)⟩
  have hstep : BitDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ b b' b'' s s' w : A,
      BitIx b (v B) → orank b + orank (v c) = orank b' →
        orank b' + orank (v c) = orank b'' → IsLowIx b'' →
          WindowAt b b' (v S) s → WindowAt b' b'' (v S) s' → WindowAt b b' (v x) w →
            ∃ n : A, Cnt A (v p) w n ∧ orank s + orank n = orank s') := by
    have hcount : BitDef (L := L) (α := α ⊕ Fin 6) (fun A _ _ _ _ u => ∃ n : A,
        Cnt A (u (Sum.inl p)) (u (Sum.inr 5)) n ∧
          orank (u (Sum.inr 3)) + orank n = orank (u (Sum.inr 4))) :=
      ((hCnt (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr 5)) (Sum.inr 0)).and
        (bitDef_plus (Sum.inl (Sum.inr 3)) (Sum.inr 0) (Sum.inl (Sum.inr 4)))).ex
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 6) (Sum.inr 0) (Sum.inl B)).imp <|
      (bitDef_plus (Sum.inr 0) (Sum.inl c) (Sum.inr 1)).imp <|
        (bitDef_plus (Sum.inr 1) (Sum.inl c) (Sum.inr 2)).imp <|
          (bitDef_isLowIx (Sum.inr 2)).imp <|
            (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl S) (Sum.inr 3)).imp <|
              (bitDef_windowAt (Sum.inr 1) (Sum.inr 2) (Sum.inl S) (Sum.inr 4)).imp <|
                (bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl x) (Sum.inr 5)).imp
                  hcount).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h b b' b'' s s' w => h ![b, b', b'', s, s', w],
      fun h u => h (u 0) (u 1) (u 2) (u 3) (u 4) (u 5)⟩
  exact (hbase.and hstep).congr fun _ _ _ _ _ _ => Iff.rfl

end Definability

end BitSum

end DescriptiveComplexity
