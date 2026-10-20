/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.BitSum.Level2
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (BitIx orank posCount)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Level 1: counting all the ones of an element

The top of the Bit Sum Lemma, and the same running sum once more, with level 2
in the place level 3 occupied at level 2: cut the whole tape into blocks of
`DescriptiveComplexity.BitSum.lvl1Block` positions, keep the running count in
each, and let `DescriptiveComplexity.BitSum.PopMid` count one block.

> `DescriptiveComplexity.BitSum.PopAll x y`: `y` is the number of ones of `x`.

This is the Bit Sum Lemma, `BSUM`, and everything above it in the section is
about *using* it rather than proving it.

## The one thing this level has that the others do not: a tail

Levels 2 and 3 count a word that is short compared with the tape, so their walk
can run past the end of the word and stop at a boundary with room to spare. Level
1 counts a word as long as the tape itself, and above the top position an element
has no bits to pack a running sum into. So the last block is handled separately:
the certificate reads the running sum at a boundary `b`, then counts the rest of
`x` – the window from `b` to any index past the top – as **one more chunk**, with
the same `PopMid` that verifies the steps, and adds the two.

That is why the statement takes no word-length parameter: the tail makes the
count total by construction, and the answer is the number of ones of `x`, full
stop.
-/

namespace Lax895169Proofs.DescriptiveComplexity

namespace BitSum

/-! ### The level -/

section Level1

variable {A : Type} [LinearOrder A] [Finite A]

/-- **`y` is the number of ones of `x`** – the Bit Sum Lemma's certificate: a
block length, the boundaries, the running sums, a boundary `b` at which the sum
is read, and the tail of `x` above `b` counted as one more chunk. -/
def PopAll (x y : A) : Prop :=
  ∃ l B S b b' e d w s n : A,
    Lax895169.BitPredicate.orank l ≠ 0 ∧ IsLowIx l ∧ IsBlockSet l B ∧ SumOk l B x S (PopMid l) ∧
      Lax895169.BitPredicate.BitIx b B ∧ Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank l = Lax895169.BitPredicate.orank b' ∧ IsLowIx b' ∧ WindowAt b b' S s ∧
        (∃ t : A, IsTopIx t ∧ t < e) ∧ Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank d = Lax895169.BitPredicate.orank e ∧
          WindowAt b e x w ∧ PopMid d w n ∧ Lax895169.BitPredicate.orank s + Lax895169.BitPredicate.orank n = Lax895169.BitPredicate.orank y

/-- **The certificate is sound**: the running sum at `b` counts the ones below
`b`, the tail counts the rest, and there is no rest above the top position. As at
level 2, no size condition is needed – the block length is guessed, and soundness
holds for whichever one is. -/
theorem popAll_sound {x y : A} (h : PopAll x y) :
    Lax895169.BitPredicate.orank y = onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.posCount A) := by
  obtain ⟨l, B, S, b, b', e, d, w, s, n, hl0, hllow, hB, hS, hbB, hsum, hlow', hwin,
    ⟨t, ht, hte⟩, hde, hxw, hn, hy⟩ := h
  have hlpos : 0 < Lax895169.BitPredicate.orank l := by omega
  have hlP : Lax895169.BitPredicate.orank l < Lax895169.BitPredicate.posCount A := by
    rw [IsLowIx] at hllow
    omega
  -- the running sum below `b`
  obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hlpos hB b).mp hbB
  have hs := sum_eq hlpos hB hS
    (fun u m hu hm => popMid_sound (fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) hi))) hm)
    j b b' s hj hbB hsum hlow' hwin
  -- the tail above `b`
  have hwval : Lax895169.BitPredicate.orank w = Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b % 2 ^ Lax895169.BitPredicate.orank d :=
    (windowAt_iff (w := Lax895169.BitPredicate.orank d) (by omega)).mp hxw
  have hnval : Lax895169.BitPredicate.orank n = onesBelow (Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b) (Lax895169.BitPredicate.orank d) := by
    rw [popMid_sound (m := d) (x := w) (fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by
        rw [hwval]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by norm_num) hi))) hn, hwval, onesBelow_mod]
  -- the tail reaches past the top position
  have hetop : Lax895169.BitPredicate.posCount A ≤ Lax895169.BitPredicate.orank e := by
    rw [IsTopIx] at ht
    have := orank_lt_orank hte
    omega
  have hxbits : ∀ i, Lax895169.BitPredicate.posCount A ≤ i → (Lax895169.BitPredicate.orank x).testBit i = false := fun i hi =>
    testBit_orank_eq_false hi
  have hsplit : onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank e) =
      onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank b) + onesBelow (Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b) (Lax895169.BitPredicate.orank d) := by
    rw [← onesBelow_add]
    congr 1
    omega
  rw [← onesBelow_eq_of_ge hxbits hetop, hsplit, ← hs, ← hnval]
  omega

/-- **The certificate exists**: the block length of
`DescriptiveComplexity.LogTime.BitSum.Sizes`, the boundaries at that gap, the
running sums, the last boundary that still has room for its field, and the tail
of `x` above it counted as one more chunk by level 2. -/
theorem exists_popAll [Nonempty A] {x : A} (hP : 2 ^ 20 ≤ Lax895169.BitPredicate.posCount A) :
    ∃ y : A, PopAll x y := by
  classical
  have hcard := posCount_lt_card (A := A)
  set P := Lax895169.BitPredicate.posCount A with hPdef
  set K := lvl1Block P with hK
  have hK2 : 2 ≤ K := two_le_lvl1Block hP
  have hroom := lvl1_room hP
  have hKsucc := lvl1Block_succ_lt hP
  -- the block length, as an element
  obtain ⟨l, hl⟩ := exists_orank_eq (A := A) (m := K) (by omega)
  have hlpos : 0 < Lax895169.BitPredicate.orank l := by omega
  have hllow : IsLowIx l := by rw [IsLowIx, hl]; omega
  -- level 2 counts a block, and a tail of two blocks
  have hmid : ∀ d w : A, Lax895169.BitPredicate.orank d ≤ 2 * K + 2 → Lax895169.BitPredicate.orank w < 2 ^ Lax895169.BitPredicate.orank d →
      ∃ n : A, PopMid d w n := by
    intro d w hd hw
    refine exists_popMid hP ?_ ?_ (fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hi)))
    · rw [← hPdef]
      have := two_lvl1Block_lt_two_pow_lvl2Block hP
      omega
    · rw [← hPdef]
      have hlt : lvl2Block P < lvl1Block P := lvl2Block_lt_lvl1Block hP
      omega
  obtain ⟨B, hB⟩ := exists_isBlockSet (A := A) (g := l) (by omega)
  obtain ⟨S, hS⟩ := exists_sumOk (x := x) hlpos hB
    (fun w n hw hn => popMid_sound (fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hi))) hn)
    (fun w hw => hmid l w (by omega) (by rw [hl] at hw ⊢; omega))
    (fun k => lt_of_le_of_lt (onesBelow_orank_le x k)
      (by rw [hl]; exact lt_two_pow_lvl1Block P))
  -- the last boundary whose field still fits
  set j := (P - 2 - K) / K with hj
  have hble : K * j ≤ P - 2 - K := by
    rw [hj, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hbgt : P - 2 - 2 * K < K * j := by
    have hmod := Nat.div_add_mod (P - 2 - K) K
    have hlt : (P - 2 - K) % K < K := Nat.mod_lt _ (by omega)
    have hcomm : K * ((P - 2 - K) / K) = (P - 2 - K) / K * K := Nat.mul_comm _ _
    rw [hj]
    omega
  obtain ⟨b, hb⟩ := exists_orank_eq (A := A) (m := K * j) (by omega)
  obtain ⟨b', hb'⟩ := exists_orank_eq (A := A) (m := K * j + K) (by omega)
  have hblow : IsLowIx b := by rw [IsLowIx, hb]; omega
  have hb'low : IsLowIx b' := by rw [IsLowIx, hb']; omega
  have hbB : Lax895169.BitPredicate.BitIx b B :=
    (bitIx_iff_of_isBlockSet hlpos hB b).mpr ⟨⟨j, by rw [hl]; exact hb⟩, hblow⟩
  obtain ⟨s, hs⟩ := exists_windowAt (b := b) (e := b') (x := S) (w := Lax895169.BitPredicate.orank l) (by omega)
  -- the tail, from the last boundary to just past the top position
  obtain ⟨e, he⟩ := exists_orank_eq (A := A) (m := P) (by omega)
  obtain ⟨d, hd⟩ := exists_orank_eq (A := A) (m := P - K * j) (by omega)
  obtain ⟨t, ht⟩ := exists_orank_eq (A := A) (m := P - 1) (by omega)
  obtain ⟨w, hw⟩ := exists_windowAt (b := b) (e := e) (x := x) (w := Lax895169.BitPredicate.orank d) (by omega)
  have hwlt : Lax895169.BitPredicate.orank w < 2 ^ Lax895169.BitPredicate.orank d := by
    rw [(windowAt_iff (w := Lax895169.BitPredicate.orank d) (by omega)).mp hw]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨n, hn⟩ := hmid d w (by omega) hwlt
  -- the answer
  have hsum : Lax895169.BitPredicate.orank s + Lax895169.BitPredicate.orank n < Nat.card A := by
    have hwval : Lax895169.BitPredicate.orank w = Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b % 2 ^ Lax895169.BitPredicate.orank d :=
      (windowAt_iff (w := Lax895169.BitPredicate.orank d) (by omega)).mp hw
    have h2 : Lax895169.BitPredicate.orank n = onesBelow (Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b) (Lax895169.BitPredicate.orank d) := by
      rw [popMid_sound (m := d) (x := w) (fun i hi => Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hwlt (Nat.pow_le_pow_right (by norm_num) hi))) hn, hwval, onesBelow_mod]
    have h3 : Lax895169.BitPredicate.orank s = onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank b) := by
      obtain ⟨⟨jb, hjb⟩, -⟩ := (bitIx_iff_of_isBlockSet hlpos hB b).mp hbB
      exact sum_eq hlpos hB hS (fun u m hu hm => popMid_sound (fun i hi =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) hi))) hm)
        jb b b' s hjb hbB (by omega) hb'low hs
    have hadd : onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank b) + onesBelow (Lax895169.BitPredicate.orank x / 2 ^ Lax895169.BitPredicate.orank b) (Lax895169.BitPredicate.orank d)
        = onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank d) := (onesBelow_add _ _ _).symm
    have hle : onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank d) ≤ Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank d :=
      onesBelow_le _ _
    omega
  obtain ⟨y, hy⟩ := exists_orank_eq (A := A) hsum
  exact ⟨y, l, B, S, b, b', e, d, w, s, n, by omega, hllow, hB, hS, hbB, by omega,
    hb'low, hs, ⟨t, by rw [IsTopIx, ht]; omega, lt_of_orank_lt (by rw [ht, he]; omega)⟩,
    by omega, hw, hn, by omega⟩

end Level1

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **The Bit Sum Lemma is a formula**: level 2 enters it twice – once as the
chunk counter of the running sum, once to count the tail. -/
theorem bitDef_popAll (x y : α) :
    BitDef (L := L) fun _ _ _ _ _ v => PopAll (v x) (v y) := by
  have htop : BitDef (L := L) (α := α ⊕ Fin 10)
      (fun A _ _ _ _ u => ∃ t : A, IsTopIx t ∧ t < u (Sum.inr 4)) :=
    ((bitDef_isTopIx (L := L) (α := (α ⊕ Fin 10) ⊕ Fin 1) (Sum.inr 0)).and
      (bitDef_lt (Sum.inr 0) (Sum.inl (Sum.inr 4)))).ex
  have hbody : BitDef (L := L) (α := α ⊕ Fin 10) (fun A _ _ _ _ u =>
      Lax895169.BitPredicate.orank (u (Sum.inr 0)) ≠ 0 ∧ IsLowIx (u (Sum.inr 0)) ∧
        IsBlockSet (u (Sum.inr 0)) (u (Sum.inr 1)) ∧
          SumOk (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inl x)) (u (Sum.inr 2))
              (PopMid (u (Sum.inr 0))) ∧
            Lax895169.BitPredicate.BitIx (u (Sum.inr 3)) (u (Sum.inr 1)) ∧
              Lax895169.BitPredicate.orank (u (Sum.inr 3)) + Lax895169.BitPredicate.orank (u (Sum.inr 0)) = Lax895169.BitPredicate.orank (u (Sum.inr 9)) ∧
                IsLowIx (u (Sum.inr 9)) ∧
                  WindowAt (u (Sum.inr 3)) (u (Sum.inr 9)) (u (Sum.inr 2)) (u (Sum.inr 7)) ∧
                    (∃ t : A, IsTopIx t ∧ t < u (Sum.inr 4)) ∧
                      Lax895169.BitPredicate.orank (u (Sum.inr 3)) + Lax895169.BitPredicate.orank (u (Sum.inr 5)) = Lax895169.BitPredicate.orank (u (Sum.inr 4)) ∧
                        WindowAt (u (Sum.inr 3)) (u (Sum.inr 4)) (u (Sum.inl x))
                            (u (Sum.inr 6)) ∧
                          PopMid (u (Sum.inr 5)) (u (Sum.inr 6)) (u (Sum.inr 8)) ∧
                            Lax895169.BitPredicate.orank (u (Sum.inr 7)) + Lax895169.BitPredicate.orank (u (Sum.inr 8)) =
                              Lax895169.BitPredicate.orank (u (Sum.inl y))) :=
    (bitDef_isZero (Sum.inr 0)).not.and <|
      (bitDef_isLowIx (Sum.inr 0)).and <|
        (bitDef_isBlockSet (Sum.inr 0) (Sum.inr 1)).and <|
          (bitDef_sumOk (Cnt := fun _ _ _ p w n => PopMid p w n)
            (fun p w n => bitDef_popMid p w n)
            (Sum.inr 0) (Sum.inr 0) (Sum.inr 1) (Sum.inl x) (Sum.inr 2)).and <|
            (bitDef_bit (Sum.inr 3) (Sum.inr 1)).and <|
              (bitDef_plus (Sum.inr 3) (Sum.inr 0) (Sum.inr 9)).and <|
                (bitDef_isLowIx (Sum.inr 9)).and <|
                  (bitDef_windowAt (Sum.inr 3) (Sum.inr 9) (Sum.inr 2) (Sum.inr 7)).and <|
                    htop.and <|
                      (bitDef_plus (Sum.inr 3) (Sum.inr 5) (Sum.inr 4)).and <|
                        (bitDef_windowAt (Sum.inr 3) (Sum.inr 4) (Sum.inl x)
                          (Sum.inr 6)).and <|
                          (bitDef_popMid (Sum.inr 5) (Sum.inr 6) (Sum.inr 8)).and
                            (bitDef_plus (Sum.inr 7) (Sum.inr 8) (Sum.inl y))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u 0, u 1, u 2, u 3, u 9, u 4, u 5, u 6, u 7, u 8, h⟩
  · rintro ⟨l, B, S, b, b', e, d, w, s, n, h⟩
    exact ⟨![l, B, S, b, e, d, w, s, n, b'], h⟩

end Definability

end BitSum

end Lax895169Proofs.DescriptiveComplexity


