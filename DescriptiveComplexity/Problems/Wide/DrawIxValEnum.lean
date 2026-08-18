/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawValEnum
import DescriptiveComplexity.Problems.Wide.DrawRunVar
import DescriptiveComplexity.Problems.Wide.BlkLayout

/-!
# The VAL loop's enumeration at an arbitrary file

`DescriptiveComplexity.Draw.Data.exists_valEnum` builds the chain the VAL loop
runs through, over the *elements* of the instance. A program whose registers are
not the elements needs the same chain over its **registers**, and that is this
file: the elementwise chain pulled back along `elt`
(`DescriptiveComplexity.ixMark`), which is an increment chain again because the
correspondence carries increments both ways
(`DescriptiveComplexity.wmIncr_ixMark`).

What the pull-back asks of the file is one thing, and it is the same thing the
legs ask: every **inner** element is the element of a used register. At the
elementwise file it is trivial, and at a laid file it is
`DescriptiveComplexity.Draw.Data.ixHolds_blkLaid`.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {I : Type} [Finite I] {ile : I → I → Prop}
variable {elt : I → Univ A R P dt.KIx dt.dd} {Use : I → Prop}
variable {blkOf : I → Option dt.KIx}

variable {dt}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] in
/-- **An increment chain is strictly increasing**: each cover is an increment,
hence a strict step, and the order on marks is linear, so the steps compose.
The elementwise `wmChain_lt` is this at the addresses. -/
theorem chain_lt_of_covers {n : ℕ} {mV : Fin (n + 1) → I → Prop}
    (hix : IsLinOrd ile)
    (hcov : ∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr ile (mV a) (mV a'))
    {a a' : Fin (n + 1)} (hlt : a < a') : WMSetLt ile (mV a) (mV a') := by
  have hset := isLinOrd_wmSetLe hix
  have hstep : ∀ (d : ℕ) (b b' : Fin (n + 1)), (b' : ℕ) = (b : ℕ) + d + 1 →
      WMSetLt ile (mV b) (mV b') := by
    intro d
    induction d with
    | zero =>
      intro b b' hb
      have hcv := hcov b b' (by
        change (b : ℕ) < (b' : ℕ)
        omega) (fun c hc => by
        have h1' : (b : ℕ) < (c : ℕ) := hc.1
        have h2' : (c : ℕ) < (b' : ℕ) := hc.2
        omega)
      exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hcv, ne_of_wmIncr hcv⟩
    | succ d ihd =>
      intro b b' hb
      have hmn : (b : ℕ) + d + 1 < n + 1 := by have := b'.isLt; omega
      set m : Fin (n + 1) := ⟨(b : ℕ) + d + 1, hmn⟩ with hm
      have hmv : (m : ℕ) = (b : ℕ) + d + 1 := rfl
      have hbm := ihd b m rfl
      have hmb' : WMSetLt ile (mV m) (mV b') := by
        have hcv := hcov m b' (by
          change (m : ℕ) < (b' : ℕ)
          omega) (fun c hc => by
          have h1' : (m : ℕ) < (c : ℕ) := hc.1
          have h2' : (c : ℕ) < (b' : ℕ) := hc.2
          omega)
        exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hcv, ne_of_wmIncr hcv⟩
      rw [wmSetLt_iff] at hbm hmb' ⊢
      refine ⟨hset.2.1 _ _ _ hbm.1 hmb'.1, fun hc => ?_⟩
      exact hmb'.2 (hset.2.2.1 _ _ hmb'.1 (hc ▸ hbm.1))
  have hab : (a : ℕ) < (a' : ℕ) := hlt
  exact hstep ((a' : ℕ) - (a : ℕ) - 1) a a' (by omega)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] in
/-- **A chain of marks is no longer than the marks it can use**: an increment
chain supported on a set `S` of registers is injective into the subsets of `S`,
so its length is at most `2 ^ |S|`. This is what bounds the VAL loop's *number
of rounds* – the second factor the clock compares – by the inner registers
alone, and not by the whole file. -/
theorem chain_length_le_two_pow {n : ℕ} {mV : Fin (n + 1) → I → Prop}
    {S : I → Prop}
    (hinjV : Function.Injective mV)
    (hsupp : ∀ (a : Fin (n + 1)) (u : I), mV a u → S u) :
    n + 1 ≤ 2 ^ Nat.card {u : I // S u} := by
  classical
  have hinj : Function.Injective
      (fun (a : Fin (n + 1)) (u : {u : I // S u}) => mV a u.1) := by
    intro a a' h
    refine hinjV (funext fun u => ?_)
    by_cases hu : S u
    · exact congrFun h ⟨u, hu⟩
    · exact propext ⟨fun hc => absurd (hsupp a u hc) hu,
        fun hc => absurd (hsupp a' u hc) hu⟩
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_fun] at hcard
  have htwo : Nat.card Prop = 2 :=
    Nat.card_eq_two_iff.mpr ⟨True, False, by simp,
      Set.eq_univ_of_forall fun p => by by_cases h : p <;> simp [h, eq_true, eq_false]⟩
  rwa [htwo] at hcard

/-- **The VAL loop's enumeration at an arbitrary file**: the same chain
`DescriptiveComplexity.Draw.Data.exists_valEnum` gives over the elements, read
at the registers – it starts empty, each cover is a machine increment of the
*index* order, the top passes the exhaustion test at every register and no
earlier mark does. -/
theorem exists_ixValEnum
    (hinj : Function.Injective elt)
    (hmono : ∀ u u', WMLt ile u u' ↔ WMLt WMLe (elt u) (elt u'))
    (hblk : ∀ u, blkOf u = tagBlk (elt u).1)
    (hheld : ∀ x : Univ A R P dt.KIx dt.dd,
      (∃ j : Fin dt.ki, x.1 = argIn dt.ko j) → ∃ u, Use u ∧ elt u = x)
    (hix : IsLinOrd ile)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (I → Prop)),
      mV 0 = (fun _ => False) ∧
      (∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
        WMIncr ile (mV a) (mV a')) ∧
      (∀ u, dt.InnerFull blkOf (mV (Fin.last n)) u) ∧
      (∀ a, a < Fin.last n → ∃ u, ¬dt.InnerFull blkOf (mV a) u) ∧
      (∀ (a : Fin (n + 1)) (u : I), mV a u →
        ∃ j : Fin dt.ki, blkOf u = some (Sum.inr j)) ∧
      Function.Injective mV := by
  classical
  obtain ⟨n, mA, h0, hIncrA, hTopA, hFailA, hKin⟩ :=
    exists_valEnum (dt := dt) (A := A) (R := R) (P := P) hlin hord
  -- every mark of the chain is held by the file's registers: its elements are
  -- inner ones, and the file has a register for each
  have hheldA : ∀ a : Fin (n + 1), IxHolds elt Use (mA a) := by
    intro a x hx
    obtain ⟨j, hj⟩ := hKin a x.1 x.2 (by exact hx)
    exact hheld x ⟨j, hj⟩
  -- a register is inner exactly when the element it stands for is
  have hinner : ∀ u : I, (∃ j : Fin dt.ki, blkOf u = some (Sum.inr j)) ↔
      ∃ j : Fin dt.ki, tagBlk (elt u).1 = some (Sum.inr j) := by
    intro u
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [← hblk u]; exact hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hblk u]; exact hj⟩
  have hcov : ∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr ile (ixMark elt (mA a)) (ixMark elt (mA a')) :=
    fun a a' hlt hnb => wmIncr_ixMark hinj hmono (hheldA a') (hIncrA a a' hlt hnb)
  refine ⟨n, fun a => ixMark elt (mA a), ?_, hcov, ?_, ?_, ?_, ?_⟩
  · change ixMark elt (mA 0) = fun _ => False
    rw [h0]
    rfl
  · intro u
    have h : mA (Fin.last n) (elt u) ↔
        ∃ j : Fin dt.ki, tagBlk (elt u).1 = some (Sum.inr j) := hTopA (elt u)
    exact h.trans (hinner u).symm
  · intro a ha
    obtain ⟨x, hx⟩ := hFailA a ha
    have hx : ¬(mA a x ↔ ∃ j : Fin dt.ki, tagBlk x.1 = some (Sum.inr j)) := hx
    -- the failing element is an inner one: everything the mark holds is inner,
    -- so a failure is an unmarked inner element
    have hxin : ∃ j : Fin dt.ki, tagBlk x.1 = some (Sum.inr j) := by
      by_contra hc
      exact hx ⟨fun hm => absurd (hKin a x.1 x.2 hm) (by
        rintro ⟨j, hj⟩
        exact hc ⟨j, by rw [hj]; rfl⟩), fun h => absurd h hc⟩
    obtain ⟨j, hj⟩ := hxin
    have hxarg : ∃ j : Fin dt.ki, x.1 = argIn dt.ko j := by
      match hx1 : x.1 with
      | .arg i =>
        rcases h' : ofLex i with k | j'
        · exact absurd hj (by rw [hx1, tagBlk, h']; exact fun hc => nomatch hc)
        · exact ⟨j', congrArg Tag.arg (congrArg toLex h')⟩
      | .sym => exact absurd hj (by rw [hx1]; exact fun hc => nomatch hc)
      | .ctrl _ => exact absurd hj (by rw [hx1]; exact fun hc => nomatch hc)
      | .phase _ => exact absurd hj (by rw [hx1]; exact fun hc => nomatch hc)
    obtain ⟨u, _hu, rfl⟩ := hheld x hxarg
    refine ⟨u, fun hc => hx ?_⟩
    exact (show ixMark elt (mA a) u ↔ ∃ j : Fin dt.ki, blkOf u = some (Sum.inr j)
      from hc).trans (hinner u)
  · -- every mark of the chain holds inner registers alone
    intro a u hu
    exact (hinner u).mpr (by
      obtain ⟨j, hj⟩ := hKin a (elt u).1 (elt u).2 (by
        exact (show mA a (elt u) from hu))
      exact ⟨j, by rw [hj]; rfl⟩)
  · -- and the chain is injective, its steps being strict
    intro a a' hEq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · exact ((wmSetLt_iff _ _).mp (chain_lt_of_covers hix hcov hab)).2 hEq
    · exact ((wmSetLt_iff _ _).mp (chain_lt_of_covers hix hcov hab)).2 hEq.symm

/-- **The VAL loop's enumeration at the file a clocked program lays**: the
general chain at `DescriptiveComplexity.Draw.Data.blkLaid`, whose four
coherences are the layout's own. -/
theorem exists_blkValEnum [Finite dt.KIx]
    (h : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R P dt.KIx dt.dd) //
        (wideData (Univ A R P dt.KIx dt.dd)).Posn p})
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (Wide.BlkIx dt.KIx A dt.dd → Prop)),
      mV 0 = (fun _ => False) ∧
      (∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
        WMIncr (dt.blkLaid h hpos hbase).le (mV a) (mV a')) ∧
      (∀ u, dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV (Fin.last n)) u) ∧
      (∀ a, a < Fin.last n → ∃ u,
        ¬dt.InnerFull (dt.blkLaid h hpos hbase).blk (mV a) u) ∧
      (∀ (a : Fin (n + 1)) (u : Wide.BlkIx dt.KIx A dt.dd), mV a u →
        ∃ j : Fin dt.ki, (dt.blkLaid h hpos hbase).blk u = some (Sum.inr j)) ∧
      Function.Injective mV :=
  exists_ixValEnum (Use := BlkIxUse A dt.KIx dt.dd)
    (fun _ _ hc => blkIxElt_inj (R := R) (P := P) (dd := dt.dd) hc)
    (fun u u' => blkIxElt_mono (R := R) (P := P) (dd := dt.dd) hord u u')
    (fun u => dt.blk_blkLaid_eq_tagBlk h hpos hbase u)
    (fun x hx => by
      obtain ⟨j, hj⟩ := hx
      exact ⟨(some (toLex (Sum.inr j)), x.2), ⟨_, rfl⟩, Prod.ext hj.symm rfl⟩)
    (Wide.isLinOrd_blkLe dt.KIx A dt.dd) h hord

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite R]
  [Finite P] in
/-- **The inner registers are one block of tuples per inner index**: at most
`kᵢ · m` of them, `m` being the tuples. -/
theorem card_blkInner_le [Finite dt.KIx] :
    Nat.card {u : Wide.BlkIx dt.KIx A dt.dd //
        ∃ j : Fin dt.ki, u.1 = some (Sum.inr j)} ≤
      dt.ki * Nat.card (Fin dt.dd → A) := by
  classical
  have hinj : Function.Injective
      (fun u : {u : Wide.BlkIx dt.KIx A dt.dd // ∃ j : Fin dt.ki, u.1 = some (Sum.inr j)} =>
        (u.2.choose, u.1.2)) := by
    rintro ⟨⟨b, t⟩, hb⟩ ⟨⟨b', t'⟩, hb'⟩ hEq
    have h1 : hb.choose = hb'.choose := congrArg Prod.fst hEq
    have h2 : t = t' := congrArg Prod.snd hEq
    exact Subtype.ext (Prod.ext (by rw [hb.choose_spec, hb'.choose_spec, h1]) h2)
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_fin] at hle

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite R]
  [Finite P] in
/-- **The VAL loop's rounds fit the clock**: the chain is supported on the inner
registers alone, so it has at most `2 ^ (kᵢ · m) ≤ 2 ^ (k · m)` rounds – the
second of the two factors
`DescriptiveComplexity.Draw.Data.nexTotal_lt_two_pow'` compares, the first
being the width (`DescriptiveComplexity.Draw.Data.ixLegWidth_le`). -/
theorem blkValEnum_rounds_le [Finite dt.KIx]
    {n : ℕ} {mV : Fin (n + 1) → (Wide.BlkIx dt.KIx A dt.dd → Prop)}
    (hinjV : Function.Injective mV)
    (hsupp : ∀ (a : Fin (n + 1)) (u : Wide.BlkIx dt.KIx A dt.dd), mV a u →
      ∃ j : Fin dt.ki, u.1 = some (Sum.inr j)) :
    n + 1 ≤ 2 ^ (Nat.card dt.KIx * Nat.card (Fin dt.dd → A)) := by
  classical
  have hki : dt.ki ≤ Nat.card dt.KIx := by
    have := Nat.card_le_card_of_injective
      (fun j : Fin dt.ki => (Sum.inr j : dt.KIx)) (fun _ _ hc => Sum.inr_injective hc)
    rwa [Nat.card_fin] at this
  refine le_trans (chain_length_le_two_pow (S := fun u : Wide.BlkIx dt.KIx A dt.dd =>
    ∃ j : Fin dt.ki, u.1 = some (Sum.inr j)) hinjV hsupp) ?_
  exact Nat.pow_le_pow_right (by norm_num)
    (le_trans (card_blkInner_le (dt := dt) (A := A))
      (Nat.mul_le_mul_right _ hki))

end Data

end Draw

end DescriptiveComplexity
