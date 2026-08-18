/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRunVar
import DescriptiveComplexity.Problems.Wide.Roam

/-!
# The VAL loop's enumeration

The variable machinery's VAL loop starts at the empty register, increments
one address at a time, and stops at the first register content its
exhaustion test accepts – the *Kin top*, the set of the inner-block
elements. The enumeration
`DescriptiveComplexity.Draw.Data.var_run` consumes is therefore an
initial segment of the binary-counter order on subsets, indexed by
`Fin (n + 1)` – which carries the `LinearOrder` and `Finite` instances the
run theorem demands, with no subtype order in sight.

This file builds it: `DescriptiveComplexity.exists_wmChain` – every subset
is reachable from the empty one by a finite chain of increments, by strong
induction on the address rank (`DescriptiveComplexity.bitRank`, the same
measure `DescriptiveComplexity.reaches_of_wideRounds` walks) –
`DescriptiveComplexity.wmChain_lt`, the chain's strict monotonicity, and
`DescriptiveComplexity.Draw.Data.exists_valEnum`, the package in exactly
the run theorem's hypothesis forms.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Chain

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-- **Every subset is reachable from the empty one by increments**: a
finite chain, each step the binary increment of the address, ending at the
target. By strong induction on the address rank. -/
theorem exists_wmChain (h : IsLinOrd (WMLe (A := A))) (target : A → Prop) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (A → Prop)),
      mV 0 = (fun _ => False) ∧ mV (Fin.last n) = target ∧
      ∀ k : Fin n, WMIncr WMLe (mV k.castSucc) (mV k.succ) := by
  classical
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  suffices key : ∀ (k : ℕ) (s : A → Prop),
      bitRank (wideData A).Le (wideData A).Posn (Sum.inl s : WPoint A) = k →
      ∃ (n : ℕ) (mV : Fin (n + 1) → (A → Prop)),
        mV 0 = (fun _ => False) ∧ mV (Fin.last n) = s ∧
        ∀ j : Fin n, WMIncr WMLe (mV j.castSucc) (mV j.succ) from
    key _ target rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hrank
    rcases Classical.em (∃ x, s x) with hne | hemp
    · -- the target has a predecessor: extend its chain by one
      obtain ⟨p, hp⟩ := exists_wmPred h hne
      have hb : bitRank (wideData A).Le (wideData A).Posn
          (Sum.inl s : WPoint A) =
          bitRank (wideData A).Le (wideData A).Posn (Sum.inl p) + 1 :=
        bitRank_succPos hlin ((succPos_wpLe_iff h p s).mpr hp)
      obtain ⟨n, mV, h0, hlast, hchain⟩ :=
        ih (bitRank (wideData A).Le (wideData A).Posn (Sum.inl p))
          (by omega) p rfl
      refine ⟨n + 1, Fin.snoc mV s, ?_, ?_, ?_⟩
      · rw [show (0 : Fin (n + 2)) = Fin.castSucc 0 from rfl,
          Fin.snoc_castSucc]
        exact h0
      · rw [Fin.snoc_last]
      · intro j
        by_cases hj : (j : ℕ) < n
        · have h1 : (j.succ : Fin (n + 2)) =
              Fin.castSucc (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) :=
            Fin.ext rfl
          have h2 : (j.castSucc : Fin (n + 2)) =
              Fin.castSucc (⟨(j : ℕ), by omega⟩ : Fin (n + 1)) :=
            Fin.ext rfl
          rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_castSucc]
          have h3 : (⟨(j : ℕ), by omega⟩ : Fin (n + 1)) =
              Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n) := Fin.ext rfl
          have h4 : (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) =
              Fin.succ (⟨(j : ℕ), hj⟩ : Fin n) := Fin.ext rfl
          rw [h3, h4]
          exact hchain _
        · have hjn : (j : ℕ) = n := by omega
          have h1 : (j.castSucc : Fin (n + 2)) =
              Fin.castSucc (Fin.last n) := Fin.ext hjn
          have h2 : (j.succ : Fin (n + 2)) = Fin.last (n + 1) :=
            Fin.ext (by simp [hjn, Fin.last])
          rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_last, hlast]
          exact hp
    · -- the target is the empty register: the trivial chain
      have hs : s = fun _ => False :=
        funext fun x => propext ⟨fun hx => hemp ⟨x, hx⟩, False.elim⟩
      exact ⟨0, fun _ => fun _ => False, rfl, hs.symm, fun j => j.elim0⟩

/-- **The chain is strictly increasing**: any two positions compare as
their register contents do, by induction on the distance. -/
theorem wmChain_lt (h : IsLinOrd (WMLe (A := A))) {n : ℕ}
    {mV : Fin (n + 1) → (A → Prop)}
    (hchain : ∀ k : Fin n, WMIncr WMLe (mV k.castSucc) (mV k.succ))
    {a a' : Fin (n + 1)} (hlt : a < a') :
    WMSetLt WMLe (mV a) (mV a') := by
  have hset := isLinOrd_wmSetLe h
  have hstep : ∀ (d : ℕ) (b b' : Fin (n + 1)), (b' : ℕ) = (b : ℕ) + d + 1 →
      WMSetLt WMLe (mV b) (mV b') := by
    intro d
    induction d with
    | zero =>
      intro b b' hb
      have hbn : (b : ℕ) < n := by have := b'.isLt; omega
      have e1 : mV b = mV (Fin.castSucc (⟨(b : ℕ), hbn⟩ : Fin n)) :=
        congrArg mV (Fin.ext rfl)
      have e2 : mV b' = mV (Fin.succ (⟨(b : ℕ), hbn⟩ : Fin n)) :=
        congrArg mV (Fin.ext hb)
      rw [e1, e2]
      have hi := hchain ⟨(b : ℕ), hbn⟩
      exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
    | succ d ihd =>
      intro b b' hb
      have hmn : (b : ℕ) + d + 1 < n + 1 := by have := b'.isLt; omega
      set m : Fin (n + 1) := ⟨(b : ℕ) + d + 1, hmn⟩ with hm
      have hmval : (m : ℕ) = (b : ℕ) + d + 1 := rfl
      have hbm := ihd b m rfl
      have hmb' : WMSetLt WMLe (mV m) (mV b') := by
        have hmn' : (m : ℕ) < n := by have := b'.isLt; omega
        have e1 : mV m = mV (Fin.castSucc (⟨(m : ℕ), hmn'⟩ : Fin n)) :=
          congrArg mV (Fin.ext rfl)
        have e2 : mV b' = mV (Fin.succ (⟨(m : ℕ), hmn'⟩ : Fin n)) :=
          congrArg mV (Fin.ext (show (b' : ℕ) = (m : ℕ) + 1 by omega))
        rw [e1, e2]
        have hi := hchain ⟨(m : ℕ), hmn'⟩
        exact (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
      rw [wmSetLt_iff] at hbm hmb' ⊢
      refine ⟨hset.2.1 _ _ _ hbm.1 hmb'.1, fun hc => ?_⟩
      exact hmb'.2 (hset.2.2.1 _ _ hmb'.1 (hc ▸ hbm.1))
  exact hstep ((a' : ℕ) - (a : ℕ) - 1) a a' (by omega)

end Chain

namespace Draw

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]

/-- **The Kin top**: the register content the exhaustion test accepts –
the set of the inner-block elements. -/
def kinTop : Univ A R P dt.KIx dt.dd → Prop :=
  fun u => ∃ j : Fin dt.ki, tagBlk u.1 = some (Sum.inr j)

variable {dt}

/-- **The VAL loop's enumeration exists**: an increment chain over
`Fin (n + 1)` from the empty register to the Kin top, in exactly the forms
`DescriptiveComplexity.Draw.Data.var_run` demands – the covers are
machine increments, the top passes the exhaustion test everywhere, every
earlier register fails it somewhere, and every register of the chain holds
inner cells alone, the Kin blocks being a final segment of the universe
(`DescriptiveComplexity.Draw.kinSeg`, `DescriptiveComplexity.subset_of_wmSetLe`).
That last fact is what the semantic layer reads a register through. -/
theorem exists_valEnum
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    ∃ (n : ℕ) (mV : Fin (n + 1) → (Univ A R P dt.KIx dt.dd → Prop)),
      mV 0 = (fun _ => False) ∧
      (∀ a a' : Fin (n + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
        WMIncr WMLe (mV a) (mV a')) ∧
      (∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV (Fin.last n)) u) ∧
      (∀ a, a < Fin.last n → ∃ u, ¬dt.InnerFull (fun u => tagBlk u.1) (mV a) u) ∧
      (∀ (a : Fin (n + 1)) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
        mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j) := by
  classical
  obtain ⟨n, mV, h0, hlast, hchain⟩ := exists_wmChain hlin (dt.kinTop
    (A := A) (R := R) (P := P))
  -- a Kin cell is an inner tag, and conversely
  have hcvt : ∀ t : Tag R P dt.KIx, (∃ j : Fin dt.ki, tagBlk t = some (Sum.inr j)) →
      ∃ j : Fin dt.ki, t = argIn dt.ko j := by
    rintro t ⟨j, hj⟩
    match t with
    | .arg i =>
      rcases h' : ofLex i with k | j'
      · exact absurd hj (by rw [tagBlk, h']; exact fun hc => nomatch hc)
      · exact ⟨j', congrArg Tag.arg (congrArg toLex h')⟩
  -- the Kin cells are a final segment of the universe, so a register at or
  -- below their address holds nothing else
  have hup : ∀ x y : Univ A R P dt.KIx dt.dd,
      dt.kinTop x → WMLt WMLe x y → dt.kinTop y := by
    rintro ⟨t, w⟩ ⟨t', w'⟩ hx hlt
    obtain ⟨j, rfl⟩ := hcvt t hx
    rcases (hord _ _).mp hlt.1 with htag | ⟨htag, -⟩
    · obtain ⟨j', rfl⟩ := kinSeg.final j t' (wmLt_le_iff.mpr htag)
      exact ⟨j', rfl⟩
    · exact ⟨j, by rw [← htag]; rfl⟩
  refine ⟨n, mV, h0, ?_, ?_, ?_, ?_⟩
  · -- adjacency in `Fin (n + 1)` is the chain's cover
    intro a a' hlt hnb
    have hava : (a : ℕ) < (a' : ℕ) := hlt
    have ha' := a'.isLt
    have hsucc : (a' : ℕ) = (a : ℕ) + 1 := by
      by_contra hc
      exact hnb ⟨(a : ℕ) + 1, by omega⟩
        ⟨show (a : ℕ) < (a : ℕ) + 1 by omega,
          show (a : ℕ) + 1 < (a' : ℕ) by omega⟩
    have han : (a : ℕ) < n := by omega
    have e1 : mV a = mV (Fin.castSucc (⟨(a : ℕ), han⟩ : Fin n)) :=
      congrArg mV (Fin.ext rfl)
    have e2 : mV a' = mV (Fin.succ (⟨(a : ℕ), han⟩ : Fin n)) :=
      congrArg mV (Fin.ext hsucc)
    rw [e1, e2]
    exact hchain _
  · -- the top passes the exhaustion test everywhere
    intro u
    change mV (Fin.last n) u ↔ _
    rw [hlast]
    exact Iff.rfl
  · -- every earlier register fails it somewhere
    intro a ha
    by_contra hc
    have hfull : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV a) u :=
      fun u => Classical.byContradiction fun hu => hc ⟨u, hu⟩
    have heq : mV a = dt.kinTop (A := A) (R := R) (P := P) :=
      funext fun u => propext (hfull u)
    have hne := (wmSetLt_iff _ _).mp (wmChain_lt hlin hchain ha)
    rw [heq, ← hlast] at hne
    exact hne.2 rfl
  · -- every register of the chain is at or below the Kin top, hence inside it
    intro a t w ha
    have hle : WMSetLe WMLe (mV a) (dt.kinTop (A := A) (R := R) (P := P)) := by
      rcases eq_or_lt_of_le (Fin.le_last a) with rfl | hlt
      · exact hlast ▸ Or.inl fun _ => Iff.rfl
      · exact hlast ▸ Or.inr (wmChain_lt hlin hchain hlt)
    exact hcvt t (subset_of_wmSetLe hlin hup hle ha)

end Data

end Draw

end DescriptiveComplexity
