/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawAdv
import DescriptiveComplexity.Problems.Wide.DrawTrip
import DescriptiveComplexity.Problems.Wide.IxAddr

/-!
# Random access: seeking the working cell to a target address

The R-atoms of the EXPSPACE program read the tape at a *computed* address:
the machine builds the address in its TARGET
register, resets the working-cell marker to the empty address, and advances it
– mirror in tow – until a file test says MIRROR = TARGET. This file is that
loop.

`DescriptiveComplexity.Draw.Prog.reaches_fileSeekTo` is one theorem: from the
checkpoint at the empty address, the machine reaches the verdict configuration
on the target's cell.

The loop is stated at an **arbitrary file**
(`DescriptiveComplexity.Draw.Prog.reachesIn_ixSeekTo`), because a clocked program
has no register per element: the walked track's mark is then the address's bits
at the registers (`DescriptiveComplexity.ixMark`) rather than the address
itself, and what makes it the same proof is that the correspondence carries the
order (`DescriptiveComplexity.Problems.Wide.IxAddr`) – so the file test's
verdict, the two marks agreeing at every register, is again the equality of the
two addresses, as long as both are addresses the file can hold. The elementwise
statement is that one at the diagonal. Each round is a **turnaround step** off the marker, a
`DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip` around the file test
(`DescriptiveComplexity.Draw.Prog.reaches_fileTestG` at *the walked mirror digit
agrees with the target digit*), and – the test having failed below the
target – an `DescriptiveComplexity.Draw.Prog.reaches_fileAdvance`; the loop is
`DescriptiveComplexity.reaches_of_wideRounds`, and the **mirror invariant** –
the mirror track *is* the marker's address – holds by construction, the two
being the same predicate.

The nine phases and their rule families are exactly the call sites of the
loop; their disjointness at the program level is by the guards (`wk` set vs
clear, `rl` set vs clear, register vs working area), as everywhere in the
layer.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}

/-! ### The seek at an arbitrary file -/

theorem reachesIn_ixSeekTo {I : Type} [Finite I] {ile : I → I → Prop}
    (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {elt : I → Univ A R P K dd} {Use : I → Prop}
    (hinj : Function.Injective elt)
    (hmono : ∀ u u', WMLt ile u u' ↔ WMLt WMLe (elt u) (elt u'))
    (hup : ∀ (u : I) (x : Univ A R P K dd), Use u → WMLt WMLe (elt u) x →
      ∃ u', Use u' ∧ elt u' = x)
    {t rg rl wk tg : W} (hnerg : t ≠ rg) (hnerl : rl ≠ t) (hnewk : wk ≠ t) (hnetg : tg ≠ t)
    {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)
    {T : Univ A R P K dd → Prop} (hTh : IxHolds elt Use T)
    (hT : WMSetLt WMLe T (F.cell gbot))
    {bg : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {bgN : (Univ A R P K dd → Prop) → W → A}
    (hbgwk : ∀ v r, bg v r wk = bitVal PR.zero PR.one (r = v))
    (hbgNwk : ∀ r, bgN r wk = PR.zero)
    (hbgNoth : ∀ v r s, s ≠ wk → bgN r s = bg v r s)
    (hbgrg : ∀ v r, bg v r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hbgrl : ∀ v r, bg v r rl = bitVal PR.zero PR.one (r = F.cell gtop))
    (hbgtg : ∀ v (u : I), bg v (F.cell u) tg = bitVal PR.zero PR.one (ixMark elt T u))
    {pChk pScan pT2b pTy pTn pA1 pA2 pA2b pA3 : P} {fc : Q → A}
    (hturn : ∀ g : W → A, g wk = PR.one → g rg ≠ PR.one →
      PR.HasRight pChk fc g pScan fc g)
    (hscanT : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight pScan fc g pScan fc g)
    (hbT₁ : ∀ g : W → A, g rl = PR.one → PR.HasLeft pScan fc g pT2b fc g)
    (hbT₂ : ∀ g : W → A, PR.HasRight pT2b fc g pTy fc g)
    (hpass : ∀ g : W → A, (g t = PR.one ↔ g tg = PR.one) → g rg = PR.one →
      PR.HasLeft pTy fc g pTy fc g)
    (hfail : ∀ g : W → A, ¬(g t = PR.one ↔ g tg = PR.one) → g rg = PR.one →
      PR.HasLeft pTy fc g pTn fc g)
    (hheldN : ∀ g : W → A, g rg = PR.one → PR.HasLeft pTn fc g pTn fc g)
    (hstayY : ∀ g : W → A, g rg ≠ PR.one → g wk ≠ PR.one →
      PR.HasLeft pTy fc g pTy fc g)
    (hbackN : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pTn fc g pTn fc g)
    (hA₀ : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      PR.HasRight pTn fc (PR.passTracksAt F.cell t (bg v) (ixMark elt v) v) pA1 fc
        (PR.passTracksAt F.cell t bgN (ixMark elt v) v))
    (hA₁ : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      PR.HasRight pA1 fc (PR.passTracksAt F.cell t bgN (ixMark elt v) v') pA2 fc
        (PR.passTracksAt F.cell t (bg v') (ixMark elt v) v'))
    (hscanA : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight pA2 fc g pA2 fc g)
    (hbA₁ : ∀ g : W → A, g rl = PR.one → PR.HasLeft pA2 fc g pA2b fc g)
    (hbA₂ : ∀ g : W → A, PR.HasRight pA2b fc g pA3 fc g)
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pA3 fc g pA3 fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft pA3 fc g pChk fc (Function.update g t PR.one))
    (hholdC : ∀ g : W → A, g rg = PR.one → PR.HasLeft pChk fc g pChk fc g)
    (hstayA : ∀ g : W → A, g rg ≠ PR.one → g wk ≠ PR.one →
      PR.HasLeft pA3 fc g pA3 fc g)
    (hbackC : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pChk fc g pChk fc g)
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w) :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
          wideRank (F.cell gbot)))
      ⟨Sum.inr (PR.stElt pChk fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell t (bg fun _ => False) fun _ => False) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pTy fc), Sum.inl T,
        wideTape (PR.trackTapeAt F.cell t (bg T) (ixMark elt T)) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- ≤-<-transitivity at addresses
  have hlelt : ∀ {a b c : Univ A R P K dd → Prop}, WMSetLe WMLe a b → WMSetLt WMLe b c →
      WMSetLt WMLe a c := by
    intro a b c hab hbc
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ hab ((wmSetLt_iff _ _).mp hbc).1, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hbc).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hbc).1 hab)
  -- an address at or below the target is not the last one
  have hnotfull : ∀ v : Univ A R P K dd → Prop, WMSetLe WMLe v T →
      ∃ x : Univ A R P K dd, ¬v x := by
    intro v hv
    by_contra hc
    push Not at hc
    exact ((wmSetLt_iff _ _).mp (hlelt hv hT)).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp (hlelt hv hT)).1
        (wmSetLe_of_full hlin hc (F.cell gbot)))
  -- the file's bottom register is at or below its top
  have hbotTop : WMSetLe WMLe (F.cell gbot) (F.cell gtop) := F.cell_le hix (hbot gtop)
  -- the mark of the file's top, read at the top's cell
  have hrlTop : ∀ (v : Univ A R P K dd → Prop) (k : I → Prop),
      PR.passTracksAt F.cell t (bg v) k (F.cell gtop) rl = PR.one := fun v k => by
    rw [passTracks_of_ne hnerl, hbgrl v]
    exact bitVal_pos rfl
  -- an address strictly below the bottom register is nobody's register
  have hnonregV : ∀ v : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      ∀ u : I, v ≠ F.cell u :=
    fun v hv u => F.ne_cell_of_lt_cell hix hbot hv u
  -- the register mark, read at unmarked cells
  have hrgOffB : ∀ (v r : Univ A R P K dd → Prop) (k : I → Prop),
      (∀ x : I, r ≠ F.cell x) →
      PR.passTracksAt F.cell t (bg v) k r rg ≠ PR.one := by
    intro v r k hno
    rw [passTracks_of_ne (Ne.symm hnerg), hbgrg v,
      bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
    exact PR.zero_ne_one
  -- the marker slot, read at or above the register file
  have hwkOffB : ∀ (v r : Univ A R P K dd → Prop) (k : I → Prop), WMSetLt WMLe v (F.cell gbot) →
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      PR.passTracksAt F.cell t (bg v) k r wk ≠ PR.one := by
    intro v r k hvlt hbnd
    obtain ⟨x, hx⟩ := hbnd
    have hne : r ≠ v := by
      rintro rfl
      have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
        rcases eq_or_ne gbot x with rfl | hnex
        · exact hlinSet.1 _
        · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
            ⟨hbot x, fun hc => hnex (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
      exact ((wmSetLt_iff _ _).mp hvlt).2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hvlt).1 (hlinSet.2.1 _ _ _ hgx hx))
    rw [passTracks_of_ne hnewk, hbgwk v, bitVal_neg hne]
    exact PR.zero_ne_one
  -- the turnaround step off the marker
  have hturnStep : ∀ v v₂ : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      WMIncr WMLe v v₂ →
      (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl v₂,
          wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
    intro v v₂ hvlt hi₂
    refine PR.step_move (t := t) (rest := bg v) (rest' := bg v) (m := ixMark elt v) hR hlin hi₂
      (fun _ _ => rfl) (hturn _ ?_ ?_)
    · rw [passTracks_of_ne hnewk, hbgwk v]
      exact bitVal_pos rfl
    · rw [passTracks_of_ne (Ne.symm hnerg), hbgrg v,
        bitVal_neg fun hc => hc.elim fun u hu => hnonregV v hvlt u hu]
      exact PR.zero_ne_one
  -- one round-trip test at the marker, verdict *no*: below the target
  have htripNe : ∀ v : Univ A R P K dd → Prop, WMSetLt WMLe v T →
      ∀ s : Univ A R P K dd → Prop, WMSetLe WMLe s (F.cell gtop) →
      (wideData (Univ A R P K dd)).ReachesIn
        (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
          wideRank (F.cell gbot))
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl s,
          wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pTn fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
    intro v hv s hsle
    have hvlt : WMSetLt WMLe v (F.cell gbot) :=
      hlelt ((wmSetLt_iff _ _).mp hv).1 hT
    obtain ⟨q, hq, htest⟩ := reachesIn_fileTestG F
      (Test := fun u : I => (ixMark elt v u ↔ ixMark elt T u))
      (TestG := fun g => (g t = PR.one ↔ g tg = PR.one)) hR hlin hix
      (m := ixMark elt v) (t := t) (rg := rg) hnerg (rest := bg v) (hbgrg v)
      (fun u => by
        rw [passTracks_cell_apply F hix, passTracks_of_ne hnetg, hbgtg v u]
        exact iff_congr (bitVal_iff PR.zero_ne_one) (bitVal_iff PR.zero_ne_one))
      (py := pTy) (pn := pTn) (f := fc)
      hpass hfail hheldN
      (fun r hbnd hno => hstayY _ (hrgOffB v r (ixMark elt v) hno)
        (hwkOffB v r (ixMark elt v) hvlt hbnd))
      (fun r hbnd _hno => hbackN _ (hwkOffB v r (ixMark elt v) hvlt hbnd))
      (w := w) hgap (top := gtop) (bot := gbot) htop hbot
    have hvh : IxHolds elt Use v :=
      ixHolds_of_wmSetLe hup hlin hTh ((wmSetLt_iff _ _).mp hv).1
    have hne : ∃ u : I, ¬(ixMark elt v u ↔ ixMark elt T u) := by
      by_contra hc
      push Not at hc
      refine ((wmSetLt_iff _ _).mp hv).2 ?_
      rw [← ixAddr_ixMark (Use := Use) hvh, ← ixAddr_ixMark (Use := Use) hTh,
        show ixMark elt v = ixMark elt T from funext fun u => propext (hc u)]
    rw [accStateAfter_bot_neg hbot hne.choose_spec] at htest
    refine (reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := bg v)
      (m := ixMark elt v) (m₂ := ixMark elt v)
      (wkAddr := v) (hbgrl v) (hbgwk v) (p₁ := pScan) (p₂b := pT2b) (pIn := pTy)
      (pOut := pTn) (fc := fc) hscanT (hbT₁ _ (hrlTop v (ixMark elt v))) hbT₂ hq htest
      (fun r _ hwk => hbackN _ hwk)
      (hlelt ((wmSetLt_iff _ _).mp hv).1 hT) hsle).mono (by
      have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
      have h₂ : wideRank q - wideRank v ≤ wideRank (F.cell gbot) :=
        le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
      omega)
  -- one round-trip test at the marker, verdict *yes*: at the target
  have htripEq : ∀ s : Univ A R P K dd → Prop, WMSetLe WMLe s (F.cell gtop) →
      (wideData (Univ A R P K dd)).ReachesIn
        (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
          wideRank (F.cell gbot))
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl s,
          wideTape (PR.trackTapeAt F.cell t (bg T) (ixMark elt T)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pTy fc), Sum.inl T,
          wideTape (PR.trackTapeAt F.cell t (bg T) (ixMark elt T)) (PR.syElt PR.blank)⟩ := by
    intro s hsle
    obtain ⟨q, hq, htest⟩ := reachesIn_fileTestG F
      (Test := fun u : I => (ixMark elt T u ↔ ixMark elt T u))
      (TestG := fun g => (g t = PR.one ↔ g tg = PR.one)) hR hlin hix
      (m := ixMark elt T) (t := t) (rg := rg) hnerg (rest := bg T) (hbgrg T)
      (fun u => by
        rw [passTracks_cell_apply F hix, passTracks_of_ne hnetg, hbgtg T u]
        exact iff_congr (bitVal_iff PR.zero_ne_one) (bitVal_iff PR.zero_ne_one))
      (py := pTy) (pn := pTn) (f := fc)
      hpass hfail hheldN
      (fun r hbnd hno => hstayY _ (hrgOffB T r (ixMark elt T) hno)
        (hwkOffB T r (ixMark elt T) hT hbnd))
      (fun r hbnd _hno => hbackN _ (hwkOffB T r (ixMark elt T) hT hbnd))
      (w := w) hgap (top := gtop) (bot := gbot) htop hbot
    rw [accStateAfter_bot_pos (fun _ => Iff.rfl)] at htest
    refine (reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := bg T)
      (m := ixMark elt T) (m₂ := ixMark elt T)
      (wkAddr := T) (hbgrl T) (hbgwk T) (p₁ := pScan) (p₂b := pT2b) (pIn := pTy)
      (pOut := pTy) (fc := fc) hscanT (hbT₁ _ (hrlTop T (ixMark elt T))) hbT₂ hq htest
      (fun r hnr hwk => hstayY _ (hrgOffB T r (ixMark elt T) hnr) hwk) hT hsle).mono (by
      have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
      have h₂ : wideRank q - wideRank T ≤ wideRank (F.cell gbot) :=
        le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
      omega)
  -- <-≤-transitivity at addresses
  have hltle : ∀ {a b c : Univ A R P K dd → Prop}, WMSetLt WMLe a b → WMSetLe WMLe b c →
      WMSetLt WMLe a c := by
    intro a b c hab hbc
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ ((wmSetLt_iff _ _).mp hab).1 hbc, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hab).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hab).1 hbc)
  -- one round below the target: turnaround, failed test, ADVANCE
  have hround : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' →
      WMSetLe WMLe (fun _ => False) v → WMSetLe WMLe v' T →
      (wideData (Univ A R P K dd)).ReachesIn
        (1 + (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
            wideRank (F.cell gbot)) +
          (wideRank (F.cell gtop) + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
            wideRank (F.cell gbot) + 4))
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell t (bg v') (ixMark elt v')) (PR.syElt PR.blank)⟩ := by
    intro v v' hi _ hub
    have hvltT : WMSetLt WMLe v T :=
      hltle ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩) hub
    have hAN : ∀ r, r ≠ v → bgN r = bg v r := by
      intro r hr
      funext sl
      by_cases hs : sl = wk
      · subst hs
        rw [hbgNwk, hbgwk v, bitVal_neg hr]
      · exact hbgNoth v r sl hs
    have hNB : ∀ r, r ≠ v' → bg v' r = bgN r := by
      intro r hr
      funext sl
      by_cases hs : sl = wk
      · subst hs
        rw [hbgNwk, hbgwk v', bitVal_neg hr]
      · exact (hbgNoth v' r sl hs).symm
    have hv'lt : WMSetLt WMLe v' (F.cell gbot) := hlelt hub hT
    have hadv := reachesIn_fileAdvance F hR hlin hix hnerg hnerl hnewk htop hbot hi
      hv'lt (wmIncr_ixMark (Use := Use) hinj hmono
        (ixHolds_of_wmSetLe hup hlin hTh hub) hi) hAN hNB (hbgwk v') (hbgrg v') (hbgrl v')
      (p₀ := pTn) (p₁ := pA1) (p₂ := pA2) (p₂b := pA2b) (p₃ := pA3) (p₄ := pChk)
      (fc := fc)
      (hA₀ v v' hi hub) (hA₁ v v' hi hub)
      hscanA (hbA₁ _ (hrlTop v' (ixMark elt v))) hbA₂
      hclear hset hholdC
      (fun k r hbnd hno => hstayA _ (hrgOffB v' r k hno) (hwkOffB v' r k hv'lt hbnd))
      (fun k r hbnd _hno => hbackC _ (hwkOffB v' r k hv'lt hbnd))
      hbackC (w := w) hgap
    exact ((TMData.ReachesIn.head
      (hturnStep v v' (hltle hvltT ((wmSetLt_iff _ _).mp hT).1) hi)
      (htripNe v hvltT v'
        (hlinSet.2.1 _ _ _ (hlinSet.2.1 _ _ _ hub ((wmSetLt_iff _ _).mp hT).1)
          hbotTop))).trans hadv).mono (by omega)
  -- the loop, then the final passing round at the target
  have hloop := reachesIn_of_wideRounds hlin
    (conf := fun v => ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
      wideTape (PR.trackTapeAt F.cell t (bg v) (ixMark elt v)) (PR.syElt PR.blank)⟩)
    (s₀ := fun _ => False) (s₁ := T) hround T
    (wmSetLe_of_empty hlin (fun _ hc => hc) T) (hlinSet.1 T)
  obtain ⟨T₂, hiT⟩ := exists_wmIncr hlin (hnotfull T (hlinSet.1 T))
  refine (hloop.trans (TMData.ReachesIn.head (hturnStep T T₂ hT hiT)
    (htripEq T₂ (hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr_of_lt hlin hiT hT) hbotTop)))).mono ?_
  rw [wideRank_bot hlin, Nat.sub_zero]
  omega

/-- **The seek loop**, the budget forgotten. -/
theorem reaches_fileSeekTo (F : RegFile (Univ A R P K dd)) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t rg rl wk tg : W} (hnerg : t ≠ rg) (hnerl : rl ≠ t) (hnewk : wk ≠ t) (hnetg : tg ≠ t)
    {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {T : Univ A R P K dd → Prop} (hT : WMSetLt WMLe T (F.cell gbot))
    {bg : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {bgN : (Univ A R P K dd → Prop) → W → A}
    (hbgwk : ∀ v r, bg v r wk = bitVal PR.zero PR.one (r = v))
    (hbgNwk : ∀ r, bgN r wk = PR.zero)
    (hbgNoth : ∀ v r s, s ≠ wk → bgN r s = bg v r s)
    (hbgrg : ∀ v r, bg v r rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = F.cell u))
    (hbgrl : ∀ v r, bg v r rl = bitVal PR.zero PR.one (r = F.cell gtop))
    (hbgtg : ∀ v u, bg v (F.cell u) tg = bitVal PR.zero PR.one (T u))
    {pChk pScan pT2b pTy pTn pA1 pA2 pA2b pA3 : P} {fc : Q → A}
    (hturn : ∀ g : W → A, g wk = PR.one → g rg ≠ PR.one →
      PR.HasRight pChk fc g pScan fc g)
    (hscanT : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight pScan fc g pScan fc g)
    (hbT₁ : ∀ g : W → A, g rl = PR.one → PR.HasLeft pScan fc g pT2b fc g)
    (hbT₂ : ∀ g : W → A, PR.HasRight pT2b fc g pTy fc g)
    (hpass : ∀ g : W → A, (g t = PR.one ↔ g tg = PR.one) → g rg = PR.one →
      PR.HasLeft pTy fc g pTy fc g)
    (hfail : ∀ g : W → A, ¬(g t = PR.one ↔ g tg = PR.one) → g rg = PR.one →
      PR.HasLeft pTy fc g pTn fc g)
    (hheldN : ∀ g : W → A, g rg = PR.one → PR.HasLeft pTn fc g pTn fc g)
    (hstayY : ∀ g : W → A, g rg ≠ PR.one → g wk ≠ PR.one →
      PR.HasLeft pTy fc g pTy fc g)
    (hbackN : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pTn fc g pTn fc g)
    (hA₀ : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      PR.HasRight pTn fc (PR.passTracksAt F.cell t (bg v) v v) pA1 fc
        (PR.passTracksAt F.cell t bgN v v))
    (hA₁ : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      PR.HasRight pA1 fc (PR.passTracksAt F.cell t bgN v v') pA2 fc
        (PR.passTracksAt F.cell t (bg v') v v'))
    (hscanA : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight pA2 fc g pA2 fc g)
    (hbA₁ : ∀ g : W → A, g rl = PR.one → PR.HasLeft pA2 fc g pA2b fc g)
    (hbA₂ : ∀ g : W → A, PR.HasRight pA2b fc g pA3 fc g)
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pA3 fc g pA3 fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft pA3 fc g pChk fc (Function.update g t PR.one))
    (hholdC : ∀ g : W → A, g rg = PR.one → PR.HasLeft pChk fc g pChk fc g)
    (hstayA : ∀ g : W → A, g rg ≠ PR.one → g wk ≠ PR.one →
      PR.HasLeft pA3 fc g pA3 fc g)
    (hbackC : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pChk fc g pChk fc g) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pChk fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell t (bg fun _ => False) fun _ => False) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pTy fc), Sum.inl T,
        wideTape (PR.trackTapeAt F.cell t (bg T) T) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- ≤-<-transitivity at addresses
  have hlelt : ∀ {a b c : Univ A R P K dd → Prop}, WMSetLe WMLe a b → WMSetLt WMLe b c →
      WMSetLt WMLe a c := by
    intro a b c hab hbc
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ hab ((wmSetLt_iff _ _).mp hbc).1, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hbc).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hbc).1 hab)
  -- an address at or below the target is not the last one
  have hnotfull : ∀ v : Univ A R P K dd → Prop, WMSetLe WMLe v T →
      ∃ x : Univ A R P K dd, ¬v x := by
    intro v hv
    by_contra hc
    push Not at hc
    exact ((wmSetLt_iff _ _).mp (hlelt hv hT)).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp (hlelt hv hT)).1
        (wmSetLe_of_full hlin hc (F.cell gbot)))
  -- the file's bottom register is at or below its top
  have hbotTop : WMSetLe WMLe (F.cell gbot) (F.cell gtop) := F.cell_le hlin (hbot gtop)
  -- the mark of the file's top, read at the top's cell
  have hrlTop : ∀ v k : Univ A R P K dd → Prop,
      PR.passTracksAt F.cell t (bg v) k (F.cell gtop) rl = PR.one := fun v k => by
    rw [passTracks_of_ne hnerl, hbgrl v]
    exact bitVal_pos rfl
  -- an address strictly below the bottom register is nobody's register
  have hnonregV : ∀ v : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      ∀ u : Univ A R P K dd, v ≠ F.cell u :=
    fun v hv u => F.ne_cell_of_lt_cell hlin hbot hv u
  -- the register mark, read at unmarked cells
  have hrgOffB : ∀ v k r : Univ A R P K dd → Prop,
      (∀ x : Univ A R P K dd, r ≠ F.cell x) →
      PR.passTracksAt F.cell t (bg v) k r rg ≠ PR.one := by
    intro v k r hno
    rw [passTracks_of_ne (Ne.symm hnerg), hbgrg v,
      bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
    exact PR.zero_ne_one
  -- the marker slot, read at or above the register file
  have hwkOffB : ∀ v k r : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      (∃ x : Univ A R P K dd, WMSetLe WMLe (F.cell x) r) →
      PR.passTracksAt F.cell t (bg v) k r wk ≠ PR.one := by
    intro v k r hvlt hbnd
    obtain ⟨x, hx⟩ := hbnd
    have hne : r ≠ v := by
      rintro rfl
      have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
        rcases eq_or_ne gbot x with rfl | hnex
        · exact hlinSet.1 _
        · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hlin gbot x).mpr
            ⟨hbot x, fun hc => hnex (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
      exact ((wmSetLt_iff _ _).mp hvlt).2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hvlt).1 (hlinSet.2.1 _ _ _ hgx hx))
    rw [passTracks_of_ne hnewk, hbgwk v, bitVal_neg hne]
    exact PR.zero_ne_one
  -- the turnaround step off the marker
  have hturnStep : ∀ v v₂ : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      WMIncr WMLe v v₂ →
      (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl v₂,
          wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩ := by
    intro v v₂ hvlt hi₂
    refine PR.step_move (t := t) (rest := bg v) (rest' := bg v) (m := v) hR hlin hi₂
      (fun _ _ => rfl) (hturn _ ?_ ?_)
    · rw [passTracks_of_ne hnewk, hbgwk v]
      exact bitVal_pos rfl
    · rw [passTracks_of_ne (Ne.symm hnerg), hbgrg v,
        bitVal_neg fun hc => hc.elim fun u hu => hnonregV v hvlt u hu]
      exact PR.zero_ne_one
  -- one round-trip test at the marker, verdict *no*: below the target
  have htripNe : ∀ v : Univ A R P K dd → Prop, WMSetLt WMLe v T →
      ∀ s : Univ A R P K dd → Prop, WMSetLe WMLe s (F.cell gtop) →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl s,
          wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pTn fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩ := by
    intro v hv s hsle
    have hvlt : WMSetLt WMLe v (F.cell gbot) :=
      hlelt ((wmSetLt_iff _ _).mp hv).1 hT
    obtain ⟨q, hq, htest⟩ := reaches_fileTestG F.toIx (Test := fun u => (v u ↔ T u))
      (TestG := fun g => (g t = PR.one ↔ g tg = PR.one)) hR hlin hlin
      (m := v) (t := t) (rg := rg) hnerg (rest := bg v) (hbgrg v)
      (fun u => by
        rw [passTracks_cell_apply F.toIx hlin, passTracks_of_ne hnetg, hbgtg v u]
        exact iff_congr (bitVal_iff PR.zero_ne_one) (bitVal_iff PR.zero_ne_one))
      (py := pTy) (pn := pTn) (f := fc)
      hpass hfail hheldN
      (fun r hbnd hno => hstayY _ (hrgOffB v v r hno) (hwkOffB v v r hvlt hbnd))
      (fun r hbnd _hno => hbackN _ (hwkOffB v v r hvlt hbnd))
      (top := gtop) (bot := gbot) htop hbot
    have hne : ∃ u : Univ A R P K dd, ¬(v u ↔ T u) := by
      by_contra hc
      push Not at hc
      exact ((wmSetLt_iff _ _).mp hv).2 (funext fun u => propext (hc u))
    rw [accStateAfter_bot_neg hbot hne.choose_spec] at htest
    exact reaches_fileRoundTrip F.toIx hR hlin hlin hnerl hnewk hbot (rest := bg v)
      (m := v) (m₂ := v)
      (wkAddr := v) (hbgrl v) (hbgwk v) (p₁ := pScan) (p₂b := pT2b) (pIn := pTy)
      (pOut := pTn) (fc := fc) hscanT (hbT₁ _ (hrlTop v v)) hbT₂ hq htest
      (fun r _ hwk => hbackN _ hwk)
      (hlelt ((wmSetLt_iff _ _).mp hv).1 hT) hsle
  -- one round-trip test at the marker, verdict *yes*: at the target
  have htripEq : ∀ s : Univ A R P K dd → Prop, WMSetLe WMLe s (F.cell gtop) →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pScan fc), Sum.inl s,
          wideTape (PR.trackTapeAt F.cell t (bg T) T) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pTy fc), Sum.inl T,
          wideTape (PR.trackTapeAt F.cell t (bg T) T) (PR.syElt PR.blank)⟩ := by
    intro s hsle
    obtain ⟨q, hq, htest⟩ := reaches_fileTestG F.toIx (Test := fun u => (T u ↔ T u))
      (TestG := fun g => (g t = PR.one ↔ g tg = PR.one)) hR hlin hlin
      (m := T) (t := t) (rg := rg) hnerg (rest := bg T) (hbgrg T)
      (fun u => by
        rw [passTracks_cell_apply F.toIx hlin, passTracks_of_ne hnetg, hbgtg T u]
        exact iff_congr (bitVal_iff PR.zero_ne_one) (bitVal_iff PR.zero_ne_one))
      (py := pTy) (pn := pTn) (f := fc)
      hpass hfail hheldN
      (fun r hbnd hno => hstayY _ (hrgOffB T T r hno) (hwkOffB T T r hT hbnd))
      (fun r hbnd _hno => hbackN _ (hwkOffB T T r hT hbnd))
      (top := gtop) (bot := gbot) htop hbot
    rw [accStateAfter_bot_pos (fun _ => Iff.rfl)] at htest
    exact reaches_fileRoundTrip F.toIx hR hlin hlin hnerl hnewk hbot (rest := bg T)
      (m := T) (m₂ := T)
      (wkAddr := T) (hbgrl T) (hbgwk T) (p₁ := pScan) (p₂b := pT2b) (pIn := pTy)
      (pOut := pTy) (fc := fc) hscanT (hbT₁ _ (hrlTop T T)) hbT₂ hq htest
      (fun r hnr hwk => hstayY _ (hrgOffB T T r hnr) hwk) hT hsle
  -- <-≤-transitivity at addresses
  have hltle : ∀ {a b c : Univ A R P K dd → Prop}, WMSetLt WMLe a b → WMSetLe WMLe b c →
      WMSetLt WMLe a c := by
    intro a b c hab hbc
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ ((wmSetLt_iff _ _).mp hab).1 hbc, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hab).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hab).1 hbc)
  -- one round below the target: turnaround, failed test, ADVANCE
  have hround : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' →
      WMSetLe WMLe (fun _ => False) v → WMSetLe WMLe v' T →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell t (bg v') v') (PR.syElt PR.blank)⟩ := by
    intro v v' hi _ hub
    have hvltT : WMSetLt WMLe v T :=
      hltle ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩) hub
    have hAN : ∀ r, r ≠ v → bgN r = bg v r := by
      intro r hr
      funext sl
      by_cases hs : sl = wk
      · subst hs
        rw [hbgNwk, hbgwk v, bitVal_neg hr]
      · exact hbgNoth v r sl hs
    have hNB : ∀ r, r ≠ v' → bg v' r = bgN r := by
      intro r hr
      funext sl
      by_cases hs : sl = wk
      · subst hs
        rw [hbgNwk, hbgwk v', bitVal_neg hr]
      · exact (hbgNoth v' r sl hs).symm
    have hv'lt : WMSetLt WMLe v' (F.cell gbot) := hlelt hub hT
    have hadv := reaches_fileAdvance F.toIx hR hlin hlin hnerg hnerl hnewk htop hbot hi
      hv'lt hi hAN hNB (hbgwk v') (hbgrg v') (hbgrl v')
      (p₀ := pTn) (p₁ := pA1) (p₂ := pA2) (p₂b := pA2b) (p₃ := pA3) (p₄ := pChk)
      (fc := fc)
      (hA₀ v v' hi hub) (hA₁ v v' hi hub)
      hscanA (hbA₁ _ (hrlTop v' v)) hbA₂
      hclear hset hholdC
      (fun k r hbnd hno => hstayA _ (hrgOffB v' k r hno) (hwkOffB v' k r hv'lt hbnd))
      (fun k r hbnd _hno => hbackC _ (hwkOffB v' k r hv'lt hbnd))
      hbackC
    exact (Relation.ReflTransGen.head
      (hturnStep v v' (hltle hvltT ((wmSetLt_iff _ _).mp hT).1) hi)
      (htripNe v hvltT v'
        (hlinSet.2.1 _ _ _ (hlinSet.2.1 _ _ _ hub ((wmSetLt_iff _ _).mp hT).1)
          hbotTop))).trans hadv
  -- the loop, then the final passing round at the target
  have hloop := reaches_of_wideRounds hlin
    (conf := fun v => ⟨Sum.inr (PR.stElt pChk fc), Sum.inl v,
      wideTape (PR.trackTapeAt F.cell t (bg v) v) (PR.syElt PR.blank)⟩)
    (s₀ := fun _ => False) (s₁ := T) hround T
    (wmSetLe_of_empty hlin (fun _ hc => hc) T) (hlinSet.1 T)
  obtain ⟨T₂, hiT⟩ := exists_wmIncr hlin (hnotfull T (hlinSet.1 T))
  exact hloop.trans (Relation.ReflTransGen.head (hturnStep T T₂ hT hiT)
    (htripEq T₂ (hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr_of_lt hlin hiT hT) hbotTop)))

end Prog

end Draw

end DescriptiveComplexity
