/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpScan
import DescriptiveComplexity.Problems.Wide.PfpSub

/-!
# Reading one named register bit

The leaves of the element loops read single bits of the machine's registers at
*computed* cells: a `ρ`-atom of an expansion sentence
is one bit of VAL or MIRROR at the cell whose name marks match a tuple held in
the control, a tag read is the same at a canonical cell. The trip is always
the same: turn off the working-cell marker, scan up to the first cell whose
tracks satisfy the **name guard** – unique by
`DescriptiveComplexity.Pfp.eq_of_slotMark_name`-style facts – take one step
left reading the walked digit into the phase, and scan back down to the
marker.

`DescriptiveComplexity.Pfp.Prog.reaches_readBit_pos` and `_neg` are the two
outcomes. The read changes nothing on the tape, so the two theorems mention
one tape; the caller cases on the bit.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}

section Read

variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {t wk : W} (hnewk : wk ≠ t)
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
variable {v : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hwkS : ∀ r : Univ A R P K dd → Prop, rest r wk = bitVal PR.zero PR.one (r = v))
variable {NameG : (W → A) → Prop} {x₀ : Univ A R P K dd}
variable (hname : NameG (PR.passTracks t rest m (wmSeg x₀)))
variable (huniq : ∀ r : Univ A R P K dd → Prop,
  NameG (PR.passTracks t rest m r) → r = wmSeg x₀)
variable {pStart pUp pRy pRn : P} {fc : Q → A}
variable (hturn : ∀ g : W → A, g wk = PR.one → PR.HasRight pStart fc g pUp fc g)
variable (hup : ∀ g : W → A, ¬NameG g → PR.HasRight pUp fc g pUp fc g)

include hR hlin hnewk hbot hv hwkS hname huniq hturn hup in
/-- The common part of the two reads: turn, scan up to the named cell, one
branching step left, scan back down to the marker, in the branch phase. -/
private theorem reaches_readBit_aux {pB : P}
    (hbranch : PR.HasLeft pUp fc (PR.passTracks t rest m (wmSeg x₀)) pB fc
      (PR.passTracks t rest m (wmSeg x₀)))
    (hbackB : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pB fc g pB fc g) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pB fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- the marker's cell is strictly below the named register cell
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x₀) := by
    rcases eq_or_ne gbot x₀ with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x₀).mpr
        ⟨hbot x₀, fun hc => hne (hlin.2.2.1 gbot x₀ (hbot x₀) hc)⟩)).1
  have hvx : WMSetLt WMLe v (wmSeg x₀) := by
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ ((wmSetLt_iff _ _).mp hv).1 hgx, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hv).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv).1
      (hlinSet.2.1 _ _ _ hgx (hlinSet.1 _)))
  -- the marker's next cell exists and is at or below the named cell
  have hvne : ∃ x : Univ A R P K dd, ¬v x := by
    by_contra hc
    push Not at hc
    exact ((wmSetLt_iff _ _).mp hv).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv).1
      (wmSetLe_of_full hlin hc (wmSeg gbot)))
  obtain ⟨v₂, hi₂⟩ := exists_wmIncr hlin hvne
  have hv₂x : WMSetLe WMLe v₂ (wmSeg x₀) := by
    rcases hlinSet.2.2.2 v₂ (wmSeg x₀) with hc | hc
    · exact hc
    · rcases eq_or_ne (wmSeg x₀) v₂ with he | hne
      · exact he ▸ hlinSet.1 _
      · exact absurd ((wmSetLt_iff_of_wmIncr hlin hi₂ _).mp
          ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩)) fun hle =>
            ((wmSetLt_iff _ _).mp hvx).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hvx).1 hle)
  -- the turnaround step off the marker
  have hstep₁ : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pUp fc), Sum.inl v₂,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
    refine PR.step_move (t := t) (rest := rest) (rest' := rest) (m := m) hR hlin hi₂
      (fun _ _ => rfl) (hturn _ ?_)
    rw [passTracks_of_ne hnewk, hwkS]
    exact bitVal_pos rfl
  -- the scan up to the named cell
  have hscan := reaches_toCell (StopG := NameG) hR hlin (t := t) (rest := rest) (m := m)
    (p := pUp) (f := fc) (fun g hg => hup g hg) (u := wmSeg x₀) (s := v₂)
    hname hv₂x (fun r _ hr => huniq r hr)
  -- the branching read step, off the named cell to its predecessor
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin (s := wmSeg x₀) ⟨x₀, hlin.1 x₀⟩
  have hstep₂ : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pUp fc), Sum.inl (wmSeg x₀),
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pB fc), Sum.inl pt,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ :=
    PR.step_moveBack (t := t) (rest := rest) (rest' := rest) (m := m) hR hlin hpt
      (fun _ _ => rfl) hbranch
  -- the scan back down to the marker
  have hret := reaches_toCellBack (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := rest) (m := m) (p := pB) (f := fc)
    (fun g hg => hbackB g hg) (u := v) (s := pt)
    (by rw [passTracks_of_ne hnewk, hwkS]; exact bitVal_pos rfl)
    ((wmSetLt_iff_of_wmIncr hlin hpt v).mp hvx)
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkS] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  exact Relation.ReflTransGen.head hstep₁
    (hscan.trans (Relation.ReflTransGen.head hstep₂ hret))

include hR hlin hnewk hbot hv hwkS hname huniq hturn hup in
/-- **Writing one named register bit**: the same trip, with the walked track
updated at the named cell on the way back down. -/
theorem reaches_writeBit {b : Prop} {pW : P}
    (hwr : PR.HasLeft pUp fc (PR.passTracks t rest m (wmSeg x₀)) pW fc
      (Function.update (PR.passTracks t rest m (wmSeg x₀)) t (bitVal PR.zero PR.one b)))
    (hbackW : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pW fc g pW fc g) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pW fc), Sum.inl v,
        wideTape (PR.trackTape t rest fun y => (y = x₀ ∧ b) ∨ (y ≠ x₀ ∧ m y))
          (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x₀) := by
    rcases eq_or_ne gbot x₀ with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x₀).mpr
        ⟨hbot x₀, fun hc => hne (hlin.2.2.1 gbot x₀ (hbot x₀) hc)⟩)).1
  have hvx : WMSetLt WMLe v (wmSeg x₀) := by
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ ((wmSetLt_iff _ _).mp hv).1 hgx, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hv).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv).1
      (hlinSet.2.1 _ _ _ hgx (hlinSet.1 _)))
  have hvne : ∃ x : Univ A R P K dd, ¬v x := by
    by_contra hc
    push Not at hc
    exact ((wmSetLt_iff _ _).mp hv).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv).1
      (wmSetLe_of_full hlin hc (wmSeg gbot)))
  obtain ⟨v₂, hi₂⟩ := exists_wmIncr hlin hvne
  have hv₂x : WMSetLe WMLe v₂ (wmSeg x₀) := by
    rcases hlinSet.2.2.2 v₂ (wmSeg x₀) with hc | hc
    · exact hc
    · rcases eq_or_ne (wmSeg x₀) v₂ with he | hne
      · exact he ▸ hlinSet.1 _
      · exact absurd ((wmSetLt_iff_of_wmIncr hlin hi₂ _).mp
          ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩)) fun hle =>
            ((wmSetLt_iff _ _).mp hvx).2 (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hvx).1 hle)
  have hstep₁ : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pUp fc), Sum.inl v₂,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
    refine PR.step_move (t := t) (rest := rest) (rest' := rest) (m := m) hR hlin hi₂
      (fun _ _ => rfl) (hturn _ ?_)
    rw [passTracks_of_ne hnewk, hwkS]
    exact bitVal_pos rfl
  have hscan := reaches_toCell (StopG := NameG) hR hlin (t := t) (rest := rest) (m := m)
    (p := pUp) (f := fc) (fun g hg => hup g hg) (u := wmSeg x₀) (s := v₂)
    hname hv₂x (fun r _ hr => huniq r hr)
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin (s := wmSeg x₀) ⟨x₀, hlin.1 x₀⟩
  have hstep₂ := PR.step_writeReg (t := t) (rest := rest) (m := m) (b := b) hR hlin hpt
    (p := pUp) (p' := pW) (f := fc) (f' := fc) hwr
  have hret := reaches_toCellBack (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := rest) (m := fun y => (y = x₀ ∧ b) ∨ (y ≠ x₀ ∧ m y)) (p := pW)
    (f := fc) (fun g hg => hbackW g hg) (u := v) (s := pt)
    (by rw [passTracks_of_ne hnewk, hwkS]; exact bitVal_pos rfl)
    ((wmSetLt_iff_of_wmIncr hlin hpt v).mp hvx)
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkS] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  exact Relation.ReflTransGen.head hstep₁
    (hscan.trans (Relation.ReflTransGen.head hstep₂ hret))

variable (hrd1 : ∀ g : W → A, NameG g → g t = PR.one → PR.HasLeft pUp fc g pRy fc g)
variable (hrd0 : ∀ g : W → A, NameG g → g t ≠ PR.one → PR.HasLeft pUp fc g pRn fc g)
variable (hbackY : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pRy fc g pRy fc g)
variable (hbackN : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft pRn fc g pRn fc g)

include hR hlin hnewk hbot hv hwkS hname huniq hturn hup hrd1 hbackY in
/-- **Reading a set bit**: the trip ends at the marker in the positive
phase. -/
theorem reaches_readBit_pos (hm : m x₀) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pRy fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ :=
  reaches_readBit_aux hR hlin hnewk hbot hv hwkS hname huniq hturn hup
    (hrd1 _ hname (by rw [passTracks_wmSeg_apply hlin]; exact bitVal_pos hm)) hbackY

include hR hlin hnewk hbot hv hwkS hname huniq hturn hup hrd0 hbackN in
/-- **Reading a clear bit**: the trip ends at the marker in the negative
phase. -/
theorem reaches_readBit_neg (hm : ¬m x₀) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pStart fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pRn fc), Sum.inl v,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ :=
  reaches_readBit_aux hR hlin hnewk hbot hv hwkS hname huniq hturn hup
    (hrd0 _ hname (by
      rw [passTracks_wmSeg_apply hlin, bitVal_neg hm]
      exact PR.zero_ne_one)) hbackN

end Read

end Prog

end Pfp

end DescriptiveComplexity
