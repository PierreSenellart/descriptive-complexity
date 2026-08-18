/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSub

/-!
# ADVANCE: moving the working cell one address, mirror in tow

The round every sweep of the EXPSPACE program repeats: erase the working-cell
marker and step right; write it
at the next address and step on; scan up to the top of the register file;
**bounce** – the scan cannot overshoot the maximal cell, so entering the
downward pass costs two steps, left to the top's predecessor and back right,
changing phase; run the mirror increment down the file
(`DescriptiveComplexity.Pfp.Prog.reaches_fileIncr`); scan back down to the marker.

`DescriptiveComplexity.Pfp.Prog.reaches_fileAdvance` is the whole round, and the
first *composite* of the layer: two `Prog.step_move`s, a
`Prog.reaches_toCell`, two bounce steps, a pass and a
`Prog.reaches_toCellBack`, chained by `Relation.ReflTransGen`. Its hypotheses
are the six rule families of the phases it visits plus the background's slot
equations, and nothing else – which is the evidence the pass layer's
interfaces (the element-valued background, the cell-coupled walking rules, the
stop-ahead bounds) are the right ones: every one of them is consumed here.

The working cell and its successor lie strictly below the register file, so
the cell-coupled walking hypotheses – whose cells are all at or above a
register – never meet the marker, and one rule family per walking phase
serves both the pass's descent and the return scan.
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
variable {I : Type} [Finite I] {ile : I → I → Prop}
variable {PR : Prog A R P Q W K dd}

/-- **One round of a sweep**: the working-cell marker moves from `v` to its
increment `v'`, the mirror track from `m` to its increment `m'`, and the head
comes back to the marker. See the module docstring for the itinerary; the
hypotheses are the rule families of the six phases visited and the slot
equations of the three backgrounds (marker at `v`, marker nowhere, marker at
`v'`). -/
theorem reachesIn_fileAdvance (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    -- the slots: walked mirror track, register mark, file-top mark, cell marker
    {t rg rl wk : W} (hnerg : t ≠ rg) (hnerl : rl ≠ t) (hnewk : wk ≠ t)
    -- the two extremal elements
    {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)
    -- the marker's addresses, strictly below the register file
    {v v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v v')
    (hv' : WMSetLt WMLe v' (F.cell gbot))
    -- the mirror's contents
    {m m' : I → Prop} (him : WMIncr ile m m')
    -- the three backgrounds and their slot equations
    {restA restN restB : (Univ A R P K dd → Prop) → W → A}
    (hAN : ∀ r, r ≠ v → restN r = restA r)
    (hNB : ∀ r, r ≠ v' → restB r = restN r)
    (hwkB : ∀ r, restB r wk = bitVal PR.zero PR.one (r = v'))
    (hrgB : ∀ r, restB r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hrlB : ∀ r, restB r rl = bitVal PR.zero PR.one (r = F.cell gtop))
    -- the phases and the fixed pointer
    {p₀ p₁ p₂ p₂b p₃ p₄ : P} {fc : Q → A}
    -- the two marker steps
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt F.cell t restA m v) p₁ fc
      (PR.passTracksAt F.cell t restN m v))
    (h₁ : PR.HasRight p₁ fc (PR.passTracksAt F.cell t restN m v') p₂ fc
      (PR.passTracksAt F.cell t restB m v'))
    -- the scan up to the file top
    (hscanUp : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight p₂ fc g p₂ fc g)
    -- the bounce
    (hb₁ : PR.HasLeft p₂ fc (PR.passTracksAt F.cell t restB m (F.cell gtop)) p₂b fc
      (PR.passTracksAt F.cell t restB m (F.cell gtop)))
    (hb₂ : ∀ g : W → A, PR.HasRight p₂b fc g p₃ fc g)
    -- the pass
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft p₃ fc g p₃ fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft p₃ fc g p₄ fc (Function.update g t PR.one))
    (hhold : ∀ g : W → A, g rg = PR.one → PR.HasLeft p₄ fc g p₄ fc g)
    (hwalkC : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p₃ fc (PR.passTracksAt F.cell t restB k r) p₃ fc
        (PR.passTracksAt F.cell t restB k r))
    (hwalkD : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p₄ fc (PR.passTracksAt F.cell t restB k r) p₄ fc
        (PR.passTracksAt F.cell t restB k r))
    -- the scan back down to the marker
    (hback : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft p₄ fc g p₄ fc g)
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w) :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot) + 4)
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p₄ fc), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t restB m') (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- the marker's next address is not the last one, so it has an increment
  have hv'ne : ∃ x : Univ A R P K dd, ¬v' x := by
    by_contra hc
    push Not at hc
    exact absurd (hlinSet.2.2.1 v' (F.cell gbot) ((wmSetLt_iff _ _).mp hv').1
      (wmSetLe_of_full hlin hc (F.cell gbot))) ((wmSetLt_iff _ _).mp hv').2
  obtain ⟨v'', hi₂⟩ := exists_wmIncr hlin hv'ne
  -- the file top's predecessor, for the bounce
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin (s := F.cell gtop) (F.cell_nonempty gtop)
  -- step 1: erase the marker at `v`, moving right to `v'`
  have s₁ := PR.step_move (rest := restA) (rest' := restN) (m := m) hR hlin hi hAN
    (p := p₀) (p' := p₁) (f := fc) (f' := fc) h₀
  -- step 2: write the marker at `v'`, moving right to its increment
  have s₂ := PR.step_move (rest := restN) (rest' := restB) (m := m) hR hlin hi₂ hNB
    (p := p₁) (p' := p₂) (f := fc) (f' := fc) h₁
  -- the marker's next address is at or below the file, hence below its top
  have hv''le : WMSetLe WMLe v'' (F.cell gtop) :=
    hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr_of_lt hlin hi₂ hv') (F.cell_le hix (hbot gtop))
  -- the scan up to the file top
  have hscan := reachesIn_toCell (cell := F.cell) (StopG := fun g => g rl = PR.one) hR hlin
    (t := t) (rest := restB) (m := m) (p := p₂) (f := fc)
    (fun g hg => hscanUp g hg) (u := F.cell gtop) (s := v'')
    (by rw [passTracks_of_ne hnerl, hrlB]; exact bitVal_pos rfl)
    hv''le
    (fun r _ hstop => by
      rw [passTracks_of_ne hnerl, hrlB] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- the bounce: two steps, left then right, changing phase
  have s₃ := PR.step_moveBack (rest := restB) (rest' := restB) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₂) (p' := p₂b) (f := fc) (f' := fc) hb₁
  have s₄ := PR.step_move (t := t) (rest := restB) (rest' := restB) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₂b) (p' := p₃) (f := fc) (f' := fc)
    (hb₂ (PR.passTracksAt F.cell t restB m pt))
  -- the mirror increment, down the file
  obtain ⟨u₀, pend, -, hpend, hpass⟩ := PR.reachesIn_fileIncr F hR hlin hix him hnerg
    (rest := restB) hrgB (pc := p₃) (pd := p₄) (fc := fc)
    hclear hset hhold hwalkC hwalkD hgap htop hbot
  -- the scan back down to the marker
  have hle_back : WMSetLe WMLe v' pend :=
    (wmSetLt_iff_of_wmIncr hlin hpend v').mp hv'
  have hret := reachesIn_toCellBack (cell := F.cell) (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := restB) (m := m') (p := p₄) (f := fc)
    (fun g hg => hback g hg) (u := v') (s := pend)
    (by rw [passTracks_of_ne hnewk, hwkB]; exact bitVal_pos rfl)
    hle_back
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkB] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- chain the seven phases
  refine (TMData.ReachesIn.head s₁ (TMData.ReachesIn.head s₂
    (hscan.trans (TMData.ReachesIn.head s₃ (TMData.ReachesIn.head s₄
      (hpass.trans hret)))))).mono ?_
  have h₁ : wideRank (F.cell gtop) - wideRank v'' ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
  have h₂ : wideRank pend - wideRank v' ≤ wideRank (F.cell gbot) :=
    le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hpend))
  omega

/-- **One round of a sweep**, the budget forgotten. -/
theorem reaches_fileAdvance (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    -- the slots: walked mirror track, register mark, file-top mark, cell marker
    {t rg rl wk : W} (hnerg : t ≠ rg) (hnerl : rl ≠ t) (hnewk : wk ≠ t)
    -- the two extremal elements
    {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)
    -- the marker's addresses, strictly below the register file
    {v v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v v')
    (hv' : WMSetLt WMLe v' (F.cell gbot))
    -- the mirror's contents
    {m m' : I → Prop} (him : WMIncr ile m m')
    -- the three backgrounds and their slot equations
    {restA restN restB : (Univ A R P K dd → Prop) → W → A}
    (hAN : ∀ r, r ≠ v → restN r = restA r)
    (hNB : ∀ r, r ≠ v' → restB r = restN r)
    (hwkB : ∀ r, restB r wk = bitVal PR.zero PR.one (r = v'))
    (hrgB : ∀ r, restB r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hrlB : ∀ r, restB r rl = bitVal PR.zero PR.one (r = F.cell gtop))
    -- the phases and the fixed pointer
    {p₀ p₁ p₂ p₂b p₃ p₄ : P} {fc : Q → A}
    -- the two marker steps
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt F.cell t restA m v) p₁ fc
      (PR.passTracksAt F.cell t restN m v))
    (h₁ : PR.HasRight p₁ fc (PR.passTracksAt F.cell t restN m v') p₂ fc
      (PR.passTracksAt F.cell t restB m v'))
    -- the scan up to the file top
    (hscanUp : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight p₂ fc g p₂ fc g)
    -- the bounce
    (hb₁ : PR.HasLeft p₂ fc (PR.passTracksAt F.cell t restB m (F.cell gtop)) p₂b fc
      (PR.passTracksAt F.cell t restB m (F.cell gtop)))
    (hb₂ : ∀ g : W → A, PR.HasRight p₂b fc g p₃ fc g)
    -- the pass
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft p₃ fc g p₃ fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft p₃ fc g p₄ fc (Function.update g t PR.one))
    (hhold : ∀ g : W → A, g rg = PR.one → PR.HasLeft p₄ fc g p₄ fc g)
    (hwalkC : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p₃ fc (PR.passTracksAt F.cell t restB k r) p₃ fc
        (PR.passTracksAt F.cell t restB k r))
    (hwalkD : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p₄ fc (PR.passTracksAt F.cell t restB k r) p₄ fc
        (PR.passTracksAt F.cell t restB k r))
    -- the scan back down to the marker
    (hback : ∀ g : W → A, g wk ≠ PR.one → PR.HasLeft p₄ fc g p₄ fc g) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p₄ fc), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t restB m') (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- the marker's next address is not the last one, so it has an increment
  have hv'ne : ∃ x : Univ A R P K dd, ¬v' x := by
    by_contra hc
    push Not at hc
    exact absurd (hlinSet.2.2.1 v' (F.cell gbot) ((wmSetLt_iff _ _).mp hv').1
      (wmSetLe_of_full hlin hc (F.cell gbot))) ((wmSetLt_iff _ _).mp hv').2
  obtain ⟨v'', hi₂⟩ := exists_wmIncr hlin hv'ne
  -- the file top's predecessor, for the bounce
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin (s := F.cell gtop) (F.cell_nonempty gtop)
  -- step 1: erase the marker at `v`, moving right to `v'`
  have s₁ := PR.step_move (rest := restA) (rest' := restN) (m := m) hR hlin hi hAN
    (p := p₀) (p' := p₁) (f := fc) (f' := fc) h₀
  -- step 2: write the marker at `v'`, moving right to its increment
  have s₂ := PR.step_move (rest := restN) (rest' := restB) (m := m) hR hlin hi₂ hNB
    (p := p₁) (p' := p₂) (f := fc) (f' := fc) h₁
  -- the marker's next address is at or below the file, hence below its top
  have hv''le : WMSetLe WMLe v'' (F.cell gtop) :=
    hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr_of_lt hlin hi₂ hv') (F.cell_le hix (hbot gtop))
  -- the scan up to the file top
  have hscan := reaches_toCell (cell := F.cell) (StopG := fun g => g rl = PR.one) hR hlin
    (t := t) (rest := restB) (m := m) (p := p₂) (f := fc)
    (fun g hg => hscanUp g hg) (u := F.cell gtop) (s := v'')
    (by rw [passTracks_of_ne hnerl, hrlB]; exact bitVal_pos rfl)
    hv''le
    (fun r _ hstop => by
      rw [passTracks_of_ne hnerl, hrlB] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- the bounce: two steps, left then right, changing phase
  have s₃ := PR.step_moveBack (rest := restB) (rest' := restB) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₂) (p' := p₂b) (f := fc) (f' := fc) hb₁
  have s₄ := PR.step_move (t := t) (rest := restB) (rest' := restB) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₂b) (p' := p₃) (f := fc) (f' := fc)
    (hb₂ (PR.passTracksAt F.cell t restB m pt))
  -- the mirror increment, down the file
  obtain ⟨u₀, pend, -, hpend, hpass⟩ := PR.reaches_fileIncr F hR hlin hix him hnerg
    (rest := restB) hrgB (pc := p₃) (pd := p₄) (fc := fc)
    hclear hset hhold hwalkC hwalkD htop hbot
  -- the scan back down to the marker
  have hle_back : WMSetLe WMLe v' pend :=
    (wmSetLt_iff_of_wmIncr hlin hpend v').mp hv'
  have hret := reaches_toCellBack (cell := F.cell) (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := restB) (m := m') (p := p₄) (f := fc)
    (fun g hg => hback g hg) (u := v') (s := pend)
    (by rw [passTracks_of_ne hnewk, hwkB]; exact bitVal_pos rfl)
    hle_back
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkB] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- chain the seven phases
  exact Relation.ReflTransGen.head s₁ (Relation.ReflTransGen.head s₂
    (hscan.trans (Relation.ReflTransGen.head s₃ (Relation.ReflTransGen.head s₄
      (hpass.trans hret)))))

end Prog

end Pfp

end DescriptiveComplexity
