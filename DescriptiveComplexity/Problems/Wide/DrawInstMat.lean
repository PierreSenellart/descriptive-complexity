/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstGate

/-!
# The matrix's stages: the atom runs in the sequencer's shape

The sequencer (`DescriptiveComplexity.Draw.seq_run`) drives its stages
through one uniform interface: entry one cell to the marker's right, one
fixed walked track, exit at the next checkpoint. This file wraps the four
instantiated atom runs into that shape:

* `DescriptiveComplexity.Draw.elem_back` – the walk-back a dispatch into an
  element loop owes (the machinery's own `.e0` stay rule);
* `DescriptiveComplexity.Draw.Data.stageEndSt_eq` – the boundary
  discipline: a stage atom entered with SAV and TARGET at the home address
  leaves the state **unchanged**, so the matrix's background is constant
  across its atoms;
* the three wrappers `cmp_hStage`/`exp_hStage`/`stage_hStage`, all at the
  `Slot.val`-walked presentation of one boundary state – the presentation
  `DescriptiveComplexity.Draw.Data.var_run` hands the matrix.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The element loop's walk-back -/

section ElemBack

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {nr : ℕ}
variable {I : Type} {ile : I → I → Prop} (RF : IxFile (Univ A R P K dd) I ile)
variable {wk rg : W} {emb : ElemPh nr → P}
variable {rdTrack : Fin nr → W}
variable {MatchOf : Fin nr → (Q → A) → (W → A) → Prop}
variable {setFlag : Fin nr → Bool → (Q → A) → (W → A) → (Q → A)}
variable {initEl advEl exitSt : (Q → A) → (W → A) → (Q → A)}
variable {IsMaxEl : (Q → A) → Prop}
variable {exitPh : P}
variable {rEmb : ∀ i : ElemSite nr, ElemSh nr i → R}
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {v v' : Univ A R P K dd → Prop} (hvi : WMIncr WMLe v v')
variable {rest : (Univ A R P K dd → Prop) → W → A}
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))
variable {t₀ : W} {m₀ : I → Prop}
variable (hwkt₀ : wk ≠ t₀)

include hlin hvi hwkS hwkt₀ in
/-- The one leftward step a caller's rightward dispatch into an element
loop owes: at its entry checkpoint, the walk back down to the marker. -/
theorem elem_back (hR : PR.table.Reads)
    (hrules : ∀ (i : ElemSite nr) (ρ : ElemSh nr i),
      PR.rules (rEmb i ρ) = elemRule PR.one wk rg emb rdTrack MatchOf setFlag
        initEl advEl exitSt IsMaxEl exitPh i ρ)
    {f : Q → A} :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .e0) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hwkv' : PR.passTracksAt RF.cell t₀ rest m₀ v' wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hwkt₀, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules .e0 .stay
  exact ⟨rEmb .e0 .stay, by rw [h]; exact hwkv', by rw [h]; rfl,
    by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
    fun hc => (by rw [h] at hc; exact hc)⟩

end ElemBack

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hordM : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

/-! ### The boundary discipline -/

variable {dt}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A stage atom entered at the boundary leaves the state unchanged**:
with SAV and TARGET already at the home address, the restore restores what
was there. -/
theorem stageEndSt_eq {st : TapeStD dt A R P}
    {v : Univ A R P dt.KIx dt.dd → Prop}
    (hs : st.sav = v) (ht : st.tgt = v) : dt.stageEndSt st v = st := by
  rw [stageEndSt, ixStageEndSt]
  change { st with sav := v, tgt := v } = st
  obtain ⟨mir, tgt, sav, val, old, new, wk, bot, ltp⟩ := st
  change sav = v at hs
  change tgt = v at ht
  subst hs
  subst ht
  rfl

omit [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- The `val`-walked and the `mir`-walked presentations of one state
coincide: both are the naked background. -/
theorem trackTape_val_eq_mir (st : TapeStD dt A R P) :
    PR.trackTapeAt RF.cell Slot.val (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val =
      PR.trackTapeAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.mir := by
  refine (trackTape_of_back (t := Slot.val)
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (m := st.val)
    RF.toIx fun _ => rfl).trans
    (trackTape_of_back (t := Slot.mir)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (m := st.mir)
      RF.toIx fun _ => rfl).symm

/-! ### The comparison atom, in the sequencer's shape -/

section CmpStage

variable (vi : dt.VarIx) (av : Fin dt.natMax) (hnf : 2 ≤ dt.nfDim)
variable (isEq : Bool) (j₁ j₂ : Fin (dt.nOf vi))
variable {emb : ElemPh 2 → P} {exitPh : P}
variable {rEmb : ∀ i : ElemSite 2, ElemSh 2 i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : ElemSite 2) (ρ : ElemSh 2 i),
  PR.rules (rEmb i ρ) = elemRule PR.one Slot.wk Slot.reg emb
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).rdTrack
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).MatchOf
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).setFlag
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).initEl
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).advEl
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
    (dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).IsMaxEl exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : Univ A R P dt.KIx dt.dd} (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeStD dt A R P}
variable (hwkSt : st.wk = fun r => r = v)

omit [L.IsRelational] [L.Structure A] in
include hrules hR hlin hordM hbot hv hvi hwkSt in
/-- **The comparison atom, entered by a dispatch**: from its entry
checkpoint one cell to the marker's right, at the `Slot.val`-walked
presentation, to the exit phase back at the same cell. -/
theorem cmp_hStage (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
            (dt.cmpFam (laidFile RF hordM) PR.zero PR.one (dt.hasName_diagLayout (cell := RF.cell)
                (zero := PR.zero)) vi av hnf isEq j₁ j₂ st v f
              (toLex topTup) (Fin.last 2))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  rw [trackTape_val_eq_mir RF st]
  refine Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (elem_back RF.toIx hlin hvi hwkS hne_wk_mir hR hrules)) ?_
  exact dt.cmp_run (laidFile RF hordM)
    (dt.hasName_diagLayout (cell := RF.cell) (zero := PR.zero))
    (dt.nameSep_diagLayout (cell := RF.cell) (zero := PR.zero) (hdd := dt.dd0Le))
    vi av hnf isEq j₁ j₂ hrules hR hlin (isLinOrd_laidFile_le hlin)
    (fun y => (hordM _ y).mp (hbot y)) hv hvi hwkSt f

end CmpStage

/-! ### The expansion atom, in the sequencer's shape -/

section ExpStage

variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable {emb : TagPh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
  (dt.relNr e) → P}
variable {exitPh : P}
variable {rEmb : ∀ i : TagSite (k * Fintype.card dt.X.Tag)
    (Fin k → dt.X.Tag) (dt.relNr e),
  TagSh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag) (dt.relNr e) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : TagSite (k * Fintype.card dt.X.Tag)
      (Fin k → dt.X.Tag) (dt.relNr e))
    (ρ : TagSh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
      (dt.relNr e) i),
  PR.rules (rEmb i ρ) = tagRule PR.one Slot.wk Slot.reg emb
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).MatchT)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).TagsAre)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).MatchE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).IsMaxEl)
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : Univ A R P dt.KIx dt.dd} (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeStD dt A R P}
variable (hwkSt : st.wk = fun r => r = v)
variable (pts : Fin k → dt.X.Map A)
variable (hENC : ∀ ℓ : Fin k,
  wmBlk (dt.lvSet st vi (ts ℓ))
    (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
    encMap dt.ly PR.zero PR.one (pts ℓ))

include hrules hR hlin hordM hbot hv hvi hwkSt hENC in
/-- **The expansion atom, entered by a dispatch**: from its first phase one
cell to the marker's right, at the `Slot.val`-walked presentation, to the
exit phase back at the same cell. -/
theorem exp_hStage (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt
            (fun ℓ => (pts ℓ).1.1)
            (dt.expFam RF PR.zero PR.one vi ts e av st (fun ℓ => (pts ℓ).1.1)
              hk hn hrd v
              (dt.expTagFam RF PR.zero PR.one vi ts e av st hk hn hrd v f
                (Fin.last (k * Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  refine Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (tag_back RF.toIx hlin hvi hwkS hne_wk_val hR hrules)) ?_
  exact dt.exp_run RF hordM hrules hR hlin hbot hv hvi hwkSt (fun r => rfl)
    hne_wk_val hne_rg_val pts hENC f

end ExpStage

/-! ### The stage atom, in the sequencer's shape -/

section StageStage

variable (vi : dt.VarIx) (iv : dt.d.B.ι)
variable (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
variable (av : Fin dt.natMax)
variable {emb : StagePh (dt.d.B.arity iv) → P} {exitPh : P}
variable {rEmb : ∀ i : StageSite (dt.d.B.arity iv),
  StageSh (dt.d.B.arity iv) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : StageSite (dt.d.B.arity iv))
    (ρ : StageSh (dt.d.B.arity iv) i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).coord
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).oldSlot
    (dt.stageArgs PR.zero PR.one vi iv ts av).setAv
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeStD dt A R P}
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = v) (htgt : st.tgt = v)

omit [L.IsRelational] [L.Structure A] in
include hrules hR hlin hord htop hbot hwork hv hvi hwkSt hmirSt hbotSt hsav htgt in
/-- **The stage atom, entered by a dispatch**: at the boundary discipline –
SAV and TARGET at the home address – the random access runs and restores
the state, so the sequencer's background is untouched. -/
theorem stage_hStage (b : Bool)
    (hb : st.old iv (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)) ↔
      b = true)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.stageFAt RF PR.zero PR.one vi iv ts av st v f
              (dt.d.B.arity iv))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le
              (dt.stageAtSt st v
                (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)))
              (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv))))),
        Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  rw [trackTape_val_eq_mir RF st]
  have h := dt.stageAtom_run RF hord hrules hR hlin htop hbot hwork hv hvi hwkSt
    hmirSt hbotSt f b hb
  rw [stageEndSt_eq hsav htgt] at h
  exact h

omit [L.IsRelational] [L.Structure A] in
include hrules hR hlin hord htop hbot hwork hv hvi hwkSt hmirSt hbotSt in
/-- **The stage atom, threaded**: the same run as
`DescriptiveComplexity.Draw.Data.stage_hStage` with *no* boundary
discipline assumed — the random access writes the home address into SAV and
TARGET whatever they held, so its exit state is the normalized
`DescriptiveComplexity.Draw.Data.stageEndSt st v` rather than `st`.

This is the form the outer sweep needs: at a swept address SAV and TARGET
still hold the *previous* address (the advance refreshes only the marker and
the mirror), so `stage_hStage`'s two hypotheses are unavailable there and
the normalization has to be carried instead of assumed. -/
theorem stage_hStage_thread (b : Bool)
    (hb : st.old iv (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)) ↔
      b = true)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.stageFAt RF PR.zero PR.one vi iv ts av st v f
              (dt.d.B.arity iv))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le
              (dt.stageAtSt st v
                (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)))
              (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv))))),
        Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.stageEndSt st v))
          (dt.stageEndSt st v).val)
          (PR.syElt PR.blank)⟩ := by
  rw [trackTape_val_eq_mir RF st, trackTape_val_eq_mir RF (dt.stageEndSt st v)]
  exact dt.stageAtom_run RF hord hrules hR hlin htop hbot hwork hv hvi hwkSt
    hmirSt hbotSt f b hb

end StageStage

/-! ### One gate block, in the sequencer's shape -/

section GateBlockStage

variable (b : Fin dt.ko ⊕ Fin dt.ki)
variable (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
variable (hrd : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
variable {emb : dt.GateBlockPh → P}
variable (wellG : (dt.SlotIx → A) → Prop)
variable (setFail : (dt.CtlIx → A) → (dt.SlotIx → A) → dt.CtlIx → A)
variable {failPh exitPh : P}
variable {rEmb : ∀ i : dt.GateBlockSite, dt.GateBlockSh i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
  PR.rules (rEmb i ρ) = dt.gateBlockRule (one := PR.one) (emb := emb)
    (args := dt.gateArgs PR.zero PR.one b hc hn hrd) (wellG := wellG)
    (setFail := setFail) (failPh := failPh) (exitPh := exitPh) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeStD dt A R P}
variable (hwkSt : st.wk = fun r => r = v)
variable (Test : Univ A R P dt.KIx dt.dd → Prop)
variable (hcompat : ∀ u : Univ A R P dt.KIx dt.dd,
  wellG (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
    st.mir (RF.cell u)) ↔ Test u)

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompat in
/-- **A passing gate block, entered by a dispatch**: every register is
well-shaped, so the file test passes, the domain evaluation runs on the
block's decoded tag, and the block exits to the next checkpoint. -/
theorem gateBlock_hStage_pos (t : dt.X.Tag)
    (htag : dt.dspTagOf PR.zero PR.one
      (wmBlk st.mir (Tag.arg (toLex b) : Tag R P dt.KIx)) = t)
    (hTest : ∀ u, Test u) (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.gateArgs PR.zero PR.one b hc hn hrd).exitSt t
            (dt.gateFam RF PR.zero PR.one b st t hc hn hrd v
              (dt.gateTagFam RF PR.zero PR.one b st hc hn hrd v f
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr t)))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF.toIx hlin hlin hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_rg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_mir_rg : (Slot.mir : dt.SlotIx) ≠ Slot.reg := fun h => nomatch h
  have hne_rl_mir : (Slot.regLast : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  rw [trackTape_val_eq_mir RF st]
  -- the file test, passing
  have hkrules : ∀ ρ : TestRule, PR.rules (rEmb (Sum.inl ()) (Sum.inl ρ)) =
      (TestKit.mk (A := A) (Q := dt.CtlIx) Slot.mir Slot.reg Slot.regLast
        Slot.wk wellG (fun tp => emb (Sum.inl tp))).rule PR.one ρ :=
    fun ρ => hrules (Sum.inl ()) (Sum.inl ρ)
  have htest := TestKit.reaches_pos
    (F := RF.toIx)
    (hsle := RF.le_cell_top_of_le hlin hbot
      (wmSetLe_of_wmIncr_of_lt hlin hvi hv))
    hkrules hR hlin hlin hne_mir_rg hne_rl_mir
    hne_wk_mir htop hbot hv (fun r => rfl)
    (fun r => dt.back_regLast hlin htop hord r) hwkS hcompat hTest
    (fc := f) (s := v')
  refine htest.trans ?_
  -- the passing exit, into the domain evaluation
  have hexit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .ty)) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (dt.gateDomEntry emb) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.mir
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (Sum.inl ()) (Sum.inr true)
    refine ⟨rEmb (Sum.inl ()) (Sum.inr true), ?_, by rw [h]; rfl,
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; trivial⟩
    rw [h]
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_mir, hwkS]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_rg_mir,
        show dt.back RF.cell PR.zero PR.one dt.dd0Le st v Slot.reg =
          bitVal PR.zero PR.one
            (∃ u : Univ A R P dt.KIx dt.dd, v = RF.cell u) from rfl,
        bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
      exact PR.zero_ne_one
  refine (Relation.ReflTransGen.single hexit).trans ?_
  -- the domain evaluation, entered
  have hdomrules : ∀ (i : TagSite (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr)
      (ρ : TagSh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr i),
      PR.rules (rEmb (Sum.inr i) ρ) = tagRule PR.one Slot.wk Slot.reg
        (fun p => emb (Sum.inr p))
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackT)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).MatchT)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).setTagFlag)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).TagsAre)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackE)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).MatchE)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).setFlagE)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).initEl)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).advEl)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).exitSt)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).IsMaxEl)
        exitPh i ρ :=
    fun i ρ => hrules (Sum.inr i) ρ
  refine Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (tag_back RF.toIx hlin hvi hwkS hne_wk_mir hR hdomrules)) ?_
  exact dt.gate_run RF hdomrules hR hlin hbot hv hvi hwkSt
    (t₀ := Slot.mir) (m₀ := st.mir) (fun r => rfl)
    hne_wk_mir hne_rg_mir htag f

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompat in
/-- **A failing gate block**: some register is not well-shaped, so the file
test fails and the block leaves the whole gate sequence through the failing
exit, the fail store applied at the marker's symbol. -/
theorem gateBlock_hStage_neg {u : Univ A R P dt.KIx dt.dd}
    (hTest : ¬Test u) (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt failPh
          (setFail f (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF.toIx hlin hlin hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_rg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_mir_rg : (Slot.mir : dt.SlotIx) ≠ Slot.reg := fun h => nomatch h
  have hne_rl_mir : (Slot.regLast : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  rw [trackTape_val_eq_mir RF st]
  have hkrules : ∀ ρ : TestRule, PR.rules (rEmb (Sum.inl ()) (Sum.inl ρ)) =
      (TestKit.mk (A := A) (Q := dt.CtlIx) Slot.mir Slot.reg Slot.regLast
        Slot.wk wellG (fun tp => emb (Sum.inl tp))).rule PR.one ρ :=
    fun ρ => hrules (Sum.inl ()) (Sum.inl ρ)
  have htest := TestKit.reaches_neg
    (F := RF.toIx)
    (hsle := RF.le_cell_top_of_le hlin hbot
      (wmSetLe_of_wmIncr_of_lt hlin hvi hv))
    hkrules hR hlin hlin hne_mir_rg hne_rl_mir
    hne_wk_mir htop hbot hv (fun r => rfl)
    (fun r => dt.back_regLast hlin htop hord r) hwkS hcompat hTest
    (fc := f) (s := v')
  refine htest.trans (Relation.ReflTransGen.single ?_)
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules (Sum.inl ()) (Sum.inr false)
  refine ⟨rEmb (Sum.inl ()) (Sum.inr false), ?_, by rw [h]; rfl,
    by rw [h]; rfl, ?_, by rw [h]; rfl, by rw [h]; trivial⟩
  · rw [h]
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_mir, hwkS]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_rg_mir,
        show dt.back RF.cell PR.zero PR.one dt.dd0Le st v Slot.reg =
          bitVal PR.zero PR.one
            (∃ u' : Univ A R P dt.KIx dt.dd, v = RF.cell u') from rfl,
        bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
      exact PR.zero_ne_one
  · rw [h]
    change setFail f (PR.passTracksAt RF.cell Slot.mir
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.mir v) = _
    rw [passTracks_of_back (t := Slot.mir)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (m := st.mir)
      RF.toIx (fun r => rfl) v]

end GateBlockStage

end Data

end Draw

end DescriptiveComplexity
