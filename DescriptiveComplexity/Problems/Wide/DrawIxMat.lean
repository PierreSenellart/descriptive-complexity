/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxIGate
import DescriptiveComplexity.Problems.Wide.DrawIxStage
import DescriptiveComplexity.Problems.Wide.DrawInstMat

/-!
# The matrix's stages at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawInstMat` read at a coarse file: the
four atom runs – comparison, expansion, stage and gate block – wrapped into the
one shape the sequencer drives them through, entry one cell to the marker's
right at the `Slot.val`-walked presentation and exit at the next checkpoint.
Each wrapper is the clocked run of its atom with the walk-back the dispatch
owes, so each carries its atom's budget plus one step.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {I : Type} [Finite I] (F : LaidFile dt A R P I)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable [Nonempty A] [L.IsRelational] [L.Structure A]

variable {dt}
variable {e₀ : Univ A R P dt.KIx dt.dd} (he₀ : ∀ y, WMLe e₀ y)

omit [Finite I] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- The `val`-walked and the `mir`-walked presentations of one state
coincide: both are the naked background. -/
theorem trackTape_val_eq_ixMir (st : TapeSt dt A R P I) :
    PR.trackTapeAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val =
      PR.trackTapeAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir := by
  refine (trackTape_of_back (t := Slot.val)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (m := st.val)
    F.toIxFile fun _ => rfl).trans
    (trackTape_of_back (t := Slot.mir)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (m := st.mir)
      F.toIxFile fun _ => rfl).symm

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
variable {gbot : I} (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v)


omit [L.IsRelational] [L.Structure A] in
omit [Finite I] in
include hrules hR hlin hix hbot hv hvi hwkSt hhasP hsepP in
/-- **The comparison atom, entered by a dispatch**: from its entry
checkpoint one cell to the marker's right, at the `Slot.val`-walked
presentation, to the exit phase back at the same cell. -/
theorem ixCmp_hStage (f : dt.CtlIx → A) (w : ℕ)
    (hcost : ∀ (b : Lex (Fin dt.dd0 → A)) (k : Fin 2),
      2 * (wideRank (F.cell (dt.cmpCell F PR.zero hhasP vi j₁ j₂ b k)) -
        wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (1 + ((2 + (w + 2) * 2) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1))
      ⟨Sum.inr (PR.stElt (emb .e0) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.cmpArgs PR.zero PR.one vi av hnf isEq j₁ j₂).exitSt
            (dt.cmpFam F PR.zero PR.one hhasP vi av hnf isEq j₁ j₂ st v f
              (toLex topTup) (Fin.last 2))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  rw [trackTape_val_eq_ixMir F st]
  refine TMData.ReachesIn.trans
    (TMData.reachesIn_of_step
      (elem_back F.toIxFile hlin hvi hwkS hne_wk_mir hR hrules)) ?_
  exact dt.cmp_reachesIn F hhasP hsepP vi av hnf isEq j₁ j₂ hrules hR hlin hix hbot
    hv hvi hwkSt f w hcost

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
variable {gbot : I} (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v)
variable (pts : Fin k → dt.X.Map A)
variable (hENC : ∀ ℓ : Fin k,
  wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
    (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
    encMap dt.ly PR.zero PR.one (pts ℓ))


omit [Finite I] in
include hrules hR hlin hix hbot hv hvi hwkSt hinj helt hENC hhasP hsepP in
/-- **The expansion atom, entered by a dispatch**: from its first phase one
cell to the marker's right, at the `Slot.val`-walked presentation, to the
exit phase back at the same cell. -/
theorem ixExp_hStage (f : dt.CtlIx → A) (w : ℕ)
    (hcostT : ∀ i : Fin (k * Fintype.card dt.X.Tag),
      2 * (wideRank (F.cell (dt.ixExpTagCell F hhasP PR.one vi ts i)) -
        wideRank v) + 2 ≤ w)
    (hcostE : ∀ (a : Lex (Fin dt.eDim → A))
        (r : Fin (dt.relNr e (fun ℓ => (pts ℓ).1.1))),
      2 * (wideRank (F.cell (dt.ixExpECell F hhasP PR.one vi ts e
        (fun ℓ => (pts ℓ).1.1) (hn (fun ℓ => (pts ℓ).1.1)) a r)) -
        wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (1 + ((w + 2) * (k * Fintype.card dt.X.Tag) + 2 +
        ((2 + (w + 2) * dt.relNr e (fun ℓ => (pts ℓ).1.1)) *
          (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1)))
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt
            (fun ℓ => (pts ℓ).1.1)
            (dt.ixExpFam F hhasP PR.one vi ts e av st (fun ℓ => (pts ℓ).1.1)
              hk hn hrd v
              (dt.ixExpTagFam F hhasP PR.one vi ts e av st hk hn hrd v f
                (Fin.last (k * Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  refine TMData.ReachesIn.trans
    (TMData.reachesIn_of_step
      (tag_back F.toIxFile hlin hvi hwkS hne_wk_val hR hrules)) ?_
  exact dt.ixExp_reachesIn F hhasP hsepP hix vi ts e av st hk hn hrd hinj helt hrules hR
    hlin hbot hv hvi hwkSt (fun r => rfl) hne_wk_val hne_rg_val pts hENC f w
    hcostT hcostE

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
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = ixMark elt v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)


omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite dt.KIx] [Nonempty A] [L.IsRelational] [L.Structure A] in
/-- **A stage atom entered at the boundary leaves the state unchanged**, at an
arbitrary file: with SAV and TARGET already the marks of the home address, the
restore restores what was there. -/
theorem ixStageEndSt_eq {I : Type} {st : TapeSt dt A R P I}
    {elt : I → Univ A R P dt.KIx dt.dd} {v : Univ A R P dt.KIx dt.dd → Prop}
    (hs : st.sav = ixMark elt v) (ht : st.tgt = ixMark elt v) :
    dt.ixStageEndSt st elt v = st := by
  rw [ixStageEndSt]
  obtain ⟨mir, tgt, sav, val, old, new, wk, bot, ltp⟩ := st
  change sav = ixMark elt v at hs
  change tgt = ixMark elt v at ht
  subst hs
  subst ht
  rfl

variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ (ℓ : Fin (dt.d.B.arity iv)) (bb : Lex (Fin dt.dd0 → A)),
  Use (dt.ixStageXD F hhasP ℓ bb))

omit [L.IsRelational] [L.Structure A] hsav htgt in
include hrules hR hlin hix hhasP hsepP hinj hmono hup helt hord htop hbot he₀
  hwork hv hvi hwkSt hmirSt hbotSt hvh hxdUse in
/-- **The stage atom, threaded**: the same run as
`DescriptiveComplexity.Draw.Data.ixStage_hStage` with *no* boundary
discipline assumed – the random access writes the home address into SAV and
TARGET whatever they held, so its exit state is the normalized
`DescriptiveComplexity.Draw.Data.ixStageEndSt`. -/
theorem ixStage_hStage_thread (b : Bool) (w wG wP wR wK : ℕ)
    (hcost : ∀ (ℓ : Fin (dt.d.B.arity iv)) (a : Lex (Fin dt.dd0 → A)),
      2 * (wideRank (F.cell (dt.ixStageXS F hhasP vi ts ℓ a)) - wideRank v) + 2 ≤ w ∧
        2 * (wideRank (F.cell (dt.ixStageXD F hhasP ℓ a)) - wideRank v) + 2 ≤ w)
    (hgap : ∀ u u' : I, IxSucc F.le u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
    (hwP : wideRank (F.cell gtop) + 2 +
      ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
    (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
    (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe T (F.cell gbot) →
      wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) ≤ wK)
    (hb : st.old iv (ixAddr elt
        (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
          (dt.d.B.arity iv))) ↔ b = true)
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (5 * wP + 2 * wR + 2 * wK +
        (((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
          dt.d.B.arity iv) + 13)
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f (dt.d.B.arity iv))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixStageAtSt st elt v (ixAddr elt
                (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                  (dt.d.B.arity iv))))
              (ixAddr elt (dt.ixStageTgt F hhasP vi ts
                { st with sav := ixMark elt v } (dt.d.B.arity iv)))))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).val) (PR.syElt PR.blank)⟩ := by
  rw [trackTape_val_eq_ixMir F st, trackTape_val_eq_ixMir F (dt.ixStageEndSt st elt v)]
  exact dt.ixStageAtom_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (heltP := helt)
    (vi := vi) (ts := ts) (av := av) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (hvh := hvh) (hxdUse := hxdUse) (f₀ := f) (b := b) (w := w) (wG := wG)
    (wP := wP) (wR := wR) (wK := wK) (hcost := hcost) (hgap := hgap) (hwP := hwP)
    (hwR := hwR) (hwK := hwK) (hb := hb)

omit [L.IsRelational] [L.Structure A] in
include hrules hR hlin hix hhasP hsepP hinj hmono hup helt hord htop hbot he₀
  hwork hv hvi hwkSt hmirSt hbotSt hvh hxdUse hsav htgt in
/-- **The stage atom, entered by a dispatch**: at the boundary discipline – SAV
and TARGET at the home address – the random access runs and restores the state,
so the sequencer's background is untouched. -/
theorem ixStage_hStage (b : Bool) (w wG wP wR wK : ℕ)
    (hcost : ∀ (ℓ : Fin (dt.d.B.arity iv)) (a : Lex (Fin dt.dd0 → A)),
      2 * (wideRank (F.cell (dt.ixStageXS F hhasP vi ts ℓ a)) - wideRank v) + 2 ≤ w ∧
        2 * (wideRank (F.cell (dt.ixStageXD F hhasP ℓ a)) - wideRank v) + 2 ≤ w)
    (hgap : ∀ u u' : I, IxSucc F.le u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
    (hwP : wideRank (F.cell gtop) + 2 +
      ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
    (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
    (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
      WMSetLt WMLe T (F.cell gbot) →
      wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) ≤ wK)
    (hb : st.old iv (ixAddr elt
        (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
          (dt.d.B.arity iv))) ↔ b = true)
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (5 * wP + 2 * wR + 2 * wK +
        (((2 * w + 8) * (Nat.card (Lex (Fin dt.dd0 → A)) + 1) + 1 + 1) *
          dt.d.B.arity iv) + 13)
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.ixStageFAt F hhasP PR.one vi ts av st elt v f (dt.d.B.arity iv))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixStageAtSt st elt v (ixAddr elt
                (dt.ixStageTgt F hhasP vi ts { st with sav := ixMark elt v }
                  (dt.d.B.arity iv))))
              (ixAddr elt (dt.ixStageTgt F hhasP vi ts
                { st with sav := ixMark elt v } (dt.d.B.arity iv)))))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  rw [trackTape_val_eq_ixMir F st]
  have h := dt.ixStageAtom_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (heltP := helt)
    (vi := vi) (ts := ts) (av := av) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork)
    (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt) (hbotSt := hbotSt)
    (hvh := hvh) (hxdUse := hxdUse) (f₀ := f) (b := b) (w := w) (wG := wG)
    (wP := wP) (wR := wR) (wK := wK) (hcost := hcost) (hgap := hgap) (hwP := hwP)
    (hwR := hwR) (hwK := hwK) (hb := hb)
  rw [ixStageEndSt_eq hsav htgt] at h
  exact h

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
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v)
variable (Test : I → Prop)
variable {wG : ℕ} (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hcompat : ∀ u : I,
  wellG (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    st.mir (F.cell u)) ↔ Test u)


include hrules hR hlin hix htop hbot hv hvi hwkSt hcompat hgap hinj helt hhasP hsepP in
/-- **A passing gate block, entered by a dispatch**: every register is
well-shaped, so the file test passes, the domain evaluation runs on the
block's decoded tag, and the block exits to the next checkpoint. -/
theorem ixGateBlock_hStage_pos (t : dt.X.Tag)
    (htag : dt.dspTagOf PR.zero PR.one
      (wmBlk (ixAddr elt st.mir) (Tag.arg (toLex b) : Tag R P dt.KIx)) = t)
    (hTest : ∀ u, Test u) (f : dt.CtlIx → A) (w : ℕ)
    (hcostT : ∀ c : Fin (Fintype.card dt.X.Tag),
      2 * (wideRank (F.cell (dt.ixGateTagCell F hhasP PR.one b c)) -
        wideRank v) + 2 ≤ w)
    (hcostE : ∀ (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.domNr t)),
      2 * (wideRank (F.cell (dt.ixGateECell F hhasP PR.one b t (hn t) a r)) -
        wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((wideRank (F.cell gtop) + 2 + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
        wideRank (F.cell gbot)) + (1 + (1 +
        ((w + 2) * Fintype.card dt.X.Tag + 2 +
          ((2 + (w + 2) * dt.domNr t) *
            (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1)))))
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.gateArgs PR.zero PR.one b hc hn hrd).exitSt t
            (dt.ixGateFam F hhasP PR.one b st t hc hn hrd v
              (dt.ixGateTagFam F hhasP PR.one b st hc hn hrd v f
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr t)))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_rg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_mir_rg : (Slot.mir : dt.SlotIx) ≠ Slot.reg := fun h => nomatch h
  have hne_rl_mir : (Slot.regLast : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  rw [trackTape_val_eq_ixMir F st]
  -- the file test, passing
  have hkrules : ∀ ρ : TestRule, PR.rules (rEmb (Sum.inl ()) (Sum.inl ρ)) =
      (TestKit.mk (A := A) (Q := dt.CtlIx) Slot.mir Slot.reg Slot.regLast
        Slot.wk wellG (fun tp => emb (Sum.inl tp))).rule PR.one ρ :=
    fun ρ => hrules (Sum.inl ()) (Sum.inl ρ)
  have htest := TestKit.reachesIn_pos
    (F := F.toIxFile)
    (hsle := F.toIxFile.le_cell_top_of_le hix hbot
      (wmSetLe_of_wmIncr_of_lt hlin hvi hv))
    hkrules hR hlin hix hne_mir_rg hne_rl_mir
    hne_wk_mir htop hbot hv (fun r => rfl)
    (fun r => dt.ixBack_regLast hix htop r) hwkS hcompat hgap hTest
    (fc := f) (s := v')
  refine htest.trans ?_
  -- the passing exit, into the domain evaluation
  have hexit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .ty)) f), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (dt.gateDomEntry emb) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (Sum.inl ()) (Sum.inr true)
    refine ⟨rEmb (Sum.inl ()) (Sum.inr true), ?_, by rw [h]; rfl,
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; trivial⟩
    rw [h]
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_mir, hwkS]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_rg_mir,
        show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v Slot.reg =
          bitVal PR.zero PR.one (∃ u : I, v = F.cell u) from rfl,
        bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
      exact PR.zero_ne_one
  refine (TMData.reachesIn_of_step hexit).trans ?_
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
  refine TMData.ReachesIn.trans
    (TMData.reachesIn_of_step
      (tag_back F.toIxFile hlin hvi hwkS hne_wk_mir hR hdomrules)) ?_
  exact dt.ixGate_reachesIn (F := F) (hhasP := hhasP) (hsepR := hsepP) (hixR := hix)
    (b := b) (st := st) (t := t) (hc := hc) (hn := hn) (hrd := hrd) (hinjR := hinj)
    (heltR := helt) (hrules := hdomrules) (hR := hR) (hlin := hlin) (hbot := hbot)
    (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (t₀ := Slot.mir) (m₀ := st.mir) (hm₀ := fun r => rfl)
    (hwkt₀ := hne_wk_mir) (hrgt₀ := hne_rg_mir) (htag := htag) (f₀ := f) (w := w)
    (hcostT := hcostT) (hcostE := hcostE)


omit hhasP hsepP hinj helt in
include hrules hR hlin hix htop hbot hv hvi hwkSt hcompat hgap in
/-- **A failing gate block**: some register is not well-shaped, so the file
test fails and the block leaves the whole gate sequence through the failing
exit, the fail store applied at the marker's symbol. -/
theorem ixGateBlock_hStage_neg {u : I}
    (hTest : ¬Test u) (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((wideRank (F.cell gtop) + 2 + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
        wideRank (F.cell gbot)) + 1)
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt failPh
          (setFail f (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_rg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_mir_rg : (Slot.mir : dt.SlotIx) ≠ Slot.reg := fun h => nomatch h
  have hne_rl_mir : (Slot.regLast : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  rw [trackTape_val_eq_ixMir F st]
  have hkrules : ∀ ρ : TestRule, PR.rules (rEmb (Sum.inl ()) (Sum.inl ρ)) =
      (TestKit.mk (A := A) (Q := dt.CtlIx) Slot.mir Slot.reg Slot.regLast
        Slot.wk wellG (fun tp => emb (Sum.inl tp))).rule PR.one ρ :=
    fun ρ => hrules (Sum.inl ()) (Sum.inl ρ)
  have htest := TestKit.reachesIn_neg
    (F := F.toIxFile)
    (hsle := F.toIxFile.le_cell_top_of_le hix hbot
      (wmSetLe_of_wmIncr_of_lt hlin hvi hv))
    hkrules hR hlin hix hne_mir_rg hne_rl_mir
    hne_wk_mir htop hbot hv (fun r => rfl)
    (fun r => dt.ixBack_regLast hix htop r) hwkS hcompat hgap hTest
    (fc := f) (s := v')
  refine htest.trans (TMData.reachesIn_of_step ?_)
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules (Sum.inl ()) (Sum.inr false)
  refine ⟨rEmb (Sum.inl ()) (Sum.inr false), ?_, by rw [h]; rfl,
    by rw [h]; rfl, ?_, by rw [h]; rfl, by rw [h]; trivial⟩
  · rw [h]
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_mir, hwkS]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_rg_mir,
        show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v Slot.reg =
          bitVal PR.zero PR.one
            (∃ u' : I, v = F.cell u') from rfl,
        bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
      exact PR.zero_ne_one
  · rw [h]
    change setFail f (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir v) = _
    rw [passTracks_of_back (t := Slot.mir)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (m := st.mir)
      F.toIxFile (fun r => rfl) v]

end GateBlockStage

end Data

end Draw

end DescriptiveComplexity
