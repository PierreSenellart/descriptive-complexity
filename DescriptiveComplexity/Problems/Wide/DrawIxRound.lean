/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxSeq
import DescriptiveComplexity.Problems.Wide.DrawIxIGate
import DescriptiveComplexity.Problems.Wide.DrawInstRound

/-!
# One round of a variable's loop at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawInstRound` read at a coarse file: the
inner gates of a round (their file tests, their families and their flags), the
control the round folds and the round's two runs. Everything below it is
already at the file, so this is the last layer before the variable's loop.
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
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable {e₀ : Univ A R P dt.KIx dt.dd} (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

/-! ### One inner gate block, in the sequencer's shape -/

section IGateBlockStage

variable (b : Fin dt.ko ⊕ Fin dt.ki) (flag : dt.CtlIx)
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
    (args := dt.igateArgs PR.zero PR.one b flag hc hn hrd) (wellG := wellG)
    (setFail := setFail) (failPh := failPh) (exitPh := exitPh) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
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
-- The widths a clocked inner gate block is priced at: a walk to a named
-- register, and the sweep of the file its shape test makes.
variable (w wP : ℕ)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)

include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt
  hcompat hgap hcostR in
/-- **A passing inner gate block, entered by a dispatch**: the file test
passes, the witness chain reads the VAL block, the branch dispatches — on
the decoded tag or the default — the domain loop runs, and the conjoining
exit lands at the next checkpoint. -/
theorem ixIGateBlock_reachesIn_pos (hTest : ∀ u, Test u) (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((wideRank (F.cell gtop) + 2 + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
        wideRank (F.cell gbot)) + (1 + (1 +
        ((w + 2) * Fintype.card dt.X.Tag + 2 +
          ((2 + (w + 2) * dt.domNr (dt.dspTagOf PR.zero PR.one
              (wmBlk (ixAddr elt st.val) (Tag.arg (toLex b) : Tag R P dt.KIx)))) *
            (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1)))))
      ⟨Sum.inr (PR.stElt (emb (Sum.inl .up)) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).exitSt
            (dt.dspTagOf PR.zero PR.one
              (wmBlk (ixAddr elt st.val) (Tag.arg (toLex b) : Tag R P dt.KIx)))
            (dt.ixIGateFam F hhasP PR.one b st
              (dt.dspTagOf PR.zero PR.one
                (wmBlk (ixAddr elt st.val) (Tag.arg (toLex b) : Tag R P dt.KIx)))
              flag hc hn hrd v
              (dt.ixIGateTagFam F hhasP PR.one b st flag hc hn hrd v f
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.domNr (dt.dspTagOf PR.zero PR.one
                (wmBlk (ixAddr elt st.val)
                  (Tag.arg (toLex b) : Tag R P dt.KIx))))))
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
  -- the passing exit, into the tag-branched evaluation
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
          bitVal PR.zero PR.one
            (∃ u : I, v = F.cell u) from rfl,
        bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
      exact PR.zero_ne_one
  refine (TMData.reachesIn_of_step hexit).trans ?_
  -- the tag-branched evaluation, entered
  have hdomrules : ∀ (i : TagSite (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr)
      (ρ : TagSh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr i),
      PR.rules (rEmb (Sum.inr i) ρ) = tagRule PR.one Slot.wk Slot.reg
        (fun p => emb (Sum.inr p))
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).rdTrackT)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).MatchT)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).setTagFlag)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).TagsAre)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).rdTrackE)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).MatchE)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).setFlagE)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).initEl)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).advEl)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).exitSt)
        ((dt.igateArgs PR.zero PR.one b flag hc hn hrd).IsMaxEl)
        exitPh i ρ :=
    fun i ρ => hrules (Sum.inr i) ρ
  refine TMData.ReachesIn.trans
    (TMData.reachesIn_of_step
      (tag_back F.toIxFile hlin hvi hwkS hne_wk_mir hR hdomrules)) ?_
  exact ixIGate_reachesIn (F := F) (hhasP := hhasP) (hsepR := hsepP) (hixR := hix)
    (b := b) (st := st) (flag := flag) (hc := hc) (hn := hn) (hrd := hrd)
    (t := dt.dspTagOf PR.zero PR.one
      (wmBlk (ixAddr elt st.val) (Tag.arg (toLex b) : Tag R P dt.KIx)))
    (hinjR := hinj) (heltR := heltP) (hrules := hdomrules) (hR := hR) (hlin := hlin)
    (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (t₀ := Slot.mir) (m₀ := st.mir) (hm₀ := fun r => rfl)
    (hwkt₀ := hne_wk_mir) (hrgt₀ := hne_rg_mir) (htag := rfl) (f₀ := f)
    (w := w) (hcostT := fun _ => hcostR _ _) (hcostE := fun _ _ => hcostR _ _)

include hrules hR hlin hix htop hbot hv hvi hwkSt
  hcompat hgap in
/-- **A failing inner gate block**: some register cell is not well-shaped,
so the file test fails and the block leaves through the failing exit — for
an inner gate, the *next* checkpoint — with the fail store applied at the
marker's symbol. -/
theorem ixIGateBlock_reachesIn_neg {u : I}
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
  refine htest.tail ?_
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

end IGateBlockStage

/-! ### The concrete thread over the levels -/

section IGFs

variable (zero one : A)
variable (hhas : F.toLayout.HasName zero)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))

/-- **The file-test question of an inner gate**, semantically: every cell of
the gated block that the round's register holds is encoding-shaped. -/
noncomputable def ixIGTest (stV : TapeSt dt A R P I)
    (b : Fin dt.ko ⊕ Fin dt.ki) (u : I) : Prop :=
  dt.wellShapedIG zero one b (dt.ixBack F.toLayout zero one dt.dd0Le stV (F.cell u))

omit [Finite I] [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **A file test depends on the VAL register alone**: everything else it
reads is the tape's permanent geometry. -/
theorem ixIGTest_congr (zero one : A)
    {st st' : TapeSt dt A R P I}
    (hval : st.val = st'.val) (b : Fin dt.ko ⊕ Fin dt.ki) (u : I) :
    dt.ixIGTest F zero one st b u ↔ dt.ixIGTest F zero one st' b u := by
  refine dt.wellShapedIG_congr zero one b rfl ?_ rfl (fun _ => rfl)
  change bitVal zero one (bitAtOf F.cell st.val (F.cell u)) =
    bitVal zero one (bitAtOf F.cell st'.val (F.cell u))
  rw [hval]

open Classical in
/-- **The control thread across one round's inner gates**: each level's
machinery entered through the pack's `enterIGSt` — the first level
resetting the two flags — its conjoining exit the next level's input where
the file test passes, the fail store where it does not. -/
noncomputable def ixIGFs (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) :
    ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.nIn vi then
      if ∀ u, dt.ixIGTest F zero one stV (dt.igBlk vi ⟨n, h⟩) u then
        ((dt.varArgsOf zero one vi).argsIG ⟨n, h⟩).exitSt
          (dt.dspTagOf zero one
            (wmBlk (ixAddr elt stV.val)
              (Tag.arg (toLex (dt.igBlk vi ⟨n, h⟩)) : Tag R P dt.KIx)))
          (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, h⟩) stV
            (dt.dspTagOf zero one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ⟨n, h⟩)) :
                  Tag R P dt.KIx)))
            (dt.igFlag vi ⟨n, h⟩) dt.card_le_ntgDim dt.domN dt.domRd v
            (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, h⟩) stV
              (dt.igFlag vi ⟨n, h⟩) dt.card_le_ntgDim dt.domN dt.domRd v
              ((dt.varArgsOf zero one vi).enterIGSt ⟨n, h⟩
                (ixIGFs vi stV v f₀ n) (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup)
            (Fin.last (dt.domNr (dt.dspTagOf zero one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ⟨n, h⟩)) :
                  Tag R P dt.KIx))))))
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v)
      else
        (dt.varArgsOf zero one vi).setFailIGOf ⟨n, h⟩
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, h⟩
            (ixIGFs vi stV v f₀ n) (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v)
    else ixIGFs vi stV v f₀ n

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The inner gates are blind to the two scratch registers**: every
level's test reads the VAL register (`igTest_congr`), its dispatched tag is
that register's block value, and its two loops read their background at the
working cell. -/
theorem ixIGFs_congr_scratch {v : Univ A R P dt.KIx dt.dd → Prop}
    {stV stV' : TapeSt dt A R P I} (h : dt.ScratchEq stV stV')
    (hreg : ¬∃ u : I, v = F.cell u)
    (vi : dt.VarIx) (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n = dt.ixIGFs
      (elt := elt) F zero one hhas vi stV' v f₀ n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ixIGFs, ixIGFs]
    by_cases hn : n < dt.nIn vi
    · rw [dif_pos hn, dif_pos hn, ih]
      have htest : (∀ u, dt.ixIGTest F zero one stV (dt.igBlk vi ⟨n, hn⟩) u) =
          (∀ u, dt.ixIGTest F zero one stV' (dt.igBlk vi ⟨n, hn⟩) u) :=
        propext (forall_congr' fun u =>
          ixIGTest_congr (F := F) (zero := zero) (one := one) (hval := h.2.2.1)
            (b := dt.igBlk vi ⟨n, hn⟩) (u := u))
      rw [htest, h.2.2.1, h.ixBack hreg]
      by_cases hp : ∀ u, dt.ixIGTest F zero one stV' (dt.igBlk vi ⟨n, hn⟩) u
      · rw [if_pos hp, if_pos hp,
          ixIGateTagFam_congr_scratch (F := F) (hhas := hhas) h hreg _ _,
          ixIGateFam_congr_scratch (F := F) (hhas := hhas) h hreg _ _ _]
      · rw [if_neg hp, if_neg hp]
    · rw [dif_neg hn, dif_neg hn, ih]

/-- **What one level's gate is worth**: the file test passed, the block
value's witness one-hot at the dispatched tag, and the domain condition
there. By `DescriptiveComplexity.Draw.Data.igVerdict_iff_isEnc` this is
`IsEnc` of the block value, once the encoding layer relates the test's
marks to the true shapes. -/
noncomputable def ixIGPassP (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (ℓ : Fin (dt.nIn vi)) : Prop :=
  (∀ u, dt.ixIGTest F zero one stV (dt.igBlk vi ℓ) u) ∧
  (∀ t' : dt.X.Tag,
    wmBlk (ixAddr elt stV.val)
        (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)
        (encTagTup dt.ly zero one t') ↔
      t' = dt.dspTagOf zero one
        (wmBlk (ixAddr elt stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx))) ∧
  ExpExpansion.DomHolds (X := dt.X)
    (dt.dspTagOf zero one
        (wmBlk (ixAddr elt stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)),
      decRho dt.ly zero one
        (wmBlk (ixAddr elt stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)))

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
/-- **A round's pass depends on the VAL register alone.** Hence at a round
state (`DescriptiveComplexity.Draw.Data.roundSt`, which sets VAL and
keeps everything else) the pass is the *same proposition* at every
position of the spine — so a position's `hp` is the entry state's, and
`kindSemCast` may carry the pack it unlocks. -/
theorem ixIGPassP_congr (zero one : A) (vi : dt.VarIx)
    {st st' : TapeSt dt A R P I}
    (hval : st.val = st'.val) (ℓ : Fin (dt.nIn vi)) :
    dt.ixIGPassP (elt := elt) F zero one vi st ℓ ↔
      dt.ixIGPassP (elt := elt) F zero one vi st' ℓ := by
  refine and_congr
    (forall_congr' fun u => ixIGTest_congr (F := F) (zero := zero) (one := one) (hval := hval)
      (b := _) (u := u)) ?_
  rw [hval]

/-! ### The rides: what the round's machinery never writes -/

section Rides

variable {zero one}

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The inner fold's vector survives the inner gates**: no level's
machinery — witness chain, domain loop, conjoining exit, fail store or
entry reset — ever writes an accumulator. -/
theorem ixIGFs_apply_accC (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A)
    (jj : Fin dt.naDim) (n : ℕ) :
    dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n (dt.accC jj) = f₀ (dt.accC jj) := by
  classical
  have hSub : dt.accC jj ≠ dt.subLeafC := fun h => nomatch h
  have hSac : ∀ j : Fin dt.eDim, dt.accC jj ≠ dt.sacC j :=
    fun j h => nomatch h
  have hLvE : ∀ j : Fin dt.eDim, dt.accC jj ≠ dt.lvE j :=
    fun j h => nomatch h
  have hFlag : ∀ ℓ : Fin (dt.nIn vi), dt.accC jj ≠ dt.igFlag vi ℓ := by
    intro ℓ
    rw [igFlag]
    split <;> exact fun h => nomatch h
  have hEnter : ∀ (ℓ : Fin (dt.nIn vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A),
      (dt.varArgsOf zero one vi).enterIGSt ℓ f g (dt.accC jj) =
        f (dt.accC jj) := by
    intro ℓ f g
    change (if (ℓ : ℕ) = 0 then
        dt.setCtl zero one dt.existGateC True
          (dt.setCtl zero one dt.allGateC True f) else f) (dt.accC jj) = _
    by_cases h0 : (ℓ : ℕ) = 0
    · rw [if_pos h0,
        setCtl_of_ne (show dt.accC jj ≠ dt.existGateC from
          fun h => nomatch h),
        setCtl_of_ne (show dt.accC jj ≠ dt.allGateC from
          fun h => nomatch h)]
    · rw [if_neg h0]
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < dt.nIn vi
    · by_cases hp : ∀ u, dt.ixIGTest F zero one stV (dt.igBlk vi ⟨n, hn⟩) u
      · have hFa : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1) =
            ((dt.varArgsOf zero one vi).argsIG ⟨n, hn⟩).exitSt
              (dt.dspTagOf zero one
                (wmBlk (ixAddr elt stV.val)
                  (Tag.arg (toLex (dt.igBlk vi ⟨n, hn⟩)) :
                    Tag R P dt.KIx)))
              (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, hn⟩) stV
                (dt.dspTagOf zero one
                  (wmBlk (ixAddr elt stV.val)
                    (Tag.arg (toLex (dt.igBlk vi ⟨n, hn⟩)) :
                      Tag R P dt.KIx)))
                (dt.igFlag vi ⟨n, hn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
                (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, hn⟩) stV
                  (dt.igFlag vi ⟨n, hn⟩) dt.card_le_ntgDim dt.domN dt.domRd
                  v
                  ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hn⟩
                    (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                    (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
                  (Fin.last (Fintype.card dt.X.Tag)))
                (toLex topTup)
                (Fin.last (dt.domNr (dt.dspTagOf zero one
                  (wmBlk (ixAddr elt stV.val)
                    (Tag.arg (toLex (dt.igBlk vi ⟨n, hn⟩)) :
                      Tag R P dt.KIx))))))
              (dt.ixBack F.toLayout zero one dt.dd0Le stV v) := by
          simp only [ixIGFs]
          rw [dif_pos hn, if_pos hp]
        rw [hFa]
        set t := dt.dspTagOf zero one
          (wmBlk (ixAddr elt stV.val)
            (Tag.arg (toLex (dt.igBlk vi ⟨n, hn⟩)) : Tag R P dt.KIx))
          with ht
        change dt.igateExit zero one (dt.igFlag vi ⟨n, hn⟩) t
          dt.card_le_ntgDim (dt.domN t) (dt.domRd t)
          (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, hn⟩) stV t
            (dt.igFlag vi ⟨n, hn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
            (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, hn⟩) stV
              (dt.igFlag vi ⟨n, hn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
              ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hn⟩
                (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr t)))
          (dt.accC jj) = _
        rw [igateExit, setCtl_of_ne (hFlag ⟨n, hn⟩), setSubLeaf,
          setCtl_of_ne hSub]
        rw [ixIGateFam]
        refine Eq.trans (elemFam_apply_of (dt.accC jj) ?_ ?_ ?_ _ _ _ _) ?_
        · intro r bb fd g
          change dt.setCtl zero one
            (dt.rdfC (Fin.castLE (dt.domRd t) r)) (bb = true) fd
            (dt.accC jj) = _
          exact setCtl_of_ne
            (show dt.accC jj ≠ dt.rdfC _ from fun h => nomatch h) _ _
        · intro fd g
          change dt.gateInit zero one t fd (dt.accC jj) = _
          rw [gateInit, initSac, putSac_of_not_sac hSac, initLvE,
            putLvE_acc]
        · intro fd g
          change dt.gateAdv zero one t (dt.domN t) (dt.domRd t) fd
            (dt.accC jj) = _
          rw [gateAdv, advLvE, putLvE_acc, carrySac,
            putSac_of_not_sac hSac, setSubLeaf, setCtl_of_ne hSub]
        · rw [ixIGateTagFam, tagFam]
          refine Eq.trans (chainSt_apply_of (dt.accC jj) _ _ ?_ _ _) ?_
          · intro i bb fd
            change dt.setCtl zero one
              (dt.gateTagC dt.card_le_ntgDim
                ((Fintype.equivFin dt.X.Tag).symm i)) (bb = true) fd
              (dt.accC jj) = _
            exact setCtl_of_ne
              (show dt.accC jj ≠ dt.gateTagC _ _ from fun h => nomatch h)
              _ _
          · rw [hEnter]
            exact ih
      · have hFa : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1) =
            (dt.varArgsOf zero one vi).setFailIGOf ⟨n, hn⟩
              ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hn⟩
                (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
              (dt.ixBack F.toLayout zero one dt.dd0Le stV v) := by
          simp only [ixIGFs]
          rw [dif_pos hn, if_neg hp]
        rw [hFa]
        change dt.setCtl zero one
          (if dt.polOf vi (dt.arOf vi + n) then dt.existGateC
            else dt.allGateC) False
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) (dt.accC jj) = _
        rw [setCtl_of_ne (show dt.accC jj ≠
          (if dt.polOf vi (dt.arOf vi + n) then dt.existGateC
            else dt.allGateC) from by
          split <;> exact fun h => nomatch h), hEnter]
        exact ih
    · have hFa : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1) =
          dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n := by
        simp only [ixIGFs]
        rw [dif_neg hn]
      rw [hFa]
      exact ih

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round flag survives one atom's machinery**: no kind's exit control
writes the two VAL-round gate flags. -/
theorem ixKindExitCtl_apply_roundFlag {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (vi : dt.VarIx) (av : Fin dt.natMax) (st : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop)
    (κ : MatAtom dt.X dt.d.B (dt.nOf vi))
    (sem : dt.IxKindSem (elt := elt) zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ixKindExitCtl F zero one hhas vi av st v κ sem hk hnd hrd f q = f q := by
  classical
  have hne : q ≠ dt.avC av := by
    rcases hq with rfl | rfl <;> exact fun h => nomatch h
  have hAcc : q ≠ dt.cmpAccC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  have hDec : q ≠ dt.cmpDecC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  have hVal : q ≠ dt.cmpValC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  have hSub : q ≠ dt.subLeafC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  have hBit : q ≠ dt.bitFlagC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  have hLv : ∀ j : Fin dt.dd0, q ≠ dt.lvC j := by
    rcases hq with rfl | rfl <;> exact fun j h => nomatch h
  have hLvE : ∀ j : Fin dt.eDim, q ≠ dt.lvE j := by
    rcases hq with rfl | rfl <;> exact fun j h => nomatch h
  have hNotSac : ∀ j : Fin dt.eDim, q ≠ dt.sacC j := by
    rcases hq with rfl | rfl <;> exact fun j h => nomatch h
  have hRdf : ∀ r : Fin dt.nfDim, q ≠ dt.rdfC r := by
    rcases hq with rfl | rfl <;> exact fun r h => nomatch h
  have hTgf : ∀ a' : Fin dt.ntgDim, q ≠ dt.tgfC a' := by
    rcases hq with rfl | rfl <;> exact fun a' h => nomatch h
  have hcmpFold : ∀ (hnf : 2 ≤ dt.nfDim) (fc : dt.CtlIx → A),
      dt.cmpFold zero one hnf fc q = fc q := by
    intro hnf fc
    rw [cmpFold, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal]
  have hcmpFam : ∀ (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
      (j₁ j₂ : Fin (dt.nOf vi)) (fc : dt.CtlIx → A),
      dt.cmpFam F zero one hhas
          vi av hnf isEq j₁ j₂ st v fc (toLex topTup)
        (Fin.last 2) q = fc q := by
    intro hnf isEq j₁ j₂ fc
    rw [cmpFam]
    refine elemFam_apply_of q ?_ ?_ ?_ _ _ _ _
    · intro k bb fd g
      change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) fd q = _
      exact setCtl_of_ne
        (show q ≠ dt.cmpRdC hnf k from hRdf _) _ _
    · intro fd g
      change dt.cmpInit zero one (dt.initLvN fd) q = _
      rw [cmpInit, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal,
        initLvN, putLv_of_not_lv hLv]
    · intro fd g
      change dt.advLvN (dt.cmpFold zero one hnf fd) q = _
      rw [advLvN, putLv_of_not_lv hLv]
      exact hcmpFold hnf fd
  cases κ with
  | eq j₁ j₂ =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.eq j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one true (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd true j₁ j₂ f)
  | ord j₁ j₂ =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.ord j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one false (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam F zero one hhas vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd false j₁ j₂ f)
  | stage i ts =>
    have hstage : ∀ n : ℕ,
        dt.ixStageFAt F hhas one vi ts av st elt v f n q = f q := by
      intro n
      induction n with
      | zero =>
        change dt.initLvN f q = _
        rw [initLvN, putLv_of_not_lv hLv]
      | succ n ih =>
        by_cases h : n < dt.d.B.arity i
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              tupleIter1 (dt.stageArgs zero one vi i ts av).setBit
                (dt.stageArgs zero one vi i ts av).initLv
                (dt.stageArgs zero one vi i ts av).advLv
                (dt.lvSet { st with sav := ixMark elt v } vi (ts ⟨n, h⟩)) v
                (dt.ixStageRestF F zero one { st with sav := ixMark elt v })
                (dt.ixStageXS F hhas vi ts ⟨n, h⟩) (dt.ixStageXD F hhas ⟨n, h⟩)
                (dt.ixStageTgt F hhas vi ts { st with sav := ixMark elt v } n)
                (dt.ixStageFAt F hhas one vi ts av st elt v f n)
                (toLex topTup) := by
            simp only [ixStageFAt]
            rw [dif_pos h]
          rw [hstep]
          refine (tupleIter1_apply_of q ?_ ?_ ?_ _ _ _ _ _).trans ih
          · intro bb fd g
            change dt.setCtl zero one dt.bitFlagC (bb = true) fd q = _
            exact setCtl_of_ne hBit _ _
          · intro fd g
            change dt.initLvN fd q = _
            rw [initLvN, putLv_of_not_lv hLv]
          · intro fd g
            change dt.advLvN fd q = _
            rw [advLvN, putLv_of_not_lv hLv]
        · have hstep : dt.ixStageFAt F hhas one vi ts av st elt v f (n + 1) =
              dt.ixStageFAt F hhas one vi ts av st elt v f n := by
            simp only [ixStageFAt]
            rw [dif_neg h]
          rw [hstep]
          exact ih
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.stage i ts) sem hk hnd
        hrd f =
        dt.setCtl zero one (dt.avC av)
          ((if st.old i (ixAddr elt (dt.ixStageTgt F hhas vi ts
              { st with sav := ixMark elt v } (dt.d.B.arity i)))
            then true else false) = true)
          (dt.ixStageFAt F hhas one vi ts av st elt v f (dt.d.B.arity i)) := rfl
    rw [hK, setCtl_of_ne hne]
    exact hstage _
  | @exp k e ts =>
    have hK : dt.ixKindExitCtl F zero one hhas vi av st v (.exp e ts) sem hk hnd hrd
        f =
        dt.expExit zero one e (fun ℓ => (sem.1 ℓ).1.1)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (dt.relPk e τ').n)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd)
          av
          (dt.ixExpFam F hhas one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
              (Finset.mem_univ τ')) hnd)
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag =>
                (blkAtoms (dt.relPk e τ'').mat).length)
              (Finset.mem_univ τ')) hrd) v
            (dt.ixExpTagFam F hhas one vi ts e av st hk
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
                (Finset.mem_univ τ')) hnd)
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag =>
                  (blkAtoms (dt.relPk e τ'').mat).length)
                (Finset.mem_univ τ')) hrd)
              v f (Fin.last (k * Fintype.card dt.X.Tag)))
            (toLex topTup)
            (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) := rfl
    rw [hK, expExit, setCtl_of_ne hne, setSubLeaf, setCtl_of_ne hSub]
    refine Eq.trans (elemFam_apply_of q ?_ ?_ ?_
      (dt.ixExpECell F hhas one vi ts e (fun ℓ => (sem.1 ℓ).1.1)
        (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n)
          (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd))
      (dt.ixExpTagFam F hhas one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))
      (toLex topTup)
      (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) ?_
    · intro r bb fd g
      change dt.setCtl zero one
        (dt.rdfC (Fin.castLE
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd) r))
        (bb = true) fd q = _
      exact setCtl_of_ne (hRdf _) _ _
    · intro fd g
      change dt.expInit zero one e (fun ℓ => (sem.1 ℓ).1.1) fd q = _
      rw [expInit, initSac, putSac_of_not_sac hNotSac, initLvE,
        putLvE_of_not_lv hLvE]
    · intro fd g
      change dt.expAdv zero one e (fun ℓ => (sem.1 ℓ).1.1) _ _ fd q = _
      rw [expAdv, advLvE, putLvE_of_not_lv hLvE, carrySac,
        putSac_of_not_sac hNotSac, setSubLeaf, setCtl_of_ne hSub]
    · refine chainSt_apply_of q _ _ ?_ f
        ((Fin.last (k * Fintype.card dt.X.Tag) :
          Fin (k * Fintype.card dt.X.Tag + 1)) : ℕ)
      intro i bb fd
      change dt.setCtl zero one
        (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (bb = true) fd q = _
      exact setCtl_of_ne (hTgf _) _ _

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round flag survives the whole matrix**: what the branch checkpoint
read, the fold checkpoint still reads. -/
theorem ixMatFs_apply_roundFlag {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (vi : dt.VarIx) (st : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : ∀ b : Fin (dt.natOf vi),
      dt.IxKindSem (elt := elt) zero one vi st (dt.kindOf vi b))
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ixMatFs F zero one hhas vi st v (dt.varArgsOf zero one vi).enterAtomSt sem f₀
        n q =
      f₀ q := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < dt.natOf vi
    · have hFa : dt.ixMatFs F zero one hhas vi st v
          (dt.varArgsOf zero one vi).enterAtomSt sem f₀ (n + 1) =
          dt.ixKindExitCtl F zero one hhas vi
            (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) st v
            (dt.kindOf vi ⟨n, hn⟩) (sem ⟨n, hn⟩)
            (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, hn⟩)
            (dt.kindDepth_le_eDim vi ⟨n, hn⟩)
            (dt.kindReads_le_nfDim vi ⟨n, hn⟩)
            ((dt.varArgsOf zero one vi).enterAtomSt ⟨n, hn⟩
              (dt.ixMatFs F zero one hhas vi st v
                (dt.varArgsOf zero one vi).enterAtomSt sem f₀ n)
              (dt.ixBack F.toLayout zero one dt.dd0Le st v)) := by
        simp only [ixMatFs]
        rw [dif_pos hn]
      rw [hFa, ixKindExitCtl_apply_roundFlag (F := F) (hhas := hhas) (hq := hq)]
      exact ih
    · have hFa : dt.ixMatFs F zero one hhas vi st v
          (dt.varArgsOf zero one vi).enterAtomSt sem f₀ (n + 1) =
          dt.ixMatFs F zero one hhas vi st v
            (dt.varArgsOf zero one vi).enterAtomSt sem f₀ n := by
        simp only [ixMatFs]
        rw [dif_neg hn]
      rw [hFa]
      exact ih

/-! ### The two-flag characterization -/

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **One level's effect on a round flag**: its own polarity flag becomes
"held at entry ∧ the level's verdict"; the other polarity's rides
through. -/
theorem ctlBit_flag_ixIGFs_succ (hzo : zero ≠ one) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A)
    {n : ℕ} (hℓn : n < dt.nIn vi) :
    dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1)) q ↔
      (dt.ctlBit one ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
          (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q ∧
        (dt.igFlag vi ⟨n, hℓn⟩ = q →
          dt.ixIGPassP (elt := elt) F zero one vi stV ⟨n, hℓn⟩)) := by
  classical
  have hflagn : dt.igFlag vi ⟨n, hℓn⟩ = dt.existGateC ∨
      dt.igFlag vi ⟨n, hℓn⟩ = dt.allGateC := by
    rw [igFlag]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases hp : ∀ u, dt.ixIGTest F zero one stV (dt.igBlk vi ⟨n, hℓn⟩) u
  · have hFa : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1) =
        ((dt.varArgsOf zero one vi).argsIG ⟨n, hℓn⟩).exitSt
          (dt.dspTagOf zero one
            (wmBlk (ixAddr elt stV.val)
              (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                Tag R P dt.KIx)))
          (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV
            (dt.dspTagOf zero one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                  Tag R P dt.KIx)))
            (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
            (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV
              (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd
              v
              ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
                (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup)
            (Fin.last (dt.domNr (dt.dspTagOf zero one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                  Tag R P dt.KIx))))))
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v) := by
      simp only [ixIGFs]
      rw [dif_pos hℓn, if_pos hp]
    rw [hFa]
    by_cases hqf : dt.igFlag vi ⟨n, hℓn⟩ = q
    · subst hqf
      have hchar := ctlBit_flag_ixIGate_domHolds (dt := dt)
        (b := dt.igBlk vi ⟨n, hℓn⟩) (st := stV)
        (t := dt.dspTagOf zero one
          (wmBlk (ixAddr elt stV.val)
            (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
              Tag R P dt.KIx)))
        (flag := dt.igFlag vi ⟨n, hℓn⟩) (hc := dt.card_le_ntgDim)
        (hn := dt.domN) (hrd := dt.domRd) (vAdr := v) (F := F) (hhas := hhas)
        (hinj := hinj) (helt := helt) (hflag := hflagn) (hzo := hzo)
        (f₀ := (dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
          (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
      refine Iff.trans hchar ?_
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, fun _ => ⟨hp, h2, h3⟩⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨-, h2', h3'⟩ := h2 rfl
        exact ⟨h1, h2', h3'⟩
    · have hride : dt.ctlBit one
          (((dt.varArgsOf zero one vi).argsIG ⟨n, hℓn⟩).exitSt
            (dt.dspTagOf zero one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                  Tag R P dt.KIx)))
            (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV
              (dt.dspTagOf zero one
                (wmBlk (ixAddr elt stV.val)
                  (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                    Tag R P dt.KIx)))
              (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
              (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV
                (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd
                v
                ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
                  (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                  (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.domNr (dt.dspTagOf zero one
                (wmBlk (ixAddr elt stV.val)
                  (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) :
                    Tag R P dt.KIx))))))
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q ↔
          dt.ctlBit one ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q := by
        set t := dt.dspTagOf zero one
          (wmBlk (ixAddr elt stV.val)
            (Tag.arg (toLex (dt.igBlk vi ⟨n, hℓn⟩)) : Tag R P dt.KIx))
          with ht
        change dt.ctlBit one
          (dt.igateExit zero one (dt.igFlag vi ⟨n, hℓn⟩) t
            dt.card_le_ntgDim (dt.domN t) (dt.domRd t)
            (dt.ixIGateFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV t
              (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd v
              (dt.ixIGateTagFam F hhas one (dt.igBlk vi ⟨n, hℓn⟩) stV
                (dt.igFlag vi ⟨n, hℓn⟩) dt.card_le_ntgDim dt.domN dt.domRd
                v
                ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
                  (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
                  (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr t)))) q ↔ _
        rw [igateExit]
        refine Iff.trans (ctlBit_setCtl_of_ne
          (show q ≠ dt.igFlag vi ⟨n, hℓn⟩ from
            fun h => hqf h.symm) _ _) ?_
        rw [setSubLeaf]
        refine Iff.trans (ctlBit_setCtl_of_ne
          (show q ≠ dt.subLeafC from by
            rcases hq with rfl | rfl <;>
              exact fun h => by
                injection h with h'
                exact absurd h' (by decide)) _ _) ?_
        exact ctlBit_roundFlag_ixIGateFam (dt := dt) (b := dt.igBlk vi ⟨n, hℓn⟩)
          (st := stV) (t := t) (flag := dt.igFlag vi ⟨n, hℓn⟩)
          (hc := dt.card_le_ntgDim) (hn := dt.domN) (hrd := dt.domRd)
          (vAdr := v) (F := F) (hhas := hhas) (hq := hq)
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
          (toLex topTup) (Fin.last (dt.domNr t))
      refine Iff.trans hride ?_
      constructor
      · intro h
        exact ⟨h, fun hc => absurd hc hqf⟩
      · exact And.left
  · have hFa : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (n + 1) =
        (dt.varArgsOf zero one vi).setFailIGOf ⟨n, hℓn⟩
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v) := by
      simp only [ixIGFs]
      rw [dif_pos hℓn, if_neg hp]
    rw [hFa]
    have hchg : dt.ctlBit one
        ((dt.varArgsOf zero one vi).setFailIGOf ⟨n, hℓn⟩
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v))
          (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q ↔
        dt.ctlBit one
          (dt.setCtl zero one (dt.igFlag vi ⟨n, hℓn⟩) False
            ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
              (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
              (dt.ixBack F.toLayout zero one dt.dd0Le stV v))) q := Iff.rfl
    rw [hchg]
    by_cases hqf : dt.igFlag vi ⟨n, hℓn⟩ = q
    · subst hqf
      refine Iff.trans (ctlBit_setCtl_self hzo _ _ _) ?_
      constructor
      · exact fun h => h.elim
      · rintro ⟨-, h2⟩
        exact absurd (h2 rfl).1 hp
    · refine Iff.trans (ctlBit_setCtl_of_ne
        (show q ≠ dt.igFlag vi ⟨n, hℓn⟩ from fun h => hqf h.symm) _ _) ?_
      constructor
      · intro h
        exact ⟨h, fun hc => absurd hc hqf⟩
      · exact And.left

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
omit [Finite I] in
include hinj helt in
/-- **The two-flag characterization**: after the whole inner-gates thread,
a round flag holds exactly when every quantified level of its polarity
passes its gate — the file test, the one-hot witness at the dispatched
tag, and the domain condition there. -/
theorem ctlBit_flag_ixIGFs (hzo : zero ≠ one) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A)
    {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ dt.nIn vi) :
    dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n) q ↔
      ∀ ℓ : Fin (dt.nIn vi), (ℓ : ℕ) < n → dt.igFlag vi ℓ = q →
        dt.ixIGPassP (elt := elt) F zero one vi stV ℓ := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
    have hℓn : n < dt.nIn vi := hn
    have hsucc := ctlBit_flag_ixIGFs_succ (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
      (hzo := hzo) (hq := hq) (vi := vi) (stV := stV) (v := v) (f₀ := f₀) (dt := dt)
      (n := n) hℓn
    have hsplit : (∀ ℓ : Fin (dt.nIn vi), (ℓ : ℕ) < n + 1 →
        dt.igFlag vi ℓ = q → dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) ↔
        ((∀ ℓ : Fin (dt.nIn vi), (ℓ : ℕ) < n →
          dt.igFlag vi ℓ = q → dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) ∧
          (dt.igFlag vi ⟨n, hℓn⟩ = q →
            dt.ixIGPassP (elt := elt) F zero one vi stV ⟨n, hℓn⟩)) := by
      constructor
      · intro h
        exact ⟨fun ℓ hℓ => h ℓ (by omega),
          h ⟨n, hℓn⟩ (Nat.lt_succ_self n)⟩
      · rintro ⟨hlt, hn'⟩ ℓ hℓ hfl
        by_cases hcase : (ℓ : ℕ) < n
        · exact hlt ℓ hcase hfl
        · have hval : (ℓ : ℕ) = n := by omega
          have hℓeq : ℓ = ⟨n, hℓn⟩ := Fin.ext hval
          rw [hℓeq] at hfl ⊢
          exact hn' hfl
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hENT : dt.ctlBit one
          ((dt.varArgsOf zero one vi).enterIGSt ⟨0, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ 0)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q := by
        change dt.ctlBit one
          (dt.setCtl zero one dt.existGateC True
            (dt.setCtl zero one dt.allGateC True
              (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ 0))) q
        rcases hq with rfl | rfl
        · exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
        · refine (ctlBit_setCtl_of_ne (show dt.allGateC ≠ dt.existGateC
              from fun h => by
                injection h with h'
                exact absurd h' (by decide)) _ _).mpr ?_
          exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
      refine hsucc.trans (Iff.trans ?_ hsplit.symm)
      constructor
      · rintro ⟨-, h2⟩
        exact ⟨fun ℓ hℓ => absurd hℓ (by omega), h2⟩
      · rintro ⟨-, h2⟩
        exact ⟨hENT, h2⟩
    · have hENT : dt.ctlBit one
          ((dt.varArgsOf zero one vi).enterIGSt ⟨n, hℓn⟩
            (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n)
            (dt.ixBack F.toLayout zero one dt.dd0Le stV v)) q ↔
          dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n) q := by
        change dt.ctlBit one
          (if n = 0 then
            dt.setCtl zero one dt.existGateC True
              (dt.setCtl zero one dt.allGateC True
                (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n))
          else dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ n) q ↔ _
        rw [if_neg (by omega)]
      refine hsucc.trans (Iff.trans ?_ hsplit.symm)
      constructor
      · rintro ⟨h1', h2⟩
        exact ⟨(ih hpos (by omega)).mp (hENT.mp h1'), h2⟩
      · rintro ⟨h1', h2⟩
        exact ⟨hENT.mpr ((ih hpos (by omega)).mpr h1'), h2⟩

omit [Fintype dt.SlotIx] [Finite I] [Finite R] [Finite P] in
include hinj helt in
/-- **The branch's guard delivers the pass**: with both flags set after
the inner gates' thread, every quantified level passed its gate — what
unlocks the round's semantic pack. -/
theorem ixRoundPass_of_flags (hzo : zero ≠ one) (vi : dt.VarIx)
    (stV : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)
    (f₀ : dt.CtlIx → A)
    (h : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.allGateC) :
    ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ := by
  intro ℓ
  have h1 : 1 ≤ dt.nIn vi := ℓ.pos
  have hflagn : dt.igFlag vi ℓ = dt.existGateC ∨
      dt.igFlag vi ℓ = dt.allGateC := by
    rw [igFlag]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hflagn with hf | hf
  · exact (ctlBit_flag_ixIGFs (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
      (hzo := hzo) (hq := Or.inl rfl) (vi := vi) (stV := stV) (v := v) (f₀ := f₀)
      (dt := dt) h1
      (le_refl _)).mp h.1 ℓ ℓ.isLt hf
  · exact (ctlBit_flag_ixIGFs (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
      (hzo := hzo) (hq := Or.inr rfl) (vi := vi) (stV := stV) (v := v) (f₀ := f₀)
      (dt := dt) h1
      (le_refl _)).mp h.2 ℓ ℓ.isLt hf

open Classical in
/-- **The control one round leaves at the fold checkpoint**: the matrix
thread applied to the inner gates' output at a passing round — both flags
set, the round's **conditional semantic pack** unlocked by
`DescriptiveComplexity.Draw.Data.roundPass_of_flags` — and the gates'
output alone at a skipping one. The pack must be conditional: a garbage
round holds no encodings to build one from, and its matrix never runs. -/
noncomputable def ixRoundCtl (hzo : zero ≠ one) (vi : dt.VarIx)
    (stV : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi stV (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  if h : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.allGateC then
    dt.ixMatFs F zero one hhas vi stV v (dt.varArgsOf zero one vi).enterAtomSt
      (sem (ixRoundPass_of_flags (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
        (hzo := hzo) (vi := vi) (stV := stV) (v := v) (f₀ := f₀) (h := h)))
      (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)) (dt.natOf vi)
  else dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)

open Classical in
variable (zero one) in
/-- **The state one round leaves**: the matrix runs on the passing branch
only, so the round's exit state is the matrix's threaded state there and
the entry state at a skipping round. -/
noncomputable def ixRoundEndSt (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) :
    TapeSt dt A R P I :=
  if dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.allGateC then
    dt.ixMatSt (elt := elt) vi stV v (dt.natOf vi)
  else stV

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round's exit state differs from its entry in SAV and TARGET
alone** — the same fact as
`DescriptiveComplexity.Draw.Data.matSt_fields`, through the branch. -/
theorem ixRoundEndSt_fields (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) :
    (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).wk = stV.wk ∧
      (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).mir = stV.mir ∧
      (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).bot = stV.bot ∧
      (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).val = stV.val ∧
      (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).old = stV.old := by
  classical
  rw [ixRoundEndSt]
  split
  · exact ixMatSt_fields (elt := elt) (v := v) (st := stV) (dt.natOf vi)
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round's exit state is its entry state with the two scratch
registers rewritten** — the sharpening of
`DescriptiveComplexity.Draw.Data.roundEndSt_fields`, and what lets the
VAL loop thread those two registers rather than the whole state. -/
theorem ixRoundEndSt_eq (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) :
    dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀ =
      { stV with
        sav := (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).sav
        tgt := (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀).tgt } := by
  classical
  rw [ixRoundEndSt]
  split
  · exact ixMatSt_eq (elt := elt) (v := v) (st := stV) (dt.natOf vi)
  · rfl

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round's exit state differs from its entry state in the two scratch
registers alone** — `roundEndSt_eq` in the form the congruences take. -/
theorem ixScratchEq_roundEndSt (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A) :
    dt.ScratchEq (dt.ixRoundEndSt (elt := elt) F zero one hhas vi stV v f₀) stV := by
  rw [ixRoundEndSt_eq (F := F) (hhas := hhas) (elt := elt) (vi := vi) (stV := stV)
    (v := v) (f₀ := f₀)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Classical in
/-- **The control one round leaves, threaded**: as
`DescriptiveComplexity.Draw.Data.roundCtl`, with the matrix's thread
taken at the states its atoms run at. -/
noncomputable def ixRoundCtlT (hzo : zero ≠ one) (vi : dt.VarIx)
    (stV : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi),
        dt.IxKindSem (elt := elt) zero one vi (dt.ixMatSt (elt := elt) vi stV v (a : ℕ))
          (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  if h : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.allGateC then
    dt.ixMatFsT F zero one hhas vi stV v (dt.varArgsOf zero one vi).enterAtomSt
      (sem (ixRoundPass_of_flags (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
        (hzo := hzo) (vi := vi) (stV := stV) (v := v) (f₀ := f₀) (h := h)))
      (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)) (dt.natOf vi)
  else dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round is blind to the two scratch registers**: its gates by
`igFs_congr_scratch`, its matrix by `matFs_congr_scratch`. -/
theorem ixRoundCtl_congr_scratch (hzo : zero ≠ one)
    {v : Univ A R P dt.KIx dt.dd → Prop} {stV stV' : TapeSt dt A R P I}
    (h : dt.ScratchEq stV stV')
    (hreg : ¬∃ u : I, v = F.cell u) (vi : dt.VarIx)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi stV (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
      (vi := vi) (stV := stV)
        (v := v) (sem := sem) (f₀ := f₀) =
      dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
        (vi := vi)
        (stV := stV') (v := v) (f₀ := f₀) (sem :=
        fun hp a => dt.ixKindSemCast zero one vi h.2.1 h.2.2.1
          (dt.kindOf vi a)
          (sem (fun ℓ =>
            (ixIGPassP_congr (F := F) (elt := elt) (zero := zero) (one := one) (vi := vi)
              (hval := h.2.2.1) (ℓ := ℓ)).mpr (hp ℓ))
            a)) := by
  classical
  have hig : dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi) =
      dt.ixIGFs (elt := elt) F zero one hhas vi stV' v f₀ (dt.nIn vi) :=
    ixIGFs_congr_scratch (F := F) (hhas := hhas) (elt := elt) (zero := zero)
      (one := one) (h := h) (hreg := hreg) (vi := vi) (f₀ := f₀) (n := dt.nIn vi)
  by_cases hc : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)) dt.allGateC
  · simp only [ixRoundCtl, dif_pos hc, dif_pos (hig ▸ hc)]
    refine Eq.trans (ixMatFs_congr_scratch (F := F) (hhas := hhas) (h := h)
      (hreg := hreg) _ _ _ _) ?_
    exact congrArg (fun fc : dt.CtlIx → A =>
      dt.ixMatFs F zero one hhas vi stV' v (dt.varArgsOf zero one vi).enterAtomSt
        (fun a => dt.ixKindSemCast zero one vi h.2.1 h.2.2.1 (dt.kindOf vi a)
          (sem (ixRoundPass_of_flags (F := F) (hhas := hhas) (hinj := hinj)
            (helt := helt) (hzo := hzo) (vi := vi) (stV := stV) (v := v)
            (f₀ := f₀) (h := hc)) a)) fc
        (dt.natOf vi)) hig
  · simp only [ixRoundCtl, dif_neg hc, dif_neg (hig ▸ hc)]
    rw [hig]

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The threaded round is the unthreaded one**: the gates decide the
branch off the same registers, and on the passing branch the matrix
threads SAV and TARGET alone (`matFsT_eq_matFs`). With this the control the
*run* produces is the control the semantic capstone
(`DescriptiveComplexity.Draw.Data.accVerdict_leafP`) is stated at. -/
theorem ixRoundCtlT_eq_ixRoundCtl (hzo : zero ≠ one)
    {v : Univ A R P dt.KIx dt.dd → Prop}
    (hreg : ¬∃ u : I, v = F.cell u) (vi : dt.VarIx)
    (stV : TapeSt dt A R P I)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi),
        dt.IxKindSem (elt := elt) zero one vi (dt.ixMatSt (elt := elt) vi stV v (a : ℕ))
          (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    dt.ixRoundCtlT (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
      (vi := vi) (stV := stV)
        (v := v) (sem := sem) (f₀ := f₀) =
      dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
        (vi := vi) (stV := stV)
        (v := v) (f₀ := f₀)
        (sem := fun hp a => dt.ixKindSemCast zero one vi
          (ixScratchEq_matSt (elt := elt) (a : ℕ)).2.1
          (ixScratchEq_matSt (elt := elt) (a : ℕ)).2.2.1 (dt.kindOf vi a)
          (sem hp a)) := by
  classical
  by_cases hc : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
        dt.existGateC ∧
      dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)) dt.allGateC
  · simp only [ixRoundCtlT, ixRoundCtl, dif_pos hc]
    exact ixMatFsT_eq_ixMatFs (F := F) (hhas := hhas) (hreg := hreg) _ _ _ _
  · simp only [ixRoundCtlT, ixRoundCtl, dif_neg hc]

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The accumulators survive one whole round.** -/
theorem ixRoundCtl_apply_accC {hzo : zero ≠ one} (vi : dt.VarIx)
    (stV : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi stV (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) (jj : Fin dt.naDim) :
    dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
      (vi := vi) (stV := stV)
        (v := v) (sem := sem) (f₀ := f₀) (dt.accC jj) =
      f₀ (dt.accC jj) := by
  rw [ixRoundCtl]
  split
  · exact (ixMatFs_apply_accC (F := F) (hhas := hhas) (elt := elt) (one := one) _
      (fun _ _ _ _ => rfl) _ _ jj _).trans
      (ixIGFs_apply_accC (F := F) (hhas := hhas) (elt := elt) (one := one) (vi := vi)
        (stV := stV) (v := v) (f₀ := f₀) (jj := jj) (n := dt.nIn vi))
  · exact ixIGFs_apply_accC (F := F) (hhas := hhas) (elt := elt) (one := one)
      (vi := vi) (stV := stV) (v := v) (f₀ := f₀) (jj := jj) (n := dt.nIn vi)

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A round's exit reads the two flags off the inner gates' thread**:
the matrix — run or skipped — never writes them. -/
theorem ixRoundCtl_apply_roundFlag {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC) {hzo : zero ≠ one}
    (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi stV (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
      (vi := vi) (stV := stV)
        (v := v) sem f₀ q =
      dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi) q := by
  rw [ixRoundCtl]
  split
  · exact ixMatFs_apply_roundFlag (dt := dt) (F := F) (hhas := hhas) (hq := hq) vi stV v _ _ _
  · rfl

omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A passing round's exit is the matrix thread**, at any proof of the
pass — the branch's own derivation is proof-irrelevant. -/
theorem ixRoundCtl_of_flags {hzo : zero ≠ one} (vi : dt.VarIx)
    (stV : TapeSt dt A R P I) (v : Univ A R P dt.KIx dt.dd → Prop)
    (sem : (∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi), dt.IxKindSem (elt := elt) zero one vi stV (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (hEx : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
      dt.existGateC)
    (hAl : dt.ctlBit one (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi))
      dt.allGateC) :
    dt.ixRoundCtl (elt := elt) F (hhas := hhas) (hinj := hinj) (helt := helt) (hzo := hzo)
      (vi := vi) (stV := stV)
        (v := v) sem f₀ =
      dt.ixMatFs F zero one hhas vi stV v (dt.varArgsOf zero one vi).enterAtomSt
        (sem hp)
        (dt.ixIGFs (elt := elt) F zero one hhas vi stV v f₀ (dt.nIn vi)) (dt.natOf vi) := by
  rw [ixRoundCtl, dif_pos ⟨hEx, hAl⟩]

end Rides

end IGFs

/-! ### The inner gates' run -/

section IGsRun

variable (vi : dt.VarIx) {stV : TapeSt dt A R P I}
variable {emb : dt.IGatesPh vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.IGatesSite vi, dt.IGatesSh vi i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : dt.IGatesSite vi) (ρ : dt.IGatesSh vi i),
  PR.rules (rEmb i ρ) = dt.igatesRule (one := PR.one) (v := vi) (emb := emb)
    (argsG := (dt.varArgsOf PR.zero PR.one vi).argsIG)
    (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellIGOf)
    (setFailOf := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf)
    (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterIGSt)
    (exitPh := exitPh) i ρ)
variable {wG : ℕ} (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
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
variable (hwkSt : stV.wk = fun r => r = v)
-- The widths a clocked level is priced at: a walk to a named register, and
-- the sweep of the file each level's shape test makes.
variable (w wP : ℕ)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)

include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt hgap
  hwP hcostR in
/-- **The inner gates' run, on a clock**: as
`DescriptiveComplexity.Draw.Data.ixIGs_run` with the levels counted – one
level's width, its dispatch and the step back per level, and one step to
leave. -/
theorem ixIGs_reachesIn (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((dt.ixGateCost A w wP + 2) * dt.nIn vi + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (dt.nIn vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hchain := seq_reachesIn F.toIxFile hrules hR hlin hix hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
    (mOf := fun _ => stV.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (j : ℕ))
    (dt.ixGateCost A w wP) ?_
  · exact hchain
  · intro ℓ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ p))
            (args := dt.igateArgs PR.zero PR.one (dt.igBlk vi ℓ)
              (dt.igFlag vi ℓ) dt.card_le_ntgDim dt.domN dt.domRd)
            (wellG := (dt.varArgsOf PR.zero PR.one vi).wellIGOf ℓ)
            (setFail := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf ℓ)
            (failPh := emb (.chk ℓ.succ)) (exitPh := emb (.chk ℓ.succ))
            i ρ :=
      fun i ρ => hrules (.sub ℓ i) ρ
    have hcompat : ∀ u : I,
        (dt.varArgsOf PR.zero PR.one vi).wellIGOf ℓ
          (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
            stV.mir (F.cell u)) ↔
          dt.ixIGTest F PR.zero PR.one stV (dt.igBlk vi ℓ) u := by
      intro u
      rw [passTracks_of_back (t := Slot.mir)
        (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) (m := stV.mir)
        F.toIxFile (fun r => rfl) (F.cell u)]
      exact Iff.rfl
    by_cases hp : ∀ u, dt.ixIGTest F PR.zero PR.one stV (dt.igBlk vi ℓ) u
    · have hFa : dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ ((ℓ : ℕ) + 1) =
          ((dt.varArgsOf PR.zero PR.one vi).argsIG ℓ).exitSt
            (dt.dspTagOf PR.zero PR.one
              (wmBlk (ixAddr elt stV.val)
                (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)))
            (dt.ixIGateFam F hhasP PR.one (dt.igBlk vi ℓ) stV
              (dt.dspTagOf PR.zero PR.one
                (wmBlk (ixAddr elt stV.val)
                  (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)))
              (dt.igFlag vi ℓ) dt.card_le_ntgDim dt.domN dt.domRd v
              (dt.ixIGateTagFam F hhasP PR.one (dt.igBlk vi ℓ) stV
                (dt.igFlag vi ℓ) dt.card_le_ntgDim dt.domN dt.domRd v
                ((dt.varArgsOf PR.zero PR.one vi).enterIGSt ℓ
                  (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (ℓ : ℕ))
                  (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v))
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.domNr (dt.dspTagOf PR.zero PR.one
                (wmBlk (ixAddr elt stV.val)
                  (Tag.arg (toLex (dt.igBlk vi ℓ)) :
                    Tag R P dt.KIx))))))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v) := by
        simp only [ixIGFs]
        rw [dif_pos ℓ.isLt, if_pos hp]
      rw [hFa]
      have hrdt := dt.domRd (dt.dspTagOf PR.zero PR.one
        (wmBlk (ixAddr elt stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)))
      have hct := dt.card_le_ntgDim
      have hwPt := hwP
      refine TMData.ReachesIn.mono ?_
        (ixIGateBlock_reachesIn_pos (F := F) (hhasP := hhasP)
        (hsepP := hsepP)
        (hix := hix) (hinj := hinj) (heltP := heltP) (b := dt.igBlk vi ℓ)
        (flag := dt.igFlag vi ℓ) (hc := dt.card_le_ntgDim) (hn := dt.domN)
        (hrd := dt.domRd) (wellG := (dt.varArgsOf PR.zero PR.one vi).wellIGOf ℓ)
        (setFail := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf ℓ)
        (hrules := hrules') (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
        (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap) (w := w)
        (hcostR := hcostR)
        (Test := dt.ixIGTest F PR.zero PR.one stV (dt.igBlk vi ℓ))
        (hcompat := hcompat) (hTest := hp)
        (f := (dt.varArgsOf PR.zero PR.one vi).enterIGSt ℓ
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (ℓ : ℕ))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v)))
      simp only [ixGateCost]
      gcongr
    · obtain ⟨u₀, hu₀⟩ := not_forall.mp hp
      have hFa : dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ ((ℓ : ℕ) + 1) =
          (dt.varArgsOf PR.zero PR.one vi).setFailIGOf ℓ
            ((dt.varArgsOf PR.zero PR.one vi).enterIGSt ℓ
              (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (ℓ : ℕ))
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v) := by
        simp only [ixIGFs]
        rw [dif_pos ℓ.isLt, if_neg hp]
      rw [hFa]
      have hwPt := hwP
      refine TMData.ReachesIn.mono ?_
        (ixIGateBlock_reachesIn_neg (F := F) (hix := hix)
        (b := dt.igBlk vi ℓ) (flag := dt.igFlag vi ℓ) (hc := dt.card_le_ntgDim)
        (hn := dt.domN) (hrd := dt.domRd)
        (wellG := (dt.varArgsOf PR.zero PR.one vi).wellIGOf ℓ)
        (setFail := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf ℓ)
        (hrules := hrules') (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
        (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap)
        (Test := dt.ixIGTest F PR.zero PR.one stV (dt.igBlk vi ℓ))
        (hcompat := hcompat) (hTest := hu₀)
        (f := (dt.varArgsOf PR.zero PR.one vi).enterIGSt ℓ
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (ℓ : ℕ))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v)))
      simp only [ixGateCost]
      omega

include hrules hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hwkSt hgap
  hwP hcostR in
/-- **The inner gates' run**: from the checkpoint before the first level at
the marker, through every level — the file test, and either the dispatch,
domain loop and conjoining exit, or the continuing fail — to the round's
branch checkpoint one cell to the marker's right, the two flags spelled by
the thread. -/
theorem ixIGs_run (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f₀ (dt.nIn vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ :=
  (ixIGs_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
    (hinj := hinj) (heltP := heltP) (hrules := hrules) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (hgap := hgap) (hwP := hwP) (hcostR := hcostR) (f₀ := f₀)).reflTransGen

end IGsRun

/-! ### The whole round, at the program's own rules -/

/-- **What one round of the VAL loop is charged**: the walk-back, the inner
gates, the walk-back at the branch checkpoint, the branching dispatch and its
walk-back, the matrix, and the walk-back at the fold checkpoint. The skipping
branch is shorter and is charged the same. -/
noncomputable def ixRoundCost (dt : Data L) (A : Type) (vi : dt.VarIx)
    (w wP wR wK : ℕ) : ℕ :=
  1 + ((dt.ixGateCost A w wP + 2) * dt.nIn vi + 1) + 1 + 1 + 1 +
    ((dt.ixMatCost A vi w wP wR wK + 2) * dt.natOf vi + 1) + 1

section RoundRun

variable (vi : dt.VarIx)
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {emb : dt.VarPhF vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.VarSiteF vi, dt.VarShF vi i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : dt.VarSiteF vi) (ρ : dt.VarShF vi i),
  PR.rules (rEmb i ρ) = dt.varRuleF PR.zero PR.one vi
    (dt.varArgsOf PR.zero PR.one vi) emb exitPh i ρ)
variable {wG : ℕ} (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom inside the round's matrix is priced at.
variable (w wP wR wK : ℕ)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
-- The reset and the seek are charged against the working area, not the tape:
-- both run at the marker or at the built TARGET, which lie below the file.
variable (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe T (F.cell gbot) →
  wideRank T *
      (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) +
        (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
          wideRank (F.cell gbot) + 4)) + 1 +
    (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
      wideRank (F.cell gbot)) ≤ wK)
-- Every named register of the file is within `w` of the marker: the width a
-- walk to a cell is charged, uniform over the blocks and the tuples.
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)

include hrules hR hlin hix hsepP hhasP hinj heltP hgap hord htop hbot hwork hv hvi
  he₀ hmono hup hvh hxdUse hwP hwR hwK hcostR in
/-- **One round of the VAL loop, run**: from the dispatch's landing one
cell right of the marker at the inner gates' first checkpoint, the
walk-back, every quantified level's gate — pass or fail, the fail
continuing — the branch checkpoint on the two flags, the matrix pass on
the passing branch, and the walk-back at the fold checkpoint. No semantic
hypothesis: the levels' outcomes and the branch are decided classically,
so the round runs at **every** VAL content the loop enumerates. -/
theorem ixRound_reachesIn (stV : TapeSt dt A R P I)
    (hwkV : stV.wk = fun r => r = v) (hmirV : stV.mir = ixMark elt v)
    (hbotV : stV.bot = fun r => r = (fun _ => False))
    (hsavV : stV.sav = ixMark elt v) (htgtV : stV.tgt = ixMark elt v)
    (sem : (∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi),
        dt.IxKindSem (elt := elt) PR.zero PR.one vi stV (dt.kindOf vi a))
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixRoundCost A vi w wP wR wK)
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .mchk1)
          (dt.ixRoundCtl (elt := elt) F (hhas := hhasP) (hinj := hinj) (helt := heltP)
          (hzo := PR.zero_ne_one) (vi := vi) (stV := stV)
        (v := v) sem f)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkV]
  have hwkv' : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  have hregv : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v Slot.reg ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_rg_val,
      show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v Slot.reg =
        bitVal PR.zero PR.one
          (∃ u : I, v = F.cell u) from rfl,
      bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
    exact PR.zero_ne_one
  have hwkv : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v Slot.wk = PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS]
    exact bitVal_pos rfl
  -- the walk-back into the inner gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.matrix (.ig (.chk 0))) .stay
    exact ⟨rEmb (.matrix (.ig (.chk 0))) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  -- the inner gates
  have higrules : ∀ (i : dt.IGatesSite vi) (ρ : dt.IGatesSh vi i),
      PR.rules (rEmb (.matrix (.ig i)) ρ) =
        dt.igatesRule (one := PR.one) (v := vi)
          (emb := fun p => emb (.matrixP (.igP p)))
          (argsG := (dt.varArgsOf PR.zero PR.one vi).argsIG)
          (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellIGOf)
          (setFailOf := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf)
          (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterIGSt)
          (exitPh := emb (.matrixP .rchk)) i ρ :=
    fun i ρ => hrules (.matrix (.ig i)) ρ
  have higs := ixIGs_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
      (hinj := hinj) (heltP := heltP) (hgap := hgap) (vi := vi)
      (stV := stV) (hrules := higrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkV) (w := w) (wP := wP)
      (hwP := hwP) (hcostR := hcostR) (f₀ := f)
  -- the walk-back at the branch checkpoint
  have hback2 : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.matrix .rchk) .stay
    exact ⟨rEmb (.matrix .rchk) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  have hpre := ((TMData.reachesIn_of_step hback).trans higs).tail hback2
  -- the branch
  rw [ixRoundCtl]
  by_cases hbr : dt.ctlBit PR.one
      (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi)) dt.existGateC ∧
    dt.ctlBit PR.one
      (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi)) dt.allGateC
  · rw [dif_pos hbr]
    -- the passing dispatch into the matrix
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix .rchk) .dspA
      refine ⟨rEmb (.matrix .rchk) .dspA, ?_, by rw [h]; rfl,
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        by rw [h]; trivial⟩
      rw [h]
      exact ⟨⟨hwkv, hregv⟩, hbr.1, hbr.2⟩
    -- the walk-back into the matrix's first checkpoint
    have hback3 : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix (.mat (.chk 0))) .stay
      exact ⟨rEmb (.matrix (.mat (.chk 0))) .stay, by rw [h]; exact hwkv',
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩
    -- the matrix
    have hmrules : ∀ (i : dt.MatrixSite vi) (ρ : dt.MatrixSh vi i),
        PR.rules (rEmb (.matrix (.mat i)) ρ) = dt.matrixRule PR.zero PR.one
          vi (emb := fun p => emb (.matrixP (.matP p)))
          (fun a => dt.atomArgs PR.zero PR.one vi a)
          ((dt.varArgsOf PR.zero PR.one vi).enterAtomSt) (emb .mchk1) i ρ :=
      fun i ρ => hrules (.matrix (.mat i)) ρ
    have hmat := ixMatrix_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
        (hix := hix)
        (hinj := hinj) (heltP := heltP) (hord := hord) (hR := hR) (hlin := hlin)
        (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork) (hv := hv)
        (hvi := hvi) (hwkSt := hwkV) (hmirSt := hmirV) (hbotSt := hbotV)
        (hsav := hsavV) (htgt := htgtV) (hmono := hmono) (hup := hup) (hvh := hvh)
        (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
        (hcostR := hcostR) (vi := vi) (st := stV)
        (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterAtomSt) (hrules := hmrules)
        (wA := dt.ixMatCost A vi w wP wR wK)
        (hwA := fun a => Finset.le_sup (f := fun a' : Fin (dt.natOf vi) =>
          dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a')) (Finset.mem_univ a))
        (sem := sem (ixRoundPass_of_flags (F := F) (hhas := hhasP) (hinj := hinj)
          (helt := heltP) (hzo := PR.zero_ne_one) (vi := vi) (stV := stV) (v := v)
          (f₀ := f) (h := hbr)))
        (f₀ := dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f
          (dt.nIn vi))
    -- the walk-back at the fold checkpoint
    refine TMData.ReachesIn.mono ?_
      ((((hpre.tail hdsp).tail hback3).trans hmat).tail ?_)
    · simp only [ixRoundCost]
      omega
    · refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules .mchk1 .stay
      exact ⟨rEmb .mchk1 .stay, by rw [h]; exact hwkv',
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩
  · rw [dif_neg hbr]
    -- the skipping dispatch, straight to the fold checkpoint
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb .mchk1)
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix .rchk) .dspB
      refine ⟨rEmb (.matrix .rchk) .dspB, ?_, by rw [h]; rfl,
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        by rw [h]; trivial⟩
      rw [h]
      exact ⟨⟨hwkv, hregv⟩, fun hc => hbr ⟨hc.1, hc.2⟩⟩
    -- the walk-back at the fold checkpoint
    refine TMData.ReachesIn.mono ?_ ((hpre.tail hdsp).tail ?_)
    · simp only [ixRoundCost]
      omega
    · refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules .mchk1 .stay
      exact ⟨rEmb .mchk1 .stay, by rw [h]; exact hwkv',
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩

include hrules hR hlin hix hsepP hhasP hinj heltP hgap hord htop hbot hwork hv hvi
  he₀ hmono hup hvh hxdUse hwP hwR hwK hcostR in
/-- **One round of the VAL loop, run — threaded**: as
`DescriptiveComplexity.Draw.Data.round_run` with no boundary discipline
assumed, so it applies at every address of the outer sweep. The tape ends
in `DescriptiveComplexity.Draw.Data.roundEndSt`, which is the entry state
unless the round's matrix ran and contained a stage atom. -/
theorem ixRound_run_thread_reachesIn (stV : TapeSt dt A R P I)
    (hwkV : stV.wk = fun r => r = v) (hmirV : stV.mir = ixMark elt v)
    (hbotV : stV.bot = fun r => r = (fun _ => False))
    (sem : (∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ) →
      ∀ a : Fin (dt.natOf vi),
        dt.IxKindSem (elt := elt) PR.zero PR.one vi (dt.ixMatSt (elt := elt) vi stV v (a : ℕ))
          (dt.kindOf vi a))
    (f : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixRoundCost A vi w wP wR wK)
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .mchk1)
          (dt.ixRoundCtlT (elt := elt) F (hhas := hhasP) (hinj := hinj) (helt := heltP)
          (hzo := PR.zero_ne_one) (vi := vi) (stV := stV)
        (v := v) sem f)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi stV v f))
          (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi stV v f).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkV]
  have hwkv' : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  have hregv : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v Slot.reg ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_rg_val,
      show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV v Slot.reg =
        bitVal PR.zero PR.one
          (∃ u : I, v = F.cell u) from rfl,
      bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
    exact PR.zero_ne_one
  have hwkv : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV)
      stV.val v Slot.wk = PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS]
    exact bitVal_pos rfl
  -- the walk-back into the inner gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.igP (.chk 0)))) f), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.matrix (.ig (.chk 0))) .stay
    exact ⟨rEmb (.matrix (.ig (.chk 0))) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  -- the inner gates
  have higrules : ∀ (i : dt.IGatesSite vi) (ρ : dt.IGatesSh vi i),
      PR.rules (rEmb (.matrix (.ig i)) ρ) =
        dt.igatesRule (one := PR.one) (v := vi)
          (emb := fun p => emb (.matrixP (.igP p)))
          (argsG := (dt.varArgsOf PR.zero PR.one vi).argsIG)
          (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellIGOf)
          (setFailOf := (dt.varArgsOf PR.zero PR.one vi).setFailIGOf)
          (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterIGSt)
          (exitPh := emb (.matrixP .rchk)) i ρ :=
    fun i ρ => hrules (.matrix (.ig i)) ρ
  have higs := ixIGs_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
      (hinj := hinj) (heltP := heltP) (hgap := hgap) (vi := vi)
      (stV := stV) (hrules := higrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkV) (w := w) (wP := wP)
      (hwP := hwP) (hcostR := hcostR) (f₀ := f)
  -- the walk-back at the branch checkpoint
  have hback2 : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.matrix .rchk) .stay
    exact ⟨rEmb (.matrix .rchk) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  have hpre := ((TMData.reachesIn_of_step hback).trans higs).tail hback2
  -- the branch
  rw [ixRoundCtlT, ixRoundEndSt]
  by_cases hbr : dt.ctlBit PR.one
      (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi)) dt.existGateC ∧
    dt.ctlBit PR.one
      (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi)) dt.allGateC
  · rw [dif_pos hbr, if_pos hbr]
    -- the passing dispatch into the matrix
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix .rchk) .dspA
      refine ⟨rEmb (.matrix .rchk) .dspA, ?_, by rw [h]; rfl,
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        by rw [h]; trivial⟩
      rw [h]
      exact ⟨⟨hwkv, hregv⟩, hbr.1, hbr.2⟩
    -- the walk-back into the matrix's first checkpoint
    have hback3 : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0))))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix (.mat (.chk 0))) .stay
      exact ⟨rEmb (.matrix (.mat (.chk 0))) .stay, by rw [h]; exact hwkv',
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩
    -- the matrix
    have hmrules : ∀ (i : dt.MatrixSite vi) (ρ : dt.MatrixSh vi i),
        PR.rules (rEmb (.matrix (.mat i)) ρ) = dt.matrixRule PR.zero PR.one
          vi (emb := fun p => emb (.matrixP (.matP p)))
          (fun a => dt.atomArgs PR.zero PR.one vi a)
          ((dt.varArgsOf PR.zero PR.one vi).enterAtomSt) (emb .mchk1) i ρ :=
      fun i ρ => hrules (.matrix (.mat i)) ρ
    have hmat := ixMatrix_run_thread_reachesIn (F := F) (hhasP := hhasP)
        (hsepP := hsepP) (hix := hix)
        (hinj := hinj) (heltP := heltP) (hord := hord) (hR := hR) (hlin := hlin)
        (htop := htop) (hbot := hbot) (he₀ := he₀) (hwork := hwork) (hv := hv)
        (hvi := hvi) (hwkSt := hwkV) (hmirSt := hmirV) (hbotSt := hbotV)
        (hmono := hmono) (hup := hup) (hvh := hvh) (hxdUse := hxdUse)
        (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK) (hcostR := hcostR)
        (vi := vi) (st := stV)
        (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterAtomSt) (hrules := hmrules)
        (wA := dt.ixMatCost A vi w wP wR wK)
        (hwA := fun a => Finset.le_sup (f := fun a' : Fin (dt.natOf vi) =>
          dt.ixKindCost A vi w wP wR wK (dt.kindOf vi a')) (Finset.mem_univ a))
        (semT := sem (ixRoundPass_of_flags (F := F) (hhas := hhasP) (hinj := hinj)
          (helt := heltP) (hzo := PR.zero_ne_one) (vi := vi) (stV := stV) (v := v)
          (f₀ := f) (h := hbr)))
        (f₀ := dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f
          (dt.nIn vi))
    -- the walk-back at the fold checkpoint, at the threaded state
    have hwkv'T : PR.passTracksAt F.cell Slot.val
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixMatSt (elt := elt) vi stV v (dt.natOf vi)))
        (dt.ixMatSt (elt := elt) vi stV v (dt.natOf vi)).val v' Slot.wk ≠ PR.one := by
      rw [Prog.passTracks_of_ne hne_wk_val, ixBack_wk,
        (ixMatSt_fields (elt := elt) (v := v) (st := stV) (dt.natOf vi)).1, hwkV,
        bitVal_neg (Ne.symm hvv')]
      exact PR.zero_ne_one
    refine TMData.ReachesIn.mono ?_
      ((((hpre.tail hdsp).tail hback3).trans hmat).tail ?_)
    · simp only [ixRoundCost]
      omega
    · refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules .mchk1 .stay
      exact ⟨rEmb .mchk1 .stay, by rw [h]; exact hwkv'T,
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩
  · rw [dif_neg hbr, if_neg hbr]
    -- the skipping dispatch, straight to the fold checkpoint
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.matrixP .rchk))
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb .mchk1)
            (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi stV v f (dt.nIn vi))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell Slot.val
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.matrix .rchk) .dspB
      refine ⟨rEmb (.matrix .rchk) .dspB, ?_, by rw [h]; rfl,
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        by rw [h]; trivial⟩
      rw [h]
      exact ⟨⟨hwkv, hregv⟩, fun hc => hbr ⟨hc.1, hc.2⟩⟩
    -- the walk-back at the fold checkpoint
    refine TMData.ReachesIn.mono ?_ ((hpre.tail hdsp).tail ?_)
    · simp only [ixRoundCost]
      omega
    · refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules .mchk1 .stay
      exact ⟨rEmb .mchk1 .stay, by rw [h]; exact hwkv',
        by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
        fun hc => (by rw [h] at hc; exact hc)⟩

end RoundRun

end Data

end Draw

end DescriptiveComplexity
