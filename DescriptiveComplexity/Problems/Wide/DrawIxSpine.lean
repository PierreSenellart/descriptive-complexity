/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxEval

/-!
# The space-bounded spine at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawIxEval`'s legs folded by the
space-bounded program's own spine (`evalRuleF`, whose phases are wrapped in
`OuterPh`). The legs themselves are generic in that wrapper, so a clocked
program folds the same legs with its own spine and nothing here is repeated.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A R : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
variable {PR : Prog A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
variable {elt : I → Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
-- A register's block is the block of the element it stands for.
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

section Spine


variable {v v' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {rEmb : ∀ i : dt.SEF, dt.SESh i → R}
-- The whole evaluation's rules: the spine's own checkpoints and, projected,
-- the machineries the legs ask for.
variable (hrules : ∀ (i : dt.SEF) (ρ : dt.SESh i),
  PR.rules (rEmb i ρ) =
    dt.evalRuleF PR.zero PR.one (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = DrawTag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
  Use u → WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom of any position's variable is priced at.
variable (w wG wP wR wK : ℕ)
variable (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
variable (hwR : ∀ s : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
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
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV → I → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr F.le (mV a) (mV a'))
variable (hTestT : ∀ u : I, dt.InnerFull F.blk (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u : I, ¬dt.InnerFull F.blk (mV a) u)


/-! ### The spine -/

omit [Finite I] [Finite dt.KIx] in
include hrules hR hlin hix hbot hv hvi in
/-- **The spine over given legs**: `eval_run` at the concrete tape
presentation, each position's machinery an arbitrary run — the caller
plugs in `DescriptiveComplexity.Draw.DrawData.ixVarLeg_run` at a gated address
and `DescriptiveComplexity.Draw.DrawData.ixVarLegFail_run` at a junk one. -/
theorem ixEvalSpineLegs_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (wL : ℕ)
    (hVar : ∀ j : Fin dt.nv,
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd)).ReachesIn wL
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.sub (dt.smEntry j)))
          (fsOf j.castSucc)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk j.succ)) (fsOf j.succ)),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf j.succ))
          (stOf j.succ).val) (PR.syElt PR.blank)⟩) :
    (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn ((wL + 2) * dt.nv)
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  exact dt.eval_reachesIn F.toIxFile (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [ixBack_wk, hwkOf k]) (fun k r => rfl) fsOf wL hVar

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine, fully instantiated**: from the checkpoint
before the first variable to the checkpoint after the last, one whole
machinery per position — each leg
`DescriptiveComplexity.Draw.DrawData.ixVarLeg_run`, the tape and control
threads given as families with one cover equation per position. -/
theorem ixEvalSpine_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (TestOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → I → Prop)
    (hcompatOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).mir (F.cell u)) ↔ TestOfJ j ℓ u)
    (tOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (t' : dt.X.Tag),
      wmBlk (ixAddr elt (stOf j.castSucc).mir)
        (DrawTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOfJ j ℓ)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (hsavOf : ∀ j : Fin dt.nv, (stOf j.castSucc).sav = ixMark elt v)
    (htgtOf : ∀ j : Fin dt.nv, (stOf j.castSucc).tgt = ixMark elt v)
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (hDomJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))),
      ExpExpansion.DomHolds (X := dt.X)
        (tOfJ j ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt (stOf j.castSucc).mir)
            (DrawTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      TestOfJ j ℓ u)
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixPostVarSt v (stOf j.castSucc) (mV aT) (dt.varList.get j)
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.ixLegCtl (elt := elt)
            (v := v) (aT := aT) F hinj hhasP heltP mV j (stOf j.castSucc) (tOfJ j)
            (semOfJ j) (fsOf j.castSucc))))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtl (elt := elt)
        (v := v) (aT := aT) F hinj hhasP heltP mV j (stOf j.castSucc) (tOfJ j)
        (semOfJ j) (fsOf j.castSucc)) :
    (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn (((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv))
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_reachesIn F.toIxFile (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [ixBack_wk, hwkOf k]) (fun k r => rfl) fsOf
    (dt.ixLegCost A w wP wR wK (Nat.card ιV)) ?_
  intro k
  have hleg := ixVarLeg_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (ep := OuterPh.evalP)
    (rEmbM := fun j i ρ => rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hrulesM := fun j i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
    (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
    (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (j := k)
    (st := stOf k.castSucc) (hwkSt := hwkOf _) (TestOf := TestOfJ k)
    (hcompatOf := hcompatOfJ k) (tOf := tOfJ k) (hwitOf := hwitOfJ k)
    (hmir := hmirOf k) (hbotSt := hbotOf k) (hsav := hsavOf k) (htgt := htgtOf k)
    (semOf := semOfJ k) (hDom := hDomJ k) (hTestOf := hTestOfJ k)
    (f₀ := fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine, fully instantiated — threaded**: as
`DescriptiveComplexity.Draw.DrawData.ixEvalSpine_run` with `hsavOf` and
`htgtOf` **gone**. That is the point of the whole threading: the advance
refreshes the marker and the mirror but not SAV and TARGET, so a sweep can
meet those two hypotheses at one address at most, while every other
hypothesis here is about the marker, the mirror and the tracks, which do
ride. -/
theorem ixEvalSpine_run_thread_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (TestOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → I → Prop)
    (hcompatOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).mir (F.cell u)) ↔ TestOfJ j ℓ u)
    (tOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (t' : dt.X.Tag),
      wmBlk (ixAddr elt (stOf j.castSucc).mir)
        (DrawTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOfJ j ℓ)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv)
      (p : IxScratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hDomJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))),
      ExpExpansion.DomHolds (X := dt.X)
        (tOfJ j ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt (stOf j.castSucc).mir)
            (DrawTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              DrawTag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      TestOfJ j ℓ u)
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (tOfJ j) (semTJ j)
        (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (tOfJ j) (semTJ j)
        (fsOf j.castSucc)) :
    (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn (((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv))
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_reachesIn F.toIxFile (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [ixBack_wk, hwkOf k]) (fun k r => rfl) fsOf
    (dt.ixLegCost A w wP wR wK (Nat.card ιV)) ?_
  intro k
  have hleg := ixVarLeg_run_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (ep := OuterPh.evalP)
    (rEmbM := fun j i ρ => rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hrulesM := fun j i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
    (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
    (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (j := k)
    (st := stOf k.castSucc) (hwkSt := hwkOf _) (TestOf := TestOfJ k)
    (hcompatOf := hcompatOfJ k) (tOf := tOfJ k) (hwitOf := hwitOfJ k)
    (hmir := hmirOf k) (hbotSt := hbotOf k) (semT := semTJ k) (hDom := hDomJ k)
    (hTestOf := hTestOfJ k) (f₀ := fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine at an arbitrary address**: as
`DescriptiveComplexity.Draw.DrawData.ixEvalSpine_run_thread` with the gates no
longer assumed to pass. Each position takes whichever of the three legs
its own gates call for, and what the caller owes is only the marker, the
mirror and the bottom mark — all of which the advance sets and every leg
leaves alone. This is the form a sweep can use, since it visits junk
addresses and gated ones alike. -/
theorem ixEvalSpineB_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (elt := elt) (aT := aT) F hinj hhasP heltP mV j (stOf j.castSucc) (semTJ j)
        (fsOf j.castSucc)) :
    (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn (((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv))
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (OuterPh.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_reachesIn F.toIxFile (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [ixBack_wk, hwkOf k]) (fun k r => rfl) fsOf
    (dt.ixLegCost A w wP wR wK (Nat.card ιV)) ?_
  intro k
  have hleg := ixVarLegB_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (ep := OuterPh.evalP)
    (rEmbM := fun j i ρ => rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hrulesM := fun j i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ)
    (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
    (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
    (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (j := k)
    (st := stOf k.castSucc) (hwkSt := hwkOf _) (hmir := hmirOf k)
    (hbotSt := hbotOf k) (semT := semTJ k) (f₀ := fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

end Spine

end DrawData

end Draw

end DescriptiveComplexity
