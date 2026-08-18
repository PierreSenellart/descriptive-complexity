/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexEval
import DescriptiveComplexity.Problems.Wide.DrawIxEval

/-!
# The clocked spine at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawIxEval`'s legs folded by the *clocked*
program's spine (`nexEvalRuleF`, two rules per checkpoint instead of three, its
phases wrapped in `NexPh`). The legs are the same theorems the space-bounded
spine folds – they are generic in the wrapper – so what this file adds is one
run: the branched evaluation of the whole spine, on a clock.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R B : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (NexPh B (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (NexPh B (EvalPh dt.nv dt.PMF))]
variable {PR : Prog A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I)
variable {elt : I → Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
-- A register's block is the block of the element it stands for.
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

section Spine

variable {v v' : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {rEmb : ∀ i : dt.SEF, dt.NexSESh i → R}
-- The whole evaluation's rules: the spine's own checkpoints and, projected,
-- the machineries the legs ask for.
variable (hrules : ∀ (i : dt.SEF) (ρ : dt.NexSESh i),
  PR.rules (rEmb i ρ) =
    dt.nexEvalRuleF (B := B) PR.zero PR.one
      (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
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
variable (hwR : ∀ s : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop,
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

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The clocked evaluation's spine at an arbitrary address**: the threaded
spine, with the gates no longer assumed to pass. Each position takes whichever of the three legs
its own gates call for, and what the caller owes is only the marker, the
mirror and the bottom mark – all of which the advance sets and every leg
leaves alone. This is the form a sweep can use, since it visits junk
addresses and gated ones alike. -/
theorem nexIxSpineB_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc)) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn (((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.nexEval_reachesIn F.toIxFile (fun i ρ => hrules i ρ) hR hlin hix hbot
    hv hvi
    (restOf := fun k => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [ixBack_wk, hwkOf k]) (fun k r => rfl) fsOf
    (dt.ixLegCost A w wP wR wK (Nat.card ιV)) ?_
  intro k
  have hleg := ixVarLegB_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (ep := NexPh.evalP)
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

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The clocked evaluation, entered and left**: the walk-back the opening's
dispatch owes, the branched spine over the positions, and the dispatch into the
**output's** machinery, whose own exit is the accepting phase (the verdict bit
the accepting predicate reads is that machinery's, so the run has to reach
it). This is the middle leg of
`DescriptiveComplexity.Draw.Data.nexProg_wideAccept_of_legs`, at an arbitrary
file and on a clock. -/
theorem nexIxEvalB_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc)) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx
      dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv) + 1)
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.sub dt.smEntryOut)) (fsOf (Fin.last dt.nv))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hback := dt.step_nexEvalBack F.toIxFile (fun i ρ => hrules i ρ) hR hlin hvi
    (m := (stOf 0).val) (f := fsOf 0)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) 0
    (fun r => by rw [ixBack_wk, hwkOf 0])
  have hexit := dt.step_nexEvalExit F.toIxFile (fun i ρ => hrules i ρ) hR hlin hvi
    (m := (stOf (Fin.last dt.nv)).val) (f := fsOf (Fin.last dt.nv))
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
    ⟨by
      rw [Prog.passTracks_of_ne hne_wk_val, ixBack_wk, hwkOf (Fin.last dt.nv)]
      exact bitVal_pos rfl,
     by
      rw [Prog.passTracks_of_ne hne_rg_val,
        show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (stOf (Fin.last dt.nv)) v Slot.reg =
          bitVal PR.zero PR.one (∃ u : I, v = F.cell u) from rfl,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact PR.zero_ne_one⟩
  exact ((TMData.reachesIn_of_step hback).trans
    (nexIxSpineB_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
      (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
      (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
      (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
      (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
      (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
      (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf) (hwkOf := hwkOf)
      (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ) (hst := hst)
      (hfs := hfs))).tail hexit

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The clocked evaluation, all the way to the accepting phase**: the run
above, and then the **output's** machinery – the one whose verdict bit the
accepting predicate reads. What it asks for is what the output leg asks: the
shape of the argument blocks at the state the spine leaves, the tags they
name, the packs, and the verdict itself. -/
theorem nexIxEvalOutB_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr elt (stOf (Fin.last dt.nv)).mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : (stOf (Fin.last dt.nv)).mir = ixMark elt v)
    (hbotL : (stOf (Fin.last dt.nv)).bot = fun r => r = (fun _ => False))
    (hsavL : (stOf (Fin.last dt.nv)).sav = ixMark elt v)
    (htgtL : (stOf (Fin.last dt.nv)).tgt = ixMark elt v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) elt (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt (stOf (Fin.last dt.nv)).mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV
        (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))) :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV
            (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT))) (mV aT))
          (PR.syElt PR.blank)⟩ :=
  (nexIxEvalB_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
    (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
    (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
    (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf) (hwkOf := hwkOf)
    (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ) (hst := hst)
    (hfs := hfs)).trans
    (dt.ixOutLeg_run (F := F) (elt := elt) (ep := NexPh.evalP)
      (accPh := NexPh.acceptP) (hrulesOut := hrulesOut) (hinj := hinj)
      (hhasP := hhasP) (heltP := heltP) (hsepP := hsepP) (hix := hix)
      (he₀ := he₀) (hord := hord) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono)
      (hup := hup) (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP)
      (hwR := hwR) (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV)
      (htopV := htopV) (mV := mV) (hmV0 := hmV0) (hIncr := hIncr)
      (hTestT := hTestT) (hTestF := hTestF)
      (st := stOf (Fin.last dt.nv)) (hwkSt := hwkOf (Fin.last dt.nv))
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf)
      (hwitOf := hwitOf) (hmir := hmirL) (hbotSt := hbotL) (hsav := hsavL)
      (htgt := htgtL) (semOf := semOf) (hDom := hDom) (hTestOf := hTestOf)
      (f₀ := fsOf (Fin.last dt.nv)) (hacc := hacc))

include hrules hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
open Classical in
/-- **The clocked evaluation, entered and left, whatever the verdict**:
`nexIxEvalOutB_reachesIn` with the verdict not assumed – the run is the same and
what changes is the bit the exit writes at the marker (`ixOutLeg_run_any`). This
is the shape a backward reading uses. -/
theorem nexIxEvalOutB_any_reachesIn
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I)
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = ixMark elt v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j (stOf j.castSucc) →
      ∀ (p : IxScratch dt A R (NexPh B (EvalPh dt.nv dt.PMF)) I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.ixLegStB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.ixLegCtlB (PR := PR) (v := v) (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
      dt.VarShF (none : dt.VarIx) i → R}
    (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
        (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
          (fun p => NexPh.evalP (.sub (Sum.inr p))) NexPh.acceptP i ρ)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr elt (stOf (Fin.last dt.nv)).mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmirL : (stOf (Fin.last dt.nv)).mir = ixMark elt v)
    (hbotL : (stOf (Fin.last dt.nv)).bot = fun r => r = (fun _ => False))
    (hsavL : (stOf (Fin.last dt.nv)).sav = ixMark elt v)
    (htgtL : (stOf (Fin.last dt.nv)).tgt = ixMark elt v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV a)) elt (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt (stOf (Fin.last dt.nv)).mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    :
    (wideData (Univ A R (NexPh B (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A w wP wR wK (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) (fsOf 0)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.acceptP
          (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV
            (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (fun r => if r = v then
              Function.update
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                  (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT)) v)
                (dt.varArgsOf PR.zero PR.one none).newSlot
                (bitVal PR.zero PR.one
                  ((dt.varArgsOf PR.zero PR.one none).accBit
                    (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
                      mV (stOf (Fin.last dt.nv)) tOf semOf (fsOf (Fin.last dt.nv)))))
            else dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixRoundSt (stOf (Fin.last dt.nv)) (mV aT)) r) (mV aT))
          (PR.syElt PR.blank)⟩ :=
  (nexIxEvalB_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
    (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
    (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
    (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
    (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (stOf := stOf) (fsOf := fsOf) (hwkOf := hwkOf)
    (hmirOf := hmirOf) (hbotOf := hbotOf) (semTJ := semTJ) (hst := hst)
    (hfs := hfs)).trans
    (dt.ixOutLeg_run_any (F := F) (elt := elt) (ep := NexPh.evalP)
      (accPh := NexPh.acceptP) (hrulesOut := hrulesOut) (hinj := hinj)
      (hhasP := hhasP) (heltP := heltP) (hsepP := hsepP) (hix := hix)
      (he₀ := he₀) (hord := hord) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono)
      (hup := hup) (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP)
      (hwR := hwR) (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV)
      (htopV := htopV) (mV := mV) (hmV0 := hmV0) (hIncr := hIncr)
      (hTestT := hTestT) (hTestF := hTestF)
      (st := stOf (Fin.last dt.nv)) (hwkSt := hwkOf (Fin.last dt.nv))
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf)
      (hwitOf := hwitOf) (hmir := hmirL) (hbotSt := hbotL) (hsav := hsavL)
      (htgt := htgtL) (semOf := semOf) (hDom := hDom) (hTestOf := hTestOf)
      (f₀ := fsOf (Fin.last dt.nv)))

end Spine

end Data

end Draw

end DescriptiveComplexity
