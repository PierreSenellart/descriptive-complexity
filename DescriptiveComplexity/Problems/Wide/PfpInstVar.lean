/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpInstRound
import DescriptiveComplexity.Problems.Wide.PfpRunVar
import DescriptiveComplexity.Problems.Wide.PfpInner
import DescriptiveComplexity.Problems.Wide.PfpAddr

/-!
# One variable's machinery, instantiated: the gates' and the matrix's legs

The two abstract machineries of
`DescriptiveComplexity.Pfp.PfpData.var_run` – the gates' run to the verdict
checkpoint and the per-round matrix pass – discharged at the program's own
rules (`DescriptiveComplexity.Pfp.PfpData.varRuleF` at
`DescriptiveComplexity.Pfp.PfpData.varArgsOf`): each is a walk-back into
the sub-machinery's first checkpoint, the assembled run
(`DescriptiveComplexity.Pfp.PfpData.gates_run`,
`DescriptiveComplexity.Pfp.PfpData.matrix_run`), and the walk-back at the
landing checkpoint.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section VarInst

variable (vi : dt.VarIx) (st : TapeStD dt A R P)
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {emb : dt.VarPhF vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.VarSiteF vi, dt.VarShF vi i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : dt.VarSiteF vi) (ρ : dt.VarShF vi i),
  PR.rules (rEmb i ρ) = dt.varRuleF PR.zero PR.one vi
    (dt.varArgsOf PR.zero PR.one vi) emb exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable (TestOf : Fin (dt.arOf vi) → Univ A R P dt.KIx dt.dd → Prop)
variable (hcompatOf : ∀ (ℓ : Fin (dt.arOf vi)) (u : Univ A R P dt.KIx dt.dd),
  dt.wellShapedG PR.zero PR.one
    (Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      st.mir (RF.cell u)) ↔ TestOf ℓ u)
variable (tOf : Fin (dt.arOf vi) → dt.X.Tag)
variable (htagOf : ∀ ℓ : Fin (dt.arOf vi),
  dt.dspTagOf PR.zero PR.one
    (wmBlk st.mir
      (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)) =
  tOf ℓ)

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The gates' leg of one variable's machinery**: from the dispatch's
landing one cell right of the marker, the walk-back, the whole gate
sequence at a gated address, and the walk-back at the verdict
checkpoint. -/
theorem varGates_run (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk1)
          (dt.gatesFs RF PR.zero PR.one vi st v
            (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
            dt.card_le_ntgDim
            (fun t => le_trans (Finset.le_sup
              (f := fun t' : dt.X.Tag => (dt.domPk t').n)
              (Finset.mem_univ t)) dt.domDepth_le_eDim)
            (fun t => le_trans (Finset.le_sup
              (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
              (Finset.mem_univ t)) dt.domReads_le_nfDim)
            tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt f₀
            (dt.arOf vi))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hwkv' : PR.passTracksAt RF.cell Slot.val (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      st.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the walk-back into the gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.gates (.chk 0)) .stay
    exact ⟨rEmb (.gates (.chk 0)) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  refine (Relation.ReflTransGen.single hback).trans ?_
  -- the gate sequence
  have hgrules : ∀ (i : dt.GatesSite vi) (ρ : dt.GatesSh vi i),
      PR.rules (rEmb (.gates i) ρ) = dt.gatesRule (one := PR.one) (v := vi)
        (emb := fun p => emb (.gatesP p))
        (argsG := fun ℓ => dt.gateArgs PR.zero PR.one
          (Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ)) dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim))
        (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellGOf)
        (setFail := (dt.varArgsOf PR.zero PR.one vi).setFail)
        (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
        (failPh := emb .vchk1) (exitPh := emb .vchk1) i ρ :=
    fun i ρ => hrules (.gates i) ρ
  refine Relation.ReflTransGen.trans
    (dt.gates_run RF hord (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      ((dt.varArgsOf PR.zero PR.one vi).wellGOf)
      ((dt.varArgsOf PR.zero PR.one vi).setFail)
      ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      hgrules hR hlin htop hbot hv hvi hwkSt
      TestOf hcompatOf tOf htagOf hTestOf f₀) ?_
  -- the walk-back at the verdict checkpoint
  refine Relation.ReflTransGen.single ?_
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules .vchk1 .stay
  exact ⟨rEmb .vchk1 .stay, by rw [h]; exact hwkv',
    by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
    fun hc => (by rw [h] at hc; exact hc)⟩

/-- **The control after a failing gate sequence**: the fail store at the
failing block's entry, the flag clear. -/
noncomputable def failCtl (ℓ₀ : Fin (dt.arOf vi)) (f₀ : dt.CtlIx → A) :
    dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one vi).setFail
    ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt ℓ₀
      (dt.gatesFs RF PR.zero PR.one vi st v
        (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
        dt.card_le_ntgDim
        (fun t => le_trans (Finset.le_sup
          (f := fun t' : dt.X.Tag => (dt.domPk t').n)
          (Finset.mem_univ t)) dt.domDepth_le_eDim)
        (fun t => le_trans (Finset.le_sup
          (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
          (Finset.mem_univ t)) dt.domReads_le_nfDim)
        tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt f₀ (ℓ₀ : ℕ))
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
    (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The gates' leg at a junk address**: the walk-back, the passing
prefix, the failing block, and the walk-back at the verdict checkpoint —
the fail store applied, the flag clear. -/
theorem varGatesFail_run (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : Univ A R P dt.KIx dt.dd} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk1)
          (dt.failCtl (PR := PR) (v := v) RF vi st tOf ℓ₀ f₀)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hwkv' : PR.passTracksAt RF.cell Slot.val (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      st.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the walk-back into the gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.gates (.chk 0)) .stay
    exact ⟨rEmb (.gates (.chk 0)) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  refine (Relation.ReflTransGen.single hback).trans ?_
  -- the failing gate sequence
  have hgrules : ∀ (i : dt.GatesSite vi) (ρ : dt.GatesSh vi i),
      PR.rules (rEmb (.gates i) ρ) = dt.gatesRule (one := PR.one) (v := vi)
        (emb := fun p => emb (.gatesP p))
        (argsG := fun ℓ => dt.gateArgs PR.zero PR.one
          (Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ)) dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim))
        (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellGOf)
        (setFail := (dt.varArgsOf PR.zero PR.one vi).setFail)
        (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
        (failPh := emb .vchk1) (exitPh := emb .vchk1) i ρ :=
    fun i ρ => hrules (.gates i) ρ
  refine Relation.ReflTransGen.trans
    (dt.gates_run_fail RF hord (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      ((dt.varArgsOf PR.zero PR.one vi).wellGOf)
      ((dt.varArgsOf PR.zero PR.one vi).setFail)
      ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      hgrules hR hlin htop hbot hv hvi hwkSt
      TestOf hcompatOf tOf htagOf ℓ₀ hTestLt hfail f₀) ?_
  -- the walk-back at the verdict checkpoint
  refine Relation.ReflTransGen.single ?_
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules .vchk1 .stay
  exact ⟨rEmb .vchk1 .stay, by rw [h]; exact hwkv',
    by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
    fun hc => (by rw [h] at hc; exact hc)⟩

include hrules hR hlin hord htop hbot hwork hv hvi in
/-- **The matrix's leg of one variable's machinery**, per VAL-loop round:
from the dispatch's landing one cell right of the marker, the walk-back,
the whole matrix at the round's state, and the walk-back at the fold
checkpoint. -/
theorem varMatrix_run (stV : TapeStD dt A R P)
    (hwkV : stV.wk = fun r => r = v) (hmirV : stV.mir = v)
    (hbotV : stV.bot = fun r => r = (fun _ => False))
    (hsavV : stV.sav = v) (htgtV : stV.tgt = v)
    (sem : ∀ a : Fin (dt.natOf vi),
      dt.KindSem PR.zero PR.one vi stV (dt.kindOf vi a))
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .mchk1)
          (dt.matFs RF hord PR.zero PR.one vi stV v
            (dt.varArgsOf PR.zero PR.one vi).enterAtomSt sem f
            (dt.natOf vi))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le stV r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkV]
  have hwkv' : PR.passTracksAt RF.cell Slot.val (dt.back RF.cell PR.zero PR.one dt.dd0Le stV)
      stV.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the walk-back into the matrix's first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0)))) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.matrixP (.matP (.chk 0)))) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le stV) stV.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.matrix (.mat (.chk 0))) .stay
    exact ⟨rEmb (.matrix (.mat (.chk 0))) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
  refine (Relation.ReflTransGen.single hback).trans ?_
  -- the matrix
  have hmrules : ∀ (i : dt.MatrixSite vi) (ρ : dt.MatrixSh vi i),
      PR.rules (rEmb (.matrix (.mat i)) ρ) = dt.matrixRule PR.zero PR.one vi
        (emb := fun p => emb (.matrixP (.matP p)))
        (fun a => dt.atomArgs PR.zero PR.one vi a)
        ((dt.varArgsOf PR.zero PR.one vi).enterAtomSt) (emb .mchk1) i ρ :=
    fun i ρ => hrules (.matrix (.mat i)) ρ
  refine Relation.ReflTransGen.trans
    (dt.matrix_run RF hord hR hlin htop hbot hwork hv hvi hwkV hmirV hbotV hsavV
      htgtV ((dt.varArgsOf PR.zero PR.one vi).enterAtomSt) hmrules sem f) ?_
  -- the walk-back at the fold checkpoint
  refine Relation.ReflTransGen.single ?_
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules .mchk1 .stay
  exact ⟨rEmb .mchk1 .stay, by rw [h]; exact hwkv',
    by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
    fun hc => (by rw [h] at hc; exact hc)⟩

omit [Nonempty A] [L.IsRelational] [L.Structure A] [Finite A] [Finite R] [Finite P]
  [Finite dt.KIx] hrules hR hv hwkSt in
include hlin hord htop in
/-- **The background bundle, discharged at a boundary state**: the five
slot equations `DescriptiveComplexity.Pfp.PfpData.var_run`'s kits read are
definitional in `DescriptiveComplexity.Pfp.PfpData.back`, given the marker
and the order facts. -/
theorem varBg_back (stV : TapeStD dt A R P)
    (hwkV : stV.wk = fun r => r = v) :
    dt.VarBg (laidFile RF hord) PR.zero PR.one v gtop
      (dt.back RF.cell PR.zero PR.one dt.dd0Le stV) stV.val := by
  refine ⟨fun r => ?_, fun r => rfl,
    fun r => dt.back_regLast hlin htop hord r,
    fun u b => dt.back_blk_cell (RF.injective hlin) u b, fun r => rfl⟩
  rw [back_wk, hwkV]

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The whole machinery at a junk address**: entry, the failing gates,
and the verdict checkpoint's clear flag routing straight to the exit with
the stage slot erased — the VAL loop never entered. -/
theorem varMachineFail_run (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : Univ A R P dt.KIx dt.dd} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A)
    {rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hoff : ∀ r, r ≠ v → rest' r = dt.back RF.cell PR.zero PR.one dt.dd0Le st r)
    (hupd : rest' v = Function.update
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)
      (dt.varArgsOf PR.zero PR.one vi).newSlot PR.zero) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.failCtl (PR := PR) (v := v) RF vi st tOf ℓ₀
            ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
              (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val rest' st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hns : (dt.varArgsOf PR.zero PR.one vi).newSlot ≠ Slot.val := by
    rcases vi with _ | i <;> exact fun h => nomatch h
  have hflagF : dt.failCtl (PR := PR) (v := v) RF vi st tOf ℓ₀
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
      (dt.varArgsOf PR.zero PR.one vi).gateFlag ≠ PR.one := by
    intro hc
    have hc' : dt.ctlBit PR.one
        (dt.setCtl PR.zero PR.one dt.gateFlagC False
          ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt ℓ₀
            (dt.gatesFs RF PR.zero PR.one vi st v
              (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
              dt.card_le_ntgDim
              (fun t => le_trans (Finset.le_sup
                (f := fun t' : dt.X.Tag => (dt.domPk t').n)
                (Finset.mem_univ t)) dt.domDepth_le_eDim)
              (fun t => le_trans (Finset.le_sup
                (f := fun t' : dt.X.Tag =>
                  (blkAtoms (dt.domPk t').mat).length)
                (Finset.mem_univ t)) dt.domReads_le_nfDim)
              tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt
              ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
                (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (ℓ₀ : ℕ))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))
        dt.gateFlagC := hc
    exact (ctlBit_setCtl_self hzo _ _ _).mp hc'
  exact dt.var_run_fail (laidFile RF hord) (fun i ρ => hrules i ρ) hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (dt.varBg_back RF hord hlin  htop st hwkSt)
    (dt.varGatesFail_run RF hord vi st hrules hR hlin  htop hbot hv hvi hwkSt
      TestOf hcompatOf tOf htagOf ℓ₀ hTestLt hfail
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))
    hflagF hns hoff hupd

/-- **The control after a completed but failing gate sequence**: the whole
gates' thread — every block's file test passed and every block's machinery
ran — with the flag clear because some block encoded no point. -/
noncomputable def ungatedCtl (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.gatesFs RF PR.zero PR.one vi st v
    (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    dt.card_le_ntgDim
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (dt.domPk t').n)
      (Finset.mem_univ t)) dt.domDepth_le_eDim)
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
      (Finset.mem_univ t)) dt.domReads_le_nfDim)
    tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt f₀ (dt.arOf vi)

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The whole machinery at a shaped but ungated address**: every block
passes its file test — the total dispatch carries each block's machinery
through — but some block encodes no point, its witness not one-hot at the
dispatched tag or its domain sentence failing. The gates complete with the
flag clear, and the verdict checkpoint routes straight to the exit with
the stage slot erased — the VAL loop never entered. The third landing an
arbitrary address makes, beside the gated and the shape-failing ones. -/
theorem varMachineUngated_run (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (ℓ₀ : Fin (dt.arOf vi))
    (hbad : ¬((∀ t' : dt.X.Tag,
        wmBlk st.mir
          (PfpTag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko vi) ℓ₀) :
            Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)
          (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ₀) ∧
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ₀, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (PfpTag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko vi) ℓ₀) :
              Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)))))
    (f₀ : dt.CtlIx → A)
    {rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hoff : ∀ r, r ≠ v → rest' r = dt.back RF.cell PR.zero PR.one dt.dd0Le st r)
    (hupd : rest' v = Function.update
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)
      (dt.varArgsOf PR.zero PR.one vi).newSlot PR.zero) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ungatedCtl (PR := PR) (v := v) RF vi st tOf
            ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
              (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val rest' st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hns : (dt.varArgsOf PR.zero PR.one vi).newSlot ≠ Slot.val := by
    rcases vi with _ | i <;> exact fun h => nomatch h
  have hflagF : dt.ungatedCtl (PR := PR) (v := v) RF vi st tOf
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
      (dt.varArgsOf PR.zero PR.one vi).gateFlag ≠ PR.one := by
    intro hcx
    have hchar := dt.ctlBit_gateFlagC_gatesFs (st := st) (v := v)
      (bOf := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      (hc := dt.card_le_ntgDim)
      (hnG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (hrdG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      (tOf := tOf)
      (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      RF hzo (fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    have hcx' : dt.ctlBit PR.one
        (dt.gatesFs RF PR.zero PR.one vi st v
          (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
          dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag =>
              (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim)
          tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt
          ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
          (dt.arOf vi)) dt.gateFlagC := hcx
    exact hbad ((hchar.mp hcx').2 ℓ₀ ℓ₀.isLt)
  exact dt.var_run_fail (laidFile RF hord) (fun i ρ => hrules i ρ) hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (dt.varBg_back RF hord hlin  htop st hwkSt)
    (hGatesR := dt.varGates_run RF hord vi st hrules hR hlin htop hbot hv hvi
      hwkSt TestOf hcompatOf tOf htagOf hTestOf
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))
    hflagF hns hoff hupd


/-! ### The whole variable machinery, run -/

section VarCapstone

/-- **The state of one VAL-loop round**: the entry state with the round's
VAL content. -/
noncomputable def roundSt (m : Univ A R P dt.KIx dt.dd → Prop) :
    TapeStD dt A R P :=
  { st with val := m }

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational]
  [Finite dt.KIx] in
/-- **Two round states at the same register ask the same pass.** -/
theorem igPassP_roundSt (zero one : A) (vi : dt.VarIx)
    (st st' : TapeStD dt A R P)
    (m : Univ A R P dt.KIx dt.dd → Prop)
    (ℓ : Fin (dt.nIn vi)) :
    dt.igPassP RF zero one vi (dt.roundSt st m) ℓ ↔
      dt.igPassP RF zero one vi (dt.roundSt st' m) ℓ :=
  dt.igPassP_congr RF zero one vi rfl ℓ


variable {dt}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- A state written with the register it already holds is itself. -/
theorem roundSt_val (stV : TapeStD dt A R P) : dt.roundSt stV stV.val = stV :=
  rfl

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- Two round states' backgrounds agree off the VAL slot. -/
theorem back_roundSt_off {zero one : A}
    (m₁ m₂ : Univ A R P dt.KIx dt.dd → Prop)
    (r : Univ A R P dt.KIx dt.dd → Prop) (s : dt.SlotIx)
    (hs : s ≠ Slot.val) :
    dt.back RF.cell zero one dt.dd0Le (dt.roundSt st m₁) r s =
      dt.back RF.cell zero one dt.dd0Le (dt.roundSt st m₂) r s := by
  match s with
  | .val => exact absurd rfl hs
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .tgt | .wk | .bot | .ltp | .old _ | .new _ => rfl

variable (dt) in
open Classical in
/-- **The carry of a VAL round**: the greatest element the register is
clear at, everything above it set – what the increment's landing phase
names. -/
noncomputable def valCarry (s : Univ A R P dt.KIx dt.dd → Prop) :
    Univ A R P dt.KIx dt.dd :=
  if h : ∃ u : Univ A R P dt.KIx dt.dd,
      ¬s u ∧ ∀ w, WMLt WMLe u w → s w then h.choose
  else (PfpTag.sym, fun _ => Classical.ofNonempty)

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- The carry is unique, so the chosen one is the hypothesis's. -/
theorem valCarry_eq (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    {s : Univ A R P dt.KIx dt.dd → Prop} {u₀ : Univ A R P dt.KIx dt.dd}
    (h1 : ¬s u₀) (h2 : ∀ w, WMLt WMLe u₀ w → s w) :
    dt.valCarry s = u₀ := by
  classical
  have hex : ∃ u : Univ A R P dt.KIx dt.dd,
      ¬s u ∧ ∀ w, WMLt WMLe u w → s w := ⟨u₀, h1, h2⟩
  rw [valCarry, dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  by_contra hne
  rcases hlin.2.2.2 hex.choose u₀ with hle | hle
  · exact h1 (hc2 _ ⟨hle, fun hc => hne (hlin.2.2.1 _ _ hle hc)⟩)
  · exact hc1 (h2 _ ⟨hle, fun hc => hne (hlin.2.2.1 _ _ hc hle)⟩)

section Threads

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi (dt.roundSt st (mV a)) (dt.kindOf vi b))

variable (v) in
/-- **The exit control of one VAL round**, at an entry control: the inner
gates' thread over the round's register, then — at a passing round only,
both flags set — the matrix thread on its output. -/
noncomputable def roundFX (q : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV a)) v (semOf a) q

variable (v) in
/-- **The VAL loop's entry-control thread**: the fold's start at the
cleared register, each round the matrix pass folded and stored at the
carry's block. -/
noncomputable def varFM (fG : dt.CtlIx → A) : ιV → dt.CtlIx → A :=
  iterOrd ((dt.varArgsOf PR.zero PR.one vi).initSt fG
      (dt.back RF.cell PR.zero PR.one dt.dd0Le
        (dt.roundSt st (fun _ => False)) v))
    (fun a q =>
      (dt.varArgsOf PR.zero PR.one vi).storeCarry
        (tagBlk (dt.valCarry (mV a)).1)
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.roundFX RF hord vi st v mV semOf q a)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))

/-- **The leaf a round stores**: the two gate flags' combination — `False`
if an ∃-level's block is not an encoding, the matrix's value only if every
∀-level's is. -/
noncomputable def roundLeaf (q : dt.CtlIx → A) : Prop :=
  dt.ctlBit PR.one q dt.existGateC ∧
    (dt.ctlBit PR.one q dt.allGateC → dt.postLeaf PR.one vi q)

/-! ### The fold invariant of the VAL loop -/

omit [Fintype dt.SlotIx] [Finite dt.KIx] in
omit [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A machine-order increment is a block-major one, through the reduction's
order characterization. -/
private theorem wmIncr_lexRel_of_wmLe
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {s t : Univ A R P dt.KIx dt.dd → Prop} (hi : WMIncr WMLe s t) :
    WMIncr (lexRel (· ≤ · : PfpTag R P dt.KIx → PfpTag R P dt.KIx → Prop)
      (tupLeLex (A := A) (d := dt.dd))) s t := by
  obtain ⟨u, hu, hab, ht⟩ := hi
  have hLt : ∀ x y : Univ A R P dt.KIx dt.dd,
      WMLt (lexRel (· ≤ · : PfpTag R P dt.KIx → PfpTag R P dt.KIx → Prop)
        (tupLeLex (A := A) (d := dt.dd))) x y ↔ WMLt WMLe x y := by
    intro x y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hord x y).mpr ((Wide.tagTupleLe_iff_lexRel x y).mpr h1),
        fun hc => h2 ((Wide.tagTupleLe_iff_lexRel y x).mp
          ((hord y x).mp hc))⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Wide.tagTupleLe_iff_lexRel x y).mp ((hord x y).mp h1),
        fun hc => h2 ((hord y x).mpr
          ((Wide.tagTupleLe_iff_lexRel y x).mpr hc))⟩
  exact ⟨u, hu, fun w hw => hab w ((hLt u w).mp hw),
    fun w => (ht w).trans (or_congr Iff.rfl
      (and_congr Iff.rfl (not_congr (hLt u w).symm)))⟩

omit [Finite R] [Finite P] [Finite dt.KIx] in
include hlin hord in
/-- **The VAL loop maintains the fold's contributions**: at every round of
the enumeration, the accumulator vector of the control thread reads the
`accCVal` contributions of the inner quantifier prefix at the register's
inner blocks — the invariant that turns the machinery's exit verdict into
the prefix's value. -/
theorem readAcc_varFM
    {a₀ : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : PfpTag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (fG : dt.CtlIx → A)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (mV a)))
    (a : ιV) (j : ℕ) (hj : j < dt.ki) :
    dt.readAcc PR.one (dt.varFM RF hord vi st v mV semOf fG a) j ↔
      accCVal (dt.polOf vi) Ps (WMSetLe tupLeLex) j
        (ixBlk (argIn dt.ko) (mV a)) := by
  classical
  have hzo := PR.zero_ne_one
  have hlinV : IsLinOrd (tupLeLex (A := A) (d := dt.dd)) :=
    Wide.isLinOrd_tupLeLex
  -- the accumulators ride through a round's matrix pass and its fold
  have hride : ∀ (q : dt.CtlIx → A) (a' : ιV) (i : ℕ),
      dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf q a')
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a')) v)) i ↔
      dt.readAcc PR.one q i := by
    intro q a' i
    have h2 : ∀ jj : Fin dt.naDim,
        dt.roundFX RF hord vi st v mV semOf q a' (dt.accC jj) = q (dt.accC jj) :=
      fun jj => dt.roundCtl_apply_accC RF hord vi (dt.roundSt st (mV a')) v
        (semOf a') q jj
    have h1 : dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf q a')
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a')) v)) i ↔
        dt.readAcc PR.one (dt.roundFX RF hord vi st v mV semOf q a') i :=
      readAcc_setLeaf _ _ i
    rw [h1]
    exact exists_congr fun h => by rw [h2 ⟨i, h⟩]
  -- the leaf after a round's fold is the matrix's value there
  have hleafride : ∀ (q : dt.CtlIx → A) (a' : ιV),
      dt.ctlBit PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf q a')
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a')) v))
        dt.leafC ↔
      dt.roundLeaf (PR := PR) vi (dt.roundFX RF hord vi st v mV semOf q a') :=
    fun q a' => ctlBit_setLeaf hzo _ _
  induction a using order_induction generalizing j hj with
  | hmin z hz =>
    have hz0 : mV z = fun _ => False := by
      have hza : z = a₀ := le_antisymm (hz a₀) (hbotV z)
      rw [hza, hmV0]
    rw [show dt.varFM RF hord vi st v mV semOf fG z =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v) from iterOrd_bot hz]
    have hjna : j < dt.naDim := by
      have hna : dt.naDim = dt.ki + 1 := rfl
      omega
    have hread : dt.readAcc PR.one
        ((dt.varArgsOf PR.zero PR.one vi).initSt fG
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.roundSt st (fun _ => False)) v)) j ↔
        (dt.polOf vi j = false) := by
      change dt.readAcc PR.one
        (dt.setCtl PR.zero PR.one dt.existGateC True
          (dt.setCtl PR.zero PR.one dt.allGateC True
            (dt.initAcc PR.zero PR.one (dt.polOf vi) fG))) j ↔ _
      have hpt : ∀ hh : j < dt.naDim,
          dt.setCtl PR.zero PR.one dt.existGateC True
            (dt.setCtl PR.zero PR.one dt.allGateC True
              (dt.initAcc PR.zero PR.one (dt.polOf vi) fG))
            (dt.accC ⟨j, hh⟩) =
          dt.initAcc PR.zero PR.one (dt.polOf vi) fG (dt.accC ⟨j, hh⟩) := by
        intro hh
        rw [setCtl_of_ne (show dt.accC ⟨j, hh⟩ ≠ dt.existGateC from
            fun h => nomatch h),
          setCtl_of_ne (show dt.accC ⟨j, hh⟩ ≠ dt.allGateC from
            fun h => nomatch h)]
      exact Iff.trans (exists_congr fun hh => by rw [hpt hh])
        (readAcc_initAcc hzo _ _ hjna)
    rw [hread, hz0]
    exact (accCVal_bot (fun i b => wmSetLe_of_empty hlinV
      (fun w hw => hw) b) j).symm
  | hstep w z hwz hnb ih =>
    -- the cover, in the machine order and block-major
    have hcov : WMIncr WMLe (mV w) (mV z) :=
      hIncr w z hwz (fun b hb => hnb b hb)
    obtain ⟨τ, hfull, hstepB, hbefore, hafter⟩ :=
      (wmIncr_lexRel_iff isLinOrd_le (mV w) (mV z)).mp
        (wmIncr_lexRel_of_wmLe hord hcov)
    -- the carry tag is an inner block
    obtain ⟨u₂, hu₂, hab₂, htz⟩ := id hstepB
    have hmem : mV z (τ, u₂) := (htz u₂).mpr (Or.inl rfl)
    obtain ⟨c, rfl⟩ := hKin z τ u₂ hmem
    -- the carry element is the register's chosen one
    have hab : ∀ y : Univ A R P dt.KIx dt.dd,
        WMLt WMLe (argIn dt.ko c, u₂) y → mV w y := by
      intro y hy
      have hyL : WMLt (lexRel (· ≤ · : PfpTag R P dt.KIx →
          PfpTag R P dt.KIx → Prop) (tupLeLex (A := A) (d := dt.dd)))
          (argIn dt.ko c, u₂) y :=
        ⟨(Wide.tagTupleLe_iff_lexRel _ y).mp ((hord _ y).mp hy.1),
          fun hc => hy.2 ((hord y _).mpr
            ((Wide.tagTupleLe_iff_lexRel y _).mpr hc))⟩
      rcases (wmLt_lexRel_iff isLinOrd_le _ y).mp hyL with hfst | ⟨heq, hsnd⟩
      · exact hfull y.1 hfst y.2
      · have hblk : wmBlk (mV w) (argIn dt.ko c) y.2 := hab₂ y.2 hsnd
        have hthis : mV w (argIn dt.ko c, y.2) := hblk
        have hy1 : y.1 = argIn dt.ko c := heq.symm
        rw [← hy1] at hthis
        exact hthis
    have hcarry : dt.valCarry (mV w) = (argIn dt.ko c, u₂) :=
      valCarry_eq hlin hu₂ hab
    -- the machine's step across the cover
    have hstep' := iterOrd_covers
      (init := (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v))
      (step := fun a q =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (tagBlk (dt.valCarry (mV a)).1)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.roundFX RF hord vi st v mV semOf q a)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
      hwz hnb
    rw [show dt.varFM RF hord vi st v mV semOf fG z = _ from hstep', hcarry]
    -- the previous round's vector and leaf
    have hacc : ∀ i : ℕ, i < dt.ki →
        (dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG w) w)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v)) i ↔
        accCVal (dt.polOf vi) Ps (WMSetLe tupLeLex) i
          (ixBlk (argIn dt.ko) (mV w))) :=
      fun i hi => (hride _ w i).trans (ih i hi)
    have hleaf' : dt.ctlBit PR.one
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG w) w)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v))
        dt.leafC ↔ Ps (ixBlk (argIn dt.ko) (mV w)) :=
      (hleafride _ w).trans (hleaf w)
    -- the vector after the carry store
    have hnew : ∀ i : ℕ, i < dt.ki →
        (dt.readAcc PR.one
          ((dt.varArgsOf PR.zero PR.one vi).storeCarry
            (tagBlk (argIn dt.ko c : PfpTag R P dt.KIx))
            ((dt.varArgsOf PR.zero PR.one vi).postFold
              (dt.roundFX RF hord vi st v mV semOf
                (dt.varFM RF hord vi st v mV semOf fG w) w)
              (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v)) i ↔
        (if i < (c : ℕ) then
            dt.readAcc PR.one
              ((dt.varArgsOf PR.zero PR.one vi).postFold
                (dt.roundFX RF hord vi st v mV semOf
                  (dt.varFM RF hord vi st v mV semOf fG w) w)
                (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v))
              i
          else if i = (c : ℕ) then
            (if dt.polOf vi (c : ℕ) = true then
                dt.readAcc PR.one
                  ((dt.varArgsOf PR.zero PR.one vi).postFold
                    (dt.roundFX RF hord vi st v mV semOf
                      (dt.varFM RF hord vi st v mV semOf fG w) w)
                    (dt.back RF.cell PR.zero PR.one dt.dd0Le
                      (dt.roundSt st (mV w)) v)) (c : ℕ) ∨
                  chainFrom (dt.polOf vi)
                    (dt.readAcc PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.roundFX RF hord vi st v mV semOf
                          (dt.varFM RF hord vi st v mV semOf fG w) w)
                        (dt.back RF.cell PR.zero PR.one dt.dd0Le
                          (dt.roundSt st (mV w)) v)))
                    (dt.ctlBit PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.roundFX RF hord vi st v mV semOf
                          (dt.varFM RF hord vi st v mV semOf fG w) w)
                        (dt.back RF.cell PR.zero PR.one dt.dd0Le
                          (dt.roundSt st (mV w)) v)) dt.leafC)
                    dt.ki ((c : ℕ) + 1)
              else
                dt.readAcc PR.one
                  ((dt.varArgsOf PR.zero PR.one vi).postFold
                    (dt.roundFX RF hord vi st v mV semOf
                      (dt.varFM RF hord vi st v mV semOf fG w) w)
                    (dt.back RF.cell PR.zero PR.one dt.dd0Le
                      (dt.roundSt st (mV w)) v)) (c : ℕ) ∧
                  chainFrom (dt.polOf vi)
                    (dt.readAcc PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.roundFX RF hord vi st v mV semOf
                          (dt.varFM RF hord vi st v mV semOf fG w) w)
                        (dt.back RF.cell PR.zero PR.one dt.dd0Le
                          (dt.roundSt st (mV w)) v)))
                    (dt.ctlBit PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.roundFX RF hord vi st v mV semOf
                          (dt.varFM RF hord vi st v mV semOf fG w) w)
                        (dt.back RF.cell PR.zero PR.one dt.dd0Le
                          (dt.roundSt st (mV w)) v)) dt.leafC)
                    dt.ki ((c : ℕ) + 1))
          else (dt.polOf vi i = false))) := by
      intro i hi
      exact readAcc_carryAcc hzo (dt.polOf vi) (c : ℕ) _
        (show i < dt.naDim by
          have hna : dt.naDim = dt.ki + 1 := rfl
          omega)
    -- the block families around the carry
    have hagree : ∀ i : Fin dt.ki, (i : ℕ) < (c : ℕ) →
        ixBlk (argIn dt.ko) (mV w) i = ixBlk (argIn dt.ko) (mV z) i := by
      intro i hic
      funext b
      exact propext (hbefore (argIn dt.ko i)
        ((kinSeg.mono i c).mpr hic) b).symm
    have htop : ∀ i : Fin dt.ki, (c : ℕ) < (i : ℕ) →
        ∀ b : (Fin dt.dd → A) → Prop,
        WMSetLe tupLeLex b (ixBlk (argIn dt.ko) (mV w) i) :=
      fun i hic b => wmSetLe_of_full hlinV
        (fun x => hfull (argIn dt.ko i) ((kinSeg.mono c i).mpr hic) x) b
    have hbot : ∀ i : Fin dt.ki, (c : ℕ) < (i : ℕ) →
        ∀ b : (Fin dt.dd → A) → Prop,
        WMSetLe tupLeLex (ixBlk (argIn dt.ko) (mV z) i) b :=
      fun i hic b => wmSetLe_of_empty hlinV
        (fun x hx => hafter (argIn dt.ko i)
          ((kinSeg.mono c i).mpr hic) x hx) b
    have hsucc : ∀ b : (Fin dt.dd → A) → Prop,
        WMLt (WMSetLe tupLeLex) b
          (ixBlk (argIn dt.ko) (mV z) ⟨(c : ℕ), c.isLt⟩) ↔
        WMSetLe tupLeLex b (ixBlk (argIn dt.ko) (mV w) ⟨(c : ℕ), c.isLt⟩) :=
      fun b => (wmLt_wmSetLe_iff hlinV b _).trans
        (wmSetLt_iff_of_wmIncr hlinV hstepB b)
    exact accCVal_step (isLinOrd_wmSetLe hlinV) c.isLt hagree htop hbot
      hsucc hacc hleaf' hnew j hj

omit [Finite R] [Finite P] [Finite dt.KIx] in
include hlin hord in
/-- **The machinery's verdict is the inner prefix's value**: at the
exhausted register — every inner block full — the exit fold's bit is the
alternating quantifier prefix over the inner blocks, applied to the
matrix's value. -/
theorem accVerdict_varFM
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : PfpTag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (fG : dt.CtlIx → A)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (mV a))) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) ↔
    altQuantFrom (dt.polOf vi) Ps 0 (ixBlk (argIn dt.ko) (mV aT)) := by
  classical
  have hzo := PR.zero_ne_one
  have hlinV : IsLinOrd (tupLeLex (A := A) (d := dt.dd)) :=
    Wide.isLinOrd_tupLeLex
  -- the accumulators ride through the last round's fold (as in the
  -- invariant)
  have hride : ∀ i : ℕ,
      dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) i ↔
      dt.readAcc PR.one (dt.varFM RF hord vi st v mV semOf fG aT) i := by
    intro i
    have h2 : ∀ jj : Fin dt.naDim,
        dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT
          (dt.accC jj) =
        dt.varFM RF hord vi st v mV semOf fG aT (dt.accC jj) :=
      fun jj => dt.roundCtl_apply_accC RF hord vi (dt.roundSt st (mV aT)) v
        (semOf aT) _ jj
    refine (readAcc_setLeaf _ _ i).trans ?_
    exact exists_congr fun h => by rw [h2 ⟨i, h⟩]
  -- the verdict is the fold from level 0
  have hfold := dt.accVerdict_iff_foldFrom
    (le := WMSetLe (tupLeLex (A := A) (d := dt.dd)))
    (P := Ps) (pol := dt.polOf vi) (v := ixBlk (argIn dt.ko) (mV aT))
    (f := (dt.varArgsOf PR.zero PR.one vi).postFold
      (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT)
      (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v))
    (fun j hj => (hride j).trans
      (readAcc_varFM RF hord vi st hlin  mV semOf hbotV hmV0 hIncr hKin fG
        hleaf aT j hj))
    ((ctlBit_setLeaf hzo _ _).trans (hleaf aT))
  rw [hfold]
  -- the register is full on every inner block
  refine foldFrom_top_of_ix hlinV fun j x => ?_
  exact (hTop (argIn dt.ko j, x)).mpr ⟨j, rfl⟩

/-! ### The leaf, discharged -/

omit [Finite dt.KIx] [LinearOrder ιV] [Finite ιV] in
include hlin in
/-- **A round's leaf is the matrix's realization**: with the round's
semantic pack built by `mkKindSem` from the encoded valuation, the fold's
leaf after the matrix pass is the quantifier-free matrix's value at that
valuation — the concrete form of the invariant's `hleaf` hypothesis. -/
theorem postLeaf_roundFX [LinearOrder (dt.X.Map A)]
    (σ : dt.d.B.Assignment (dt.X.Map A)) (a : ιV)
    (wa : Fin (dt.nOf vi) → dt.X.Map A)
    (hENCa : ∀ j : Fin (dt.nOf vi),
      wmBlk (dt.lvSet (dt.roundSt st (mV a)) vi j)
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
        encMap dt.ly PR.zero PR.one (wa j))
    (hOlda : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      (dt.roundSt st (mV a)).old i
        (dt.stageTgtD PR.zero vi i ts (dt.roundSt st (mV a)) v
          (dt.d.B.arity i)) ↔ σ i fun k => wa (ts k))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (q : dt.CtlIx → A) :
    dt.postLeaf PR.one vi
      (dt.matFs RF hord PR.zero PR.one vi (dt.roundSt st (mV a)) v
        (dt.varArgsOf PR.zero PR.one vi).enterAtomSt
        (fun b => dt.mkKindSem PR.zero PR.one vi (dt.roundSt st (mV a))
          wa hENCa (dt.kindOf vi b)) q (dt.natOf vi)) ↔
    qfValue (dt.matOf vi)
      (fun atm => (matAtom? atm).elim False (MatAtom.holds σ wa)) := by
  refine postLeaf_iff_qfValue fun k => ?_
  exact dt.ctlBit_avC_matFs_holds RF hord PR.zero_ne_one hlin σ wa hENCa hOlda
    hordP _ (fun _ _ _ _ => rfl) q k

omit [Finite dt.KIx] in
include hlin hord in
/-- **One variable's verdict, semantically**: with each round's pack built
by `mkKindSem` from an encoded valuation, the machinery's exit bit at the
exhausted register is the alternating quantifier prefix over the inner
blocks, applied to the quantifier-free matrix's realization. The remaining
interface (`hPs`) is the well-definedness of the matrix's value as a
function of the blocks alone — the encoding layer's obligation. -/
theorem accVerdict_varFM_qfValue [LinearOrder (dt.X.Map A)]
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : PfpTag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (wOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
      Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
      (j : Fin (dt.nOf vi)),
      wmBlk (dt.lvSet (dt.roundSt st (mV a)) vi j)
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
        encMap dt.ly PR.zero PR.one (wOf a hp j))
    (hOld : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
      (i : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      (dt.roundSt st (mV a)).old i
        (dt.stageTgtD PR.zero vi i ts (dt.roundSt st (mV a)) v
          (dt.d.B.arity i)) ↔ σ i fun k => wOf a hp (ts k))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf vi)),
      semOf a hp b = dt.mkKindSem PR.zero PR.one vi (dt.roundSt st (mV a))
        (wOf a hp) (hENC a hp) (dt.kindOf vi b))
    (fG : dt.CtlIx → A) {Ex Al : ιV → Prop}
    (hEx : ∀ a : ιV, dt.ctlBit PR.one
      (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
      dt.existGateC ↔ Ex a)
    (hAll : ∀ a : ιV, dt.ctlBit PR.one
      (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
      dt.allGateC ↔ Al a)
    (hPass : ∀ a : ιV, Ex a → Al a →
      ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
    (hPsPass : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ),
      (Ex a ∧ (Al a → qfValue (dt.matOf vi)
        (fun atm => (matAtom? atm).elim False
          (MatAtom.holds σ (wOf a hp))))) ↔
        Ps (ixBlk (argIn dt.ko) (mV a)))
    (hPsFail : ∀ a : ιV, ¬(Ex a ∧ Al a) →
      (Ex a ↔ Ps (ixBlk (argIn dt.ko) (mV a)))) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) ↔
    altQuantFrom (dt.polOf vi) Ps 0 (ixBlk (argIn dt.ko) (mV aT)) := by
  classical
  have hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
      (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (mV a)) := by
    intro a
    -- the two flags of the round's exit are the inner gates' thread's
    have hExig : dt.ctlBit PR.one
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
        dt.existGateC ↔
        dt.ctlBit PR.one
          (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
            (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi))
          dt.existGateC := by
      rw [show dt.roundFX RF hord vi st v mV semOf
          (dt.varFM RF hord vi st v mV semOf fG a) a =
        dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV a)) v (semOf a)
          (dt.varFM RF hord vi st v mV semOf fG a) from rfl,
        ctlBit, ctlBit,
        dt.roundCtl_apply_roundFlag RF hord (Or.inl rfl) vi (dt.roundSt st (mV a))
          v (semOf a) (dt.varFM RF hord vi st v mV semOf fG a)]
    have hAlig : dt.ctlBit PR.one
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
        dt.allGateC ↔
        dt.ctlBit PR.one
          (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
            (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi))
          dt.allGateC := by
      rw [show dt.roundFX RF hord vi st v mV semOf
          (dt.varFM RF hord vi st v mV semOf fG a) a =
        dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV a)) v (semOf a)
          (dt.varFM RF hord vi st v mV semOf fG a) from rfl,
        ctlBit, ctlBit,
        dt.roundCtl_apply_roundFlag RF hord (Or.inr rfl) vi (dt.roundSt st (mV a))
          v (semOf a) (dt.varFM RF hord vi st v mV semOf fG a)]
    rw [roundLeaf]
    by_cases hEA : Ex a ∧ Al a
    · -- a passing round: the leaf is the matrix's value at its points
      have hp : ∀ ℓ : Fin (dt.nIn vi),
          dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ :=
        hPass a hEA.1 hEA.2
      -- its exit is the matrix thread at the mkKindSem packs
      have hmat : dt.ctlBit PR.one
          (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
            dt.existGateC →
          dt.ctlBit PR.one
            (dt.roundFX RF hord vi st v mV semOf
              (dt.varFM RF hord vi st v mV semOf fG a) a)
            dt.allGateC →
          dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a =
            dt.matFs RF hord PR.zero PR.one vi (dt.roundSt st (mV a)) v
              (dt.varArgsOf PR.zero PR.one vi).enterAtomSt
              (fun b => dt.mkKindSem PR.zero PR.one vi
                (dt.roundSt st (mV a)) (wOf a hp) (hENC a hp)
                (dt.kindOf vi b))
              (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
                (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi))
              (dt.natOf vi) := by
        intro hex hal
        have hsem' : semOf a hp = fun b => dt.mkKindSem PR.zero PR.one vi
            (dt.roundSt st (mV a)) (wOf a hp) (hENC a hp)
            (dt.kindOf vi b) :=
          funext (hsem a hp)
        rw [show dt.roundFX RF hord vi st v mV semOf
            (dt.varFM RF hord vi st v mV semOf fG a) a =
          dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV a)) v (semOf a)
            (dt.varFM RF hord vi st v mV semOf fG a) from rfl,
          dt.roundCtl_of_flags RF hord vi (dt.roundSt st (mV a)) v (semOf a)
            (dt.varFM RF hord vi st v mV semOf fG a) hp (hExig.mp hex)
            (hAlig.mp hal),
          hsem']
      refine Iff.trans ?_ (hPsPass a hp)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(hEx a).mp h1, fun hal => ?_⟩
        have h2' := h2 ((hAll a).mpr hal)
        rw [hmat h1 ((hAll a).mpr hal)] at h2'
        exact (dt.postLeaf_roundFX RF hord vi st hlin mV σ a (wOf a hp)
          (hENC a hp) (hOld a hp) hordP
          (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
            (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi))).mp h2'
      · rintro ⟨h1, h2⟩
        have h1' := (hEx a).mpr h1
        refine ⟨h1', fun hal => ?_⟩
        rw [hmat h1' hal]
        exact (dt.postLeaf_roundFX RF hord vi st hlin mV σ a (wOf a hp)
          (hENC a hp) (hOld a hp) hordP
          (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
            (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi))).mpr
          (h2 ((hAll a).mp hal))
    · -- a failing round: the implication is vacuous, the leaf is the
      -- ∃-flag alone
      refine Iff.trans ?_ (hPsFail a hEA)
      constructor
      · rintro ⟨h1, -⟩
        exact (hEx a).mp h1
      · intro h1
        refine ⟨(hEx a).mpr h1, fun hal => ?_⟩
        exact absurd ⟨h1, (hAll a).mp hal⟩ hEA
  exact accVerdict_varFM RF hord vi st hlin  mV semOf hbotV hmV0 hIncr hKin
    hTop fG hleaf

end Threads

/-! ### The threaded twins of the VAL loop's two threads

A round's exit state is its entry state unless the round's matrix ran a
stage atom, which normalizes SAV and TARGET
(`DescriptiveComplexity.Pfp.PfpData.roundEndSt`). Whether it ran at all is
the gates' verdict, read off the control *entering* the round — so the two
have to be iterated **together**, one pair per round, exactly as the
spine's nodes are one scale up.

What is threaded is not the state but the **two scratch registers**
(`DescriptiveComplexity.Pfp.PfpData.roundEndSt_eq`): every other register
is the machinery's entry state's, definitionally. That is what keeps the
semantic packs available — a pack reads the tape state through the levels'
register sets, i.e. through the mirror and VAL alone, so one family
indexed by the two registers serves every round, and it can actually be
built, which a family over arbitrary states could not be. -/

section ThreadsT

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)

/-- The two registers one round of the VAL loop can change. -/
abbrev Scratch (dt : PfpData L) (A R P : Type) : Type :=
  (Univ A R P dt.KIx dt.dd → Prop) × (Univ A R P dt.KIx dt.dd → Prop)

/-- **The state a round is entered in**: the machinery's entry state with
the round's two scratch registers and the register it enumerates. -/
noncomputable def varRdSt (p : Scratch dt A R P)
    (m : Univ A R P dt.KIx dt.dd → Prop) : TapeStD dt A R P :=
  { st with sav := p.1, tgt := p.2, val := m }

variable (semT : ∀ (p : Scratch dt A R P) (a : ιV),
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.varRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi
      (dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ)) (dt.kindOf vi b))

variable (v) in
/-- **The VAL loop's thread**: the two scratch registers beside the
control, the fold's start at the cleared register, and at each cover the
round's exit — the store taken against the background the round *ends*
in. -/
noncomputable def varPairT (fG : dt.CtlIx → A) :
    ιV → Scratch dt A R P × (dt.CtlIx → A) :=
  iterOrd ((st.sav, st.tgt),
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.varRdSt st (st.sav, st.tgt) (fun _ => False)) v))
    (fun a p =>
      (((dt.roundEndSt RF PR.zero PR.one vi (dt.varRdSt st p.1 (mV a)) v p.2).sav,
        (dt.roundEndSt RF PR.zero PR.one vi (dt.varRdSt st p.1 (mV a)) v p.2).tgt),
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (tagBlk (dt.valCarry (mV a)).1)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.roundCtlT RF hord PR.zero_ne_one vi (dt.varRdSt st p.1 (mV a)) v
              (semT p.1 a) p.2)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le
              (dt.roundEndSt RF PR.zero PR.one vi
                (dt.varRdSt st p.1 (mV a)) v p.2) v))
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.roundEndSt RF PR.zero PR.one vi
              (dt.varRdSt st p.1 (mV a)) v p.2) v)))

variable (v) in
/-- The scratch family of the VAL loop. -/
noncomputable def varSTT (fG : dt.CtlIx → A) (a : ιV) : Scratch dt A R P :=
  (dt.varPairT RF hord vi st v mV semT fG a).1

variable (v) in
/-- The tape family of the VAL loop — the state each round is entered
in. -/
noncomputable def varStT (fG : dt.CtlIx → A) (a : ιV) : TapeStD dt A R P :=
  dt.varRdSt st (dt.varSTT RF hord vi st v mV semT fG a) (mV a)

variable (v) in
/-- The control family of the VAL loop, threaded — the twin of
`DescriptiveComplexity.Pfp.PfpData.varFM`. -/
noncomputable def varFMT (fG : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  (dt.varPairT RF hord vi st v mV semT fG a).2

variable (v) in
/-- **The state one round ends in** — the next round's entry state at a
cover, and the loop's exit state at the top. -/
noncomputable def varStE (fG : dt.CtlIx → A) (a : ιV) : TapeStD dt A R P :=
  dt.roundEndSt RF PR.zero PR.one vi (dt.varStT RF hord vi st v mV semT fG a) v
    (dt.varFMT RF hord vi st v mV semT fG a)

variable (v) in
/-- **The exit control of one VAL round, threaded** — the twin of
`DescriptiveComplexity.Pfp.PfpData.roundFX`, at the state the round's
atoms actually run at. -/
noncomputable def varFXT (fG : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  dt.roundCtlT RF hord PR.zero_ne_one vi (dt.varStT RF hord vi st v mV semT fG a) v
    (semT (dt.varSTT RF hord vi st v mV semT fG a) a)
    (dt.varFMT RF hord vi st v mV semT fG a)

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The registers a round leaves alone ride the whole loop** — by
construction now, since only the two scratch ones are threaded. -/
theorem varStT_fields (fG : dt.CtlIx → A) (a : ιV) :
    (dt.varStT RF hord vi st v mV semT fG a).wk = st.wk ∧
      (dt.varStT RF hord vi st v mV semT fG a).mir = st.mir ∧
      (dt.varStT RF hord vi st v mV semT fG a).bot = st.bot ∧
      (dt.varStT RF hord vi st v mV semT fG a).old = st.old ∧
      (dt.varStT RF hord vi st v mV semT fG a).val = mV a :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- A round leaves the register it was entered with. -/
theorem varStE_val (fG : dt.CtlIx → A) (a : ιV) :
    (dt.varStE RF hord vi st v mV semT fG a).val = mV a :=
  (dt.roundEndSt_fields RF vi (dt.varStT RF hord vi st v mV semT fG a) v
    (dt.varFMT RF hord vi st v mV semT fG a)).2.2.2.1

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The VAL loop never touches a stage track**: only the two scratch
registers are threaded, so the `new` tracks the spine writes ride the
whole loop. -/
theorem varStE_new (fG : dt.CtlIx → A) (a : ιV) :
    (dt.varStE RF hord vi st v mV semT fG a).new = st.new := by
  rw [varStE, dt.roundEndSt_eq RF vi (dt.varStT RF hord vi st v mV semT fG a) v
    (dt.varFMT RF hord vi st v mV semT fG a)]
  rfl

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **A round's exit state is the next round's entry state**, once the
next round's register is written over it. -/
theorem varRdSt_varStE (fG : dt.CtlIx → A) (a : ιV)
    (m : Univ A R P dt.KIx dt.dd → Prop) :
    dt.varRdSt st ((dt.varStE RF hord vi st v mV semT fG a).sav,
        (dt.varStE RF hord vi st v mV semT fG a).tgt) m =
      dt.roundSt (dt.varStE RF hord vi st v mV semT fG a) m := by
  conv_rhs => rw [varStE, dt.roundEndSt_eq RF vi (dt.varStT RF hord vi st v mV semT fG a)
    v (dt.varFMT RF hord vi st v mV semT fG a)]
  rfl

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The thread starts at the entry state. -/
theorem varSTT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.varSTT RF hord vi st v mV semT fG a₀ = (st.sav, st.tgt) :=
  congrArg Prod.fst (iterOrd_bot hbotV)

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The thread starts at the entry state. -/
theorem varStT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.varStT RF hord vi st v mV semT fG a₀ = dt.roundSt st (mV a₀) := by
  rw [varStT, dt.varSTT_bot RF hord vi st mV semT hbotV fG]
  rfl

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The control thread starts at the fold's start. -/
theorem varFMT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.varFMT RF hord vi st v mV semT fG a₀ =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v) :=
  congrArg Prod.snd (iterOrd_bot hbotV)

omit [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The tape's cover equation**: the next round is entered in this
round's exit state, its own register written over it. -/
theorem varStT_covers {a a' : ιV} (hlt : a < a')
    (hnb : ∀ b, ¬(a < b ∧ b < a')) (fG : dt.CtlIx → A) :
    dt.varStT RF hord vi st v mV semT fG a' =
      dt.roundSt (dt.varStE RF hord vi st v mV semT fG a) (mV a') := by
  rw [varStT, show dt.varSTT RF hord vi st v mV semT fG a' = _ from
    congrArg Prod.fst (iterOrd_covers hlt hnb)]
  exact dt.varRdSt_varStE RF hord vi st mV semT fG a (mV a')

omit [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The control's cover equation**: the round's exit control, folded and
stored at the block its increment carried. -/
theorem varFMT_covers {a a' : ιV} (hlt : a < a')
    (hnb : ∀ b, ¬(a < b ∧ b < a')) (fG : dt.CtlIx → A) :
    dt.varFMT RF hord vi st v mV semT fG a' =
      (dt.varArgsOf PR.zero PR.one vi).storeCarry
        (tagBlk (dt.valCarry (mV a)).1)
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.varFXT RF hord vi st v mV semT fG a)
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.varStE RF hord vi st v mV semT fG a) v))
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.varStE RF hord vi st v mV semT fG a) v) :=
  congrArg Prod.snd (iterOrd_covers hlt hnb)

/-! ### The threaded loop is the unthreaded one

The VAL loop's rounds run at states that differ from the machinery's entry
state in SAV and TARGET alone, and every control they compute is blind to
that difference (`DescriptiveComplexity.Pfp.PfpData.roundCtlT_eq_roundCtl`,
`DescriptiveComplexity.Pfp.PfpData.roundCtl_congr_scratch`). What the
threading *can* change is the semantic pack, since a family indexed by the
scratch registers may pick different points at different registers; so the
bridge is stated at a pack that is one unthreaded pack transported
(`semCastT`), which is what a reduction supplies
(`DescriptiveComplexity.Pfp.PfpData.gatedSem`, whose points are the
address's blocks and nothing else). -/

section ThreadBridge

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)
variable (sem₀ : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi (dt.roundSt st (mV a)) (dt.kindOf vi b))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- **A round's entry state is the round state up to the two scratch
registers.** -/
theorem scratchEq_varRdSt (p : Scratch dt A R P)
    (m : Univ A R P dt.KIx dt.dd → Prop) :
    dt.ScratchEq (dt.varRdSt st p m) (dt.roundSt st m) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (v) in
/-- **One unthreaded pack, at every state a round reaches**: the round's own
state and the states its matrix threads all share the mirror and VAL of the
round state, so `kindSemCast` carries the pack to each of them. -/
noncomputable def semCastT (p : Scratch dt A R P) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn vi),
      dt.igPassP RF PR.zero PR.one vi (dt.varRdSt st p (mV a)) ℓ)
    (b : Fin (dt.natOf vi)) :
    dt.KindSem PR.zero PR.one vi
      (dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ)) (dt.kindOf vi b) :=
  dt.kindSemCast (st := dt.roundSt st (mV a))
    (st' := dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ)) PR.zero PR.one vi
    ((dt.scratchEq_matSt (vi := vi) (st := dt.varRdSt st p (mV a)) (v := v)
      (b : ℕ)).2.1).symm
    ((dt.scratchEq_matSt (vi := vi) (st := dt.varRdSt st p (mV a)) (v := v)
      (b : ℕ)).2.2.1).symm
    (dt.kindOf vi b)
    (sem₀ a (fun ℓ => (dt.igPassP_congr RF PR.zero PR.one vi rfl ℓ).mp (hp ℓ)) b)

omit [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder ιV] [Finite ιV] in
/-- **One threaded round is the unthreaded round**: a round's own state is
the round state up to SAV and TARGET, its matrix threads those two further,
and the pack rides along — three transports that compose to none. -/
theorem roundCtlT_semCastT (hreg : ¬∃ u : Univ A R P dt.KIx dt.dd, v = RF.cell u)
    (p : Scratch dt A R P) (a : ιV) (q : dt.CtlIx → A) :
    dt.roundCtlT RF hord PR.zero_ne_one vi (dt.varRdSt st p (mV a)) v
        (dt.semCastT RF vi st v mV sem₀ p a) q =
      dt.roundFX RF hord vi st v mV sem₀ q a := by
  classical
  rw [roundFX, dt.roundCtlT_eq_roundCtl RF hord PR.zero_ne_one hreg vi _ _ _,
    dt.roundCtl_congr_scratch RF hord PR.zero_ne_one
      (dt.scratchEq_varRdSt st p (mV a)) hreg vi _ _]
  congr 1
  funext hp b
  simp only [semCastT]
  exact dt.kindSemCast_triple PR.zero PR.one vi _ _ _ _ _ _ (dt.kindOf vi b)
    (sem₀ a _ b)

omit [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The threaded round of the VAL loop is the unthreaded one**, at the
state the loop's own thread produced. -/
theorem varFXT_eq_roundFX
    (hreg : ¬∃ u : Univ A R P dt.KIx dt.dd, v = RF.cell u)
    (fG : dt.CtlIx → A) (a : ιV) :
    dt.varFXT RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG a =
      dt.roundFX RF hord vi st v mV sem₀
        (dt.varFMT RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG a) a :=
  dt.roundCtlT_semCastT RF hord vi st mV sem₀ hreg
    (dt.varSTT RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG a) a
    (dt.varFMT RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG a)

omit [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The VAL loop's threaded control is its unthreaded control**: round by
round, `varFXT_eq_roundFX`, the backgrounds agreeing because a round's exit
state is the round state up to SAV and TARGET. This is the bridge between
the control the machine's run produces and the control
`DescriptiveComplexity.Pfp.PfpData.accVerdict_leafP` reads. -/
theorem varFMT_eq_varFM
    (hreg : ¬∃ u : Univ A R P dt.KIx dt.dd, v = RF.cell u)
    (fG : dt.CtlIx → A) (a : ιV) :
    dt.varFMT RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG a =
      dt.varFM RF hord vi st v mV sem₀ fG a := by
  classical
  induction a using order_induction with
  | hmin z hz =>
    rw [dt.varFMT_bot RF hord vi st mV (dt.semCastT RF vi st v mV sem₀) hz fG,
      show dt.varFM RF hord vi st v mV sem₀ fG z = _ from iterOrd_bot hz]
  | hstep w z hwz hnb ih =>
    have hSE : dt.ScratchEq
        (dt.varStE RF hord vi st v mV (dt.semCastT RF vi st v mV sem₀) fG w)
        (dt.roundSt st (mV w)) :=
      (dt.scratchEq_roundEndSt RF vi _ v _).trans (dt.scratchEq_varRdSt st _ (mV w))
    rw [dt.varFMT_covers RF hord vi st mV (dt.semCastT RF vi st v mV sem₀) hwz hnb fG,
      show dt.varFM RF hord vi st v mV sem₀ fG z = _ from iterOrd_covers hwz hnb,
      dt.varFXT_eq_roundFX RF hord vi st mV sem₀ hreg fG w, hSE.back hreg, ih]
    rfl

end ThreadBridge

end ThreadsT

section Cap

variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr WMLe (mV a) (mV a'))
variable (hTestT : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (fun u => tagBlk u.1) (mV a) u)
variable (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = v) (htgt : st.tgt = v)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi (dt.roundSt st (mV a)) (dt.kindOf vi b))
variable (semT : ∀ (p : Scratch dt A R P) (a : ιV),
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.varRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi
      (dt.matSt vi (dt.varRdSt st p (mV a)) v (b : ℕ)) (dt.kindOf vi b))
variable (hDom : ∀ ℓ : Fin (dt.arOf vi),
  ExpExpansion.DomHolds (X := dt.X)
    (tOf ℓ, decRho dt.ly PR.zero PR.one
      (wmBlk st.mir
        (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx))))

variable (v) in
/-- **The control the gates leave**, at the reduction's own budgets — what
both forms of the machinery's run start their VAL loop from. -/
noncomputable def varFG (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.gatesFs RF PR.zero PR.one vi st v
    (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    dt.card_le_ntgDim
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (dt.domPk t').n)
      (Finset.mem_univ t)) dt.domDepth_le_eDim)
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
      (Finset.mem_univ t)) dt.domReads_le_nfDim)
    tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt
    ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)

include hrules hR hlin hord htop hbot hwork hv hvi hwkSt hcompatOf hbotV
  htopV hmV0 hIncr hTestT hTestF hmir hbotSt hsav htgt hDom in
/-- **One variable's machinery, fully instantiated**: from the entry
checkpoint at the marker, through the gates at a gated address, the VAL
clear and the rounds of matrix pass, exhaustion test and block-indexed
increment, to the exit checkpoint – the fold spelled by the concrete
threads, every leg the assembled runs of the layers below. -/
theorem varMachine_run
    (hwitOf : ∀ (ℓ : Fin (dt.arOf vi)) (t' : dt.X.Tag),
      wmBlk st.mir
        (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.roundFX RF hord vi st v mV semOf
              (dt.varFM RF hord vi st v mV semOf
                (dt.gatesFs RF PR.zero PR.one vi st v
                  (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
                  dt.card_le_ntgDim
                  (fun t => le_trans (Finset.le_sup
                    (f := fun t' : dt.X.Tag => (dt.domPk t').n)
                    (Finset.mem_univ t)) dt.domDepth_le_eDim)
                  (fun t => le_trans (Finset.le_sup
                    (f := fun t' : dt.X.Tag =>
                      (blkAtoms (dt.domPk t').mat).length)
                    (Finset.mem_univ t)) dt.domReads_le_nfDim)
                  tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt
                  ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
                    (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
                  (dt.arOf vi)) aT) aT)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have htagOf : ∀ ℓ : Fin (dt.arOf vi),
      dt.dspTagOf PR.zero PR.one
        (wmBlk st.mir
          (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)) =
      tOf ℓ :=
    fun ℓ => dspTagOf_eq_of_onehot (hwitOf ℓ)
  -- the gates' final control
  set fG := dt.gatesFs RF PR.zero PR.one vi st v
    (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    dt.card_le_ntgDim
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (dt.domPk t').n)
      (Finset.mem_univ t)) dt.domDepth_le_eDim)
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
      (Finset.mem_univ t)) dt.domReads_le_nfDim)
    tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt
    ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
      (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi) with hfG
  -- the verdict flag holds after the gates
  have hflag : fG dt.gateFlagC = PR.one := by
    rw [hfG]
    have hchar := dt.ctlBit_gateFlagC_gatesFs (st := st) (v := v)
      (bOf := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      (hc := dt.card_le_ntgDim)
      (hnG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (hrdG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      (tOf := tOf)
      (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      RF hzo (fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    refine hchar.mpr ⟨?_, fun ℓ _ => ⟨hwitOf ℓ, hDom ℓ⟩⟩
    change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.gateFlagC True f₀)
      dt.gateFlagC
    exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
  have heq : (WMLe (A := Univ A R P dt.KIx dt.dd)) = tagTupleLe :=
    funext fun x => funext fun y => propext (hord x y)
  refine dt.var_run (laidFile RF hord) (fun i ρ => hrules i ρ) hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord y _).mp (htop y))
    (fun y => (hord _ y).mp (hbot y)) hv hvi
    (dt.varBg_back RF hord hlin  htop st hwkSt)
    (hGatesR := dt.varGates_run RF hord vi st hrules hR hlin htop hbot hv hvi
      hwkSt TestOf hcompatOf tOf htagOf hTestOf
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))
    hflag
    (dt.varBg_back RF hord hlin  htop (dt.roundSt st (fun _ => False)) hwkSt)
    (fun r s hs => dt.back_roundSt_off RF (st := st) _ _ r s hs)
    hbotV htopV hmV0
    (restO := fun a => dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.roundSt st (mV a)))
    (fun a => dt.varBg_back RF hord hlin  htop (dt.roundSt st (mV a)) hwkSt)
    (restM := fun a => dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.roundSt st (mV a)))
    ?_
    (fM := dt.varFM RF hord vi st v mV semOf fG)
    (fX := fun a => dt.roundFX RF hord vi st v mV semOf
      (dt.varFM RF hord vi st v mV semOf fG a) a)
    ?_ (hMatrixR := ?_) (fun a a' h1 h2 =>
      show WMIncr tagTupleLe _ _ from heq ▸ hIncr a a' h1 h2) ?_ ?_ hTestT hTestF
  · -- the first round's background is the cleared one
    exact congrArg (fun m => dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.roundSt st m)) hmV0
  · -- the thread starts at the fold's start
    exact iterOrd_bot hbotV
  · -- backgrounds agree across a cover, off VAL
    intro a a' hlt hnb r s hs
    exact dt.back_roundSt_off RF (st := st) _ _ r s hs
  · -- the store at a cover is the thread's step
    intro a a' hlt hnb u₀ h1 h2
    have hcov := iterOrd_covers
      (init := (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v))
      (step := fun a q =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (tagBlk (dt.valCarry (mV a)).1)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.roundFX RF hord vi st v mV semOf q a)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
      hlt hnb
    rw [show dt.varFM RF hord vi st v mV semOf fG a' = _ from hcov,
      valCarry_eq hlin h1 (fun w hw => h2 w (show WMLt tagTupleLe u₀ w from heq ▸ hw))]
    rfl
  · -- the round, per VAL content: the inner gates, the branch and the
    -- matrix — no semantic hypothesis, so every register the loop
    -- enumerates is covered
    intro a
    exact dt.round_run RF hord vi hrules hR hlin  htop hbot hwork hv hvi
      (dt.roundSt st (mV a)) hwkSt hmir hbotSt hsav htgt (semOf a)
      (dt.varFM RF hord vi st v mV semOf fG a)

include hrules hR hlin hord htop hbot hwork hv hvi hwkSt hcompatOf hbotV
  htopV hmV0 hIncr hTestT hTestF hmir hbotSt hDom in
/-- **One variable's machinery, fully instantiated — threaded**: as
`DescriptiveComplexity.Pfp.PfpData.varMachine_run` with no boundary
discipline assumed, so it applies at every address of a sweep and not
only at the one whose SAV and TARGET the advance happens to have left
behind. The rounds run at the states the thread produces, and the loop
ends in `DescriptiveComplexity.Pfp.PfpData.varStE` at the top, which
differs from the entry state in SAV and TARGET alone. -/
theorem varMachine_run_thread
    (hwitOf : ∀ (ℓ : Fin (dt.arOf vi)) (t' : dt.X.Tag),
      wmBlk st.mir
        (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.varFXT RF hord vi st v mV semT
              (dt.varFG (PR := PR) RF vi st v tOf f₀) aT)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le
              (dt.varStE RF hord vi st v mV semT (dt.varFG (PR := PR) RF vi st v tOf f₀) aT) v))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.varStE RF hord vi st v mV semT (dt.varFG (PR := PR) RF vi st v tOf f₀) aT))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have htagOf : ∀ ℓ : Fin (dt.arOf vi),
      dt.dspTagOf PR.zero PR.one
        (wmBlk st.mir
          (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx)) =
      tOf ℓ :=
    fun ℓ => dspTagOf_eq_of_onehot (hwitOf ℓ)
  set fG := dt.varFG (PR := PR) RF vi st v tOf f₀ with hfG
  -- the verdict flag holds after the gates
  have hflag : fG dt.gateFlagC = PR.one := by
    rw [hfG, varFG]
    have hchar := dt.ctlBit_gateFlagC_gatesFs (st := st) (v := v)
      (bOf := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      (hc := dt.card_le_ntgDim)
      (hnG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (hrdG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      (tOf := tOf)
      (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      RF hzo (fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    refine hchar.mpr ⟨?_, fun ℓ _ => ⟨hwitOf ℓ, hDom ℓ⟩⟩
    change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.gateFlagC True f₀)
      dt.gateFlagC
    exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
  -- the entry state's field equations ride every round's state
  have hwkA : ∀ a : ιV, (dt.varStT RF hord vi st v mV semT fG a).wk = fun r => r = v :=
    fun a => ((dt.varStT_fields RF hord vi st mV semT fG a).1).trans hwkSt
  have hmirA : ∀ a : ιV, (dt.varStT RF hord vi st v mV semT fG a).mir = v :=
    fun a => ((dt.varStT_fields RF hord vi st mV semT fG a).2.1).trans hmir
  have hbotA : ∀ a : ιV, (dt.varStT RF hord vi st v mV semT fG a).bot =
      fun r => r = (fun _ => False) :=
    fun a => ((dt.varStT_fields RF hord vi st mV semT fG a).2.2.1).trans hbotSt
  have hvalE : ∀ a : ιV, (dt.varStE RF hord vi st v mV semT fG a).val = mV a :=
    fun a => dt.varStE_val RF hord vi st mV semT fG a
  have heq : (WMLe (A := Univ A R P dt.KIx dt.dd)) = tagTupleLe :=
    funext fun x => funext fun y => propext (hord x y)
  refine dt.var_run (laidFile RF hord) (fun i ρ => hrules i ρ) hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord y _).mp (htop y))
    (fun y => (hord _ y).mp (hbot y)) hv hvi
    (dt.varBg_back RF hord hlin  htop st hwkSt)
    (hGatesR := dt.varGates_run RF hord vi st hrules hR hlin htop hbot hv hvi
      hwkSt TestOf hcompatOf tOf htagOf hTestOf
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))
    hflag
    (dt.varBg_back RF hord hlin  htop (dt.roundSt st (fun _ => False)) hwkSt)
    (fun r s hs => dt.back_roundSt_off RF (st := st) _ _ r s hs)
    hbotV htopV hmV0
    (restO := fun a => dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.varStE RF hord vi st v mV semT fG a))
    (fun a => (hvalE a) ▸ dt.varBg_back RF hord hlin  htop
      (dt.varStE RF hord vi st v mV semT fG a)
      (((dt.roundEndSt_fields RF vi (dt.varStT RF hord vi st v mV semT fG a) v
        (dt.varFMT RF hord vi st v mV semT fG a)).1).trans (hwkA a)))
    (restM := fun a => dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.varStT RF hord vi st v mV semT fG a))
    ?_
    (fM := dt.varFMT RF hord vi st v mV semT fG)
    (fX := dt.varFXT RF hord vi st v mV semT fG)
    ?_ (hMatrixR := ?_) (fun a a' h1 h2 =>
      show WMIncr tagTupleLe _ _ from heq ▸ hIncr a a' h1 h2) ?_ ?_ hTestT hTestF
  · -- the first round's background is the cleared one
    rw [show dt.varStT RF hord vi st v mV semT fG a₀ = dt.roundSt st (mV a₀) from
      dt.varStT_bot RF hord vi st mV semT hbotV fG, hmV0]
  · -- the thread starts at the fold's start
    exact dt.varFMT_bot RF hord vi st mV semT hbotV fG
  · -- backgrounds agree across a cover, off VAL
    intro a a' hlt hnb r s hs
    rw [show dt.varStT RF hord vi st v mV semT fG a' =
      dt.roundSt (dt.varStE RF hord vi st v mV semT fG a) (mV a') from
      dt.varStT_covers RF hord vi st mV semT hlt hnb fG]
    exact dt.back_roundSt_off RF (st := dt.varStE RF hord vi st v mV semT fG a)
      _ _ r s hs
  · -- the store at a cover is the thread's step
    intro a a' hlt hnb u₀ h1 h2
    rw [show dt.varFMT RF hord vi st v mV semT fG a' = _ from
      dt.varFMT_covers RF hord vi st mV semT hlt hnb fG,
      valCarry_eq hlin h1 (fun w hw => h2 w (show WMLt tagTupleLe u₀ w from heq ▸ hw))]
  · -- the round, at the state the thread produced for it
    intro a
    have hrun := dt.round_run_thread RF hord vi hrules hR hlin  htop hbot hwork hv hvi
      (dt.varStT RF hord vi st v mV semT fG a) (hwkA a) (hmirA a) (hbotA a)
      (semT (dt.varSTT RF hord vi st v mV semT fG a) a)
      (dt.varFMT RF hord vi st v mV semT fG a)
    rw [show (dt.roundEndSt RF PR.zero PR.one vi
        (dt.varStT RF hord vi st v mV semT fG a) v
        (dt.varFMT RF hord vi st v mV semT fG a)).val = mV a from hvalE a] at hrun
    exact hrun

end Cap

end VarCapstone

end VarInst

end PfpData

end Pfp

end DescriptiveComplexity
