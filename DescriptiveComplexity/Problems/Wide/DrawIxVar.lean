/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxRound
import DescriptiveComplexity.Problems.Wide.DrawInstVar

/-!
# One variable's machinery at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawInstVar` read at a coarse file: the
gates' leg and the matrix leg of one variable's machinery, the VAL loop's
thread and the capstone runs. Everything below it is already at the file, so
this is the last layer before the evaluation.
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
-- A register's block is the block of the element it stands for. Free at the
-- elementwise file, where a register *is* an element.
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R P dt.KIx dt.dd} (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section VarInst

variable (vi : dt.VarIx) (st : TapeSt dt A R P I)
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {emb : dt.VarPhF vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.VarSiteF vi, dt.VarShF vi i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : dt.VarSiteF vi) (ρ : dt.VarShF vi i),
  PR.rules (rEmb i ρ) = dt.varRuleF PR.zero PR.one vi
    (dt.varArgsOf PR.zero PR.one vi) emb exitPh i ρ)
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
variable (hwkSt : st.wk = fun r => r = v)
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom under this machinery is priced at.
variable (w wG wP wR wK : ℕ)
variable (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
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
variable (TestOf : Fin (dt.arOf vi) → I → Prop)
variable (hcompatOf : ∀ (ℓ : Fin (dt.arOf vi)) (u : I),
  dt.wellShapedG PR.zero PR.one
    (Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      st.mir (F.cell u)) ↔ TestOf ℓ u)
variable (tOf : Fin (dt.arOf vi) → dt.X.Tag)
variable (htagOf : ∀ ℓ : Fin (dt.arOf vi),
  dt.dspTagOf PR.zero PR.one
    (wmBlk (ixAddr elt st.mir)
      (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)) =
  tOf ℓ)

/-- **What the gates' leg of one variable's machinery is charged**: the
walk-back into the sequence, the gate sequence itself, and the walk-back at
the verdict checkpoint. -/
noncomputable def ixVarGatesCost (dt : Data L) (A : Type) (vi : dt.VarIx)
    (w wP : ℕ) : ℕ :=
  1 + ((dt.ixGateCost A w wP + 2) * dt.arOf vi + 1) + 1

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
omit hord in
/-- **The gates' leg of one variable's machinery**: from the dispatch's
landing one cell right of the marker, the walk-back, the whole gate
sequence at a gated address, and the walk-back at the verdict
checkpoint. -/
theorem ixVarGates_reachesIn (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn (dt.ixVarGatesCost A vi w wP)
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk1)
          (dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hwkv' : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      st.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the walk-back into the gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.gates (.chk 0)) .stay
    exact ⟨rEmb (.gates (.chk 0)) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
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
  have hgates := ixGates_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix)
      (hinj := hinj) (heltP := heltP) (vi := vi) (st := st)
      (bOf := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      (hc := dt.card_le_ntgDim)
      (hnG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (hrdG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellGOf)
      (setFail := (dt.varArgsOf PR.zero PR.one vi).setFail)
      (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      (hrules := hgrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap) (w := w)
      (wP := wP) (hwP := hwP) (hcostR := hcostR)
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf)
      (hTestOf := hTestOf) (f₀ := f₀)
  -- the walk-back at the verdict checkpoint
  refine ((TMData.reachesIn_of_step hback).trans hgates).tail ?_
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  have h := hrules .vchk1 .stay
  exact ⟨rEmb .vchk1 .stay, by rw [h]; exact hwkv',
    by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
    fun hc => (by rw [h] at hc; exact hc)⟩

/-- **The control after a failing gate sequence**: the fail store at the
failing block's entry, the flag clear. -/
noncomputable def ixFailCtl (ℓ₀ : Fin (dt.arOf vi)) (f₀ : dt.CtlIx → A) :
    dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one vi).setFail
    ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt ℓ₀
      (dt.ixGatesFs F PR.zero PR.one hhasP vi st v
        (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
        dt.card_le_ntgDim
        (fun t => le_trans (Finset.le_sup
          (f := fun t' : dt.X.Tag => (dt.domPk t').n)
          (Finset.mem_univ t)) dt.domDepth_le_eDim)
        (fun t => le_trans (Finset.le_sup
          (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
          (Finset.mem_univ t)) dt.domReads_le_nfDim)
        tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt f₀ (ℓ₀ : ℕ))
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
omit hord in
/-- **The gates' leg at a junk address**: the walk-back, the passing
prefix, the failing block, and the walk-back at the verdict checkpoint —
the fail store applied, the flag clear. -/
theorem ixVarGatesFail_reachesIn (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : I} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn (dt.ixVarGatesCost A vi w wP)
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk1)
          (dt.ixFailCtl (PR := PR) (v := v) F hhasP vi st tOf ℓ₀ f₀)), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkS : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [ixBack_wk, hwkSt]
  have hwkv' : PR.passTracksAt F.cell Slot.val (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      st.val v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwkS, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  -- the walk-back into the gates' first checkpoint
  have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.gatesP (.chk 0))) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules (.gates (.chk 0)) .stay
    exact ⟨rEmb (.gates (.chk 0)) .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩
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
  have hgates := ixGates_reachesIn_fail (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix)
      (hinj := hinj) (heltP := heltP) (vi := vi) (st := st)
      (bOf := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
      (hc := dt.card_le_ntgDim)
      (hnG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (hrdG := fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      (wellGOf := (dt.varArgsOf PR.zero PR.one vi).wellGOf)
      (setFail := (dt.varArgsOf PR.zero PR.one vi).setFail)
      (enterSt := (dt.varArgsOf PR.zero PR.one vi).enterBlockSt)
      (hrules := hgrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap) (w := w)
      (wP := wP) (hwP := hwP) (hcostR := hcostR)
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf)
      (ℓ₀ := ℓ₀) (hTestLt := hTestLt) (hfail := hfail) (f₀ := f₀)
  -- the walk-back at the verdict checkpoint
  refine TMData.ReachesIn.mono ?_
    (((TMData.reachesIn_of_step hback).trans hgates).tail ?_)
  · simp only [ixVarGatesCost]
    have h2 : (dt.ixGateCost A w wP + 2) * ((ℓ₀ : ℕ) + 1) ≤
        (dt.ixGateCost A w wP + 2) * dt.arOf vi :=
      Nat.mul_le_mul_left _ ℓ₀.isLt
    rw [Nat.mul_succ] at h2
    have h3 : wP ≤ dt.ixGateCost A w wP := by
      simp only [ixGateCost]
      omega
    omega
  · refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    have h := hrules .vchk1 .stay
    exact ⟨rEmb .vchk1 .stay, by rw [h]; exact hwkv',
      by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl, by rw [h]; rfl,
      fun hc => (by rw [h] at hc; exact hc)⟩

omit [Nonempty A] [L.IsRelational] [L.Structure A] [Finite A] [Finite R] [Finite P]
  [Finite dt.KIx] hrules hR hv hwkSt in
omit [Finite I] in
include hix htop in
/-- **The background bundle, discharged at a boundary state**: the five
slot equations `DescriptiveComplexity.Draw.Data.var_run`'s kits read are
definitional in `DescriptiveComplexity.Draw.Data.back`, given the marker
and the order facts. -/
theorem ixVarBg_back (stV : TapeSt dt A R P I)
    (hwkV : stV.wk = fun r => r = v) :
    dt.VarBg F PR.zero PR.one v gtop
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stV) stV.val := by
  refine ⟨fun r => ?_, fun r => rfl,
    fun r => dt.ixBack_regLast hix htop r,
    fun u b => dt.ixBack_blk_cell (F.toIxFile.injective hix) u b, fun r => rfl⟩
  rw [ixBack_wk, hwkV]

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
omit hord in
/-- **The whole machinery at a junk address**: entry, the failing gates,
and the verdict checkpoint's clear flag routing straight to the exit with
the stage slot erased — the VAL loop never entered. -/
theorem ixVarMachineFail_reachesIn (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : I} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A)
    {rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hoff : ∀ r, r ≠ v → rest' r = dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r)
    (hupd : rest' v = Function.update
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)
      (dt.varArgsOf PR.zero PR.one vi).newSlot PR.zero) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (1 + dt.ixVarGatesCost A vi w wP + 1)
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixFailCtl (PR := PR) (v := v) F hhasP vi st tOf ℓ₀
            ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val rest' st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hns : (dt.varArgsOf PR.zero PR.one vi).newSlot ≠ Slot.val := by
    rcases vi with _ | i <;> exact fun h => nomatch h
  have hflagF : dt.ixFailCtl (PR := PR) (v := v) F hhasP vi st tOf ℓ₀
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
      (dt.varArgsOf PR.zero PR.one vi).gateFlag ≠ PR.one := by
    intro hc
    have hc' : dt.ctlBit PR.one
        (dt.setCtl PR.zero PR.one dt.gateFlagC False
          ((dt.varArgsOf PR.zero PR.one vi).enterBlockSt ℓ₀
            (dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (ℓ₀ : ℕ))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
        dt.gateFlagC := hc
    exact (ctlBit_setCtl_self hzo _ _ _).mp hc'
  exact dt.var_reachesIn_fail F (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (ixVarBg_back (F := F) (hix := hix) (htop := htop)
      (v := v) (stV := st) (hwkV := hwkSt))
    (wG := dt.ixVarGatesCost A vi w wP)
    (hGates := ixVarGatesFail_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix)
      (hinj := hinj) (heltP := heltP) (vi := vi) (st := st)
      (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap) (w := w)
      (wP := wP) (hwP := hwP) (hcostR := hcostR) (TestOf := TestOf)
      (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf) (ℓ₀ := ℓ₀)
      (hTestLt := hTestLt) (hfail := hfail)
      (f₀ := (dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
    hflagF hns hoff hupd

/-- **The control after a completed but failing gate sequence**: the whole
gates' thread — every block's file test passed and every block's machinery
ran — with the flag clear because some block encoded no point. -/
noncomputable def ixUngatedCtl (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.ixGatesFs F PR.zero PR.one hhasP vi st v
    (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ))
    dt.card_le_ntgDim
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (dt.domPk t').n)
      (Finset.mem_univ t)) dt.domDepth_le_eDim)
    (fun t => le_trans (Finset.le_sup
      (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
      (Finset.mem_univ t)) dt.domReads_le_nfDim)
    tOf (dt.varArgsOf PR.zero PR.one vi).enterBlockSt f₀ (dt.arOf vi)

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hv hvi hwkSt
  hcompatOf htagOf hgap hwP hcostR in
omit hord in
/-- **The whole machinery at a shaped but ungated address**: every block
passes its file test — the total dispatch carries each block's machinery
through — but some block encodes no point, its witness not one-hot at the
dispatched tag or its domain sentence failing. The gates complete with the
flag clear, and the verdict checkpoint routes straight to the exit with
the stage slot erased — the VAL loop never entered. The third landing an
arbitrary address makes, beside the gated and the shape-failing ones. -/
theorem ixVarMachineUngated_reachesIn (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (ℓ₀ : Fin (dt.arOf vi))
    (hbad : ¬((∀ t' : dt.X.Tag,
        wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko vi) ℓ₀) :
            Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)
          (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ₀) ∧
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ₀, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko vi) ℓ₀) :
              Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)))))
    (f₀ : dt.CtlIx → A)
    {rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hoff : ∀ r, r ≠ v → rest' r = dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r)
    (hupd : rest' v = Function.update
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)
      (dt.varArgsOf PR.zero PR.one vi).newSlot PR.zero) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (1 + dt.ixVarGatesCost A vi w wP + 1)
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.ixUngatedCtl (PR := PR) (v := v) F hhasP vi st tOf
            ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val rest' st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hns : (dt.varArgsOf PR.zero PR.one vi).newSlot ≠ Slot.val := by
    rcases vi with _ | i <;> exact fun h => nomatch h
  have hflagF : dt.ixUngatedCtl (PR := PR) (v := v) F hhasP vi st tOf
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
      (dt.varArgsOf PR.zero PR.one vi).gateFlag ≠ PR.one := by
    intro hcx
    have hchar := dt.ctlBit_gateFlagC_ixGatesFs (st := st) (v := v)
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
      (F := F) (hhasP := hhasP) (hinj := hinj) (heltP := heltP) (hzo := hzo)
      (hEnter := fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    have hcx' : dt.ctlBit PR.one
        (dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
          (dt.arOf vi)) dt.gateFlagC := hcx
    exact hbad ((hchar.mp hcx').2 ℓ₀ ℓ₀.isLt)
  exact dt.var_reachesIn_fail F (fun i ρ => hrules i ρ) hR hlin hix hbot hv hvi
    (ixVarBg_back (F := F) (hix := hix) (htop := htop)
      (v := v) (stV := st) (hwkV := hwkSt))
    (wG := dt.ixVarGatesCost A vi w wP)
    (hGates := ixVarGates_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (vi := vi)
      (st := st) (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap)
      (w := w) (wP := wP) (hwP := hwP) (hcostR := hcostR)
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf)
      (hTestOf := hTestOf)
      (f₀ := (dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
    hflagF hns hoff hupd

/-! ### The whole variable machinery, run -/

/-- **What one variable's machinery is charged**: the gates' leg, one round,
the three sweeps of the entry and the exhaustion test, and then one round and
two sweeps per VAL content the loop enumerates. -/
noncomputable def ixVarCost (dt : Data L) (A : Type) (vi : dt.VarIx)
    (w wP wR wK n : ℕ) : ℕ :=
  dt.ixVarGatesCost A vi w wP + dt.ixRoundCost A vi w wP wR wK + 3 * wP + 6 +
    (2 * wP + dt.ixRoundCost A vi w wP wR wK + 3) * n

section VarCapstone

/-- **The state of one VAL-loop round**: the entry state with the round's
VAL content. -/
noncomputable def ixRoundSt (m : I → Prop) :
    TapeSt dt A R P I :=
  { st with val := m }

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational]
  [Finite dt.KIx] in
omit [Finite I] in
/-- **Two round states at the same register ask the same pass.** -/
theorem ixIGPassP_roundSt (zero one : A) (vi : dt.VarIx)
    (st st' : TapeSt dt A R P I)
    (m : I → Prop)
    (ℓ : Fin (dt.nIn vi)) :
    dt.ixIGPassP (elt := elt) F zero one vi (dt.ixRoundSt st m) ℓ ↔
      dt.ixIGPassP (elt := elt) F zero one vi (dt.ixRoundSt st' m) ℓ :=
  dt.ixIGPassP_congr (elt := elt) F zero one vi rfl ℓ

variable {dt}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
/-- A state written with the register it already holds is itself. -/
theorem ixRoundSt_val (stV : TapeSt dt A R P I) : dt.ixRoundSt stV stV.val = stV :=
  rfl

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
/-- Two round states' backgrounds agree off the VAL slot. -/
theorem ixBack_roundSt_off {zero one : A}
    (m₁ m₂ : I → Prop)
    (r : Univ A R P dt.KIx dt.dd → Prop) (s : dt.SlotIx)
    (hs : s ≠ Slot.val) :
    dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixRoundSt st m₁) r s =
      dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixRoundSt st m₂) r s := by
  match s with
  | .val => exact absurd rfl hs
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .tgt | .wk | .bot | .ltp | .old _ | .new _ => rfl

variable (dt) in
open Classical in
/-- **The carry of a VAL round at a coarse file**: the greatest register the
mark is clear at, every register above it set – what the increment's landing
phase names. A file need not have one (an empty file has none), so this is an
`Option`; at the elementwise file it is always `some`. -/
noncomputable def ixValCarry (m : I → Prop) : Option I :=
  if h : ∃ u : I, ¬m u ∧ ∀ w, WMLt F.le u w → m w then some h.choose
  else none

variable (dt) in
/-- **The block the carry lies in**: what a round's store is indexed by. -/
noncomputable def ixCarryBlk (m : I → Prop) : Option dt.KIx :=
  (dt.ixValCarry F m).bind F.blk

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P]
  [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] [Nonempty A] in
/-- The carry is unique, so the chosen one is the hypothesis's. -/
theorem ixValCarry_eq (hix : IsLinOrd F.le)
    {m : I → Prop} {u₀ : I} (h1 : ¬m u₀) (h2 : ∀ w, WMLt F.le u₀ w → m w) :
    dt.ixValCarry F m = some u₀ := by
  classical
  have hex : ∃ u : I, ¬m u ∧ ∀ w, WMLt F.le u w → m w := ⟨u₀, h1, h2⟩
  rw [ixValCarry, dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  refine congrArg some ?_
  by_contra hne
  rcases hix.2.2.2 hex.choose u₀ with hle | hle
  · exact h1 (hc2 _ ⟨hle, fun hc => hne (hix.2.2.1 _ _ hle hc)⟩)
  · exact hc1 (h2 _ ⟨hle, fun hc => hne (hix.2.2.1 _ _ hc hle)⟩)

section Threads

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi (dt.ixRoundSt st (mV a)) elt (dt.kindOf vi b))

variable (v) in
/-- **The exit control of one VAL round**, at an entry control: the inner
gates' thread over the round's register, then — at a passing round only,
both flags set — the matrix thread on its output. -/
noncomputable def ixRoundFX (q : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  dt.ixRoundCtl (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a)) v (semOf a) q

variable (v) in
/-- **The VAL loop's entry-control thread**: the fold's start at the
cleared register, each round the matrix pass folded and stored at the
carry's block. -/
noncomputable def ixVarFM (fG : dt.CtlIx → A) : ιV → dt.CtlIx → A :=
  iterOrd ((dt.varArgsOf PR.zero PR.one vi).initSt fG
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        (dt.ixRoundSt st (fun _ => False)) v))
    (fun a q =>
      (dt.varArgsOf PR.zero PR.one vi).storeCarry
        (dt.ixCarryBlk F (mV a))
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))

/-! ### The fold invariant of the VAL loop -/

omit [Fintype dt.SlotIx] [Finite dt.KIx] in
omit [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A machine-order increment is a block-major one, through the reduction's
order characterization. -/
private theorem ixWmIncr_lexRel_of_wmLe
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {s t : Univ A R P dt.KIx dt.dd → Prop} (hi : WMIncr WMLe s t) :
    WMIncr (lexRel (· ≤ · : Tag R P dt.KIx → Tag R P dt.KIx → Prop)
      (tupLeLex (A := A) (d := dt.dd))) s t := by
  obtain ⟨u, hu, hab, ht⟩ := hi
  have hLt : ∀ x y : Univ A R P dt.KIx dt.dd,
      WMLt (lexRel (· ≤ · : Tag R P dt.KIx → Tag R P dt.KIx → Prop)
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

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] in
include hlin hord hinj hix hmono hup hblkP in
/-- **The VAL loop maintains the fold's contributions**: at every round of
the enumeration, the accumulator vector of the control thread reads the
`accCVal` contributions of the inner quantifier prefix at the blocks of the
register's **address** — the invariant that turns the machinery's exit
verdict into the prefix's value. -/
theorem ixReadAcc_varFM
    {a₀ : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (fG : dt.CtlIx → A)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV a))))
    (a : ιV) (j : ℕ) (hj : j < dt.ki) :
    dt.readAcc PR.one (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) j ↔
      accCVal (dt.polOf vi) Ps (WMSetLe tupLeLex) j
        (ixBlk (argIn dt.ko) (ixAddr elt (mV a))) := by
  classical
  have hzo := PR.zero_ne_one
  have hlinV : IsLinOrd (tupLeLex (A := A) (d := dt.dd)) :=
    Wide.isLinOrd_tupLeLex
  -- the accumulators ride through a round's matrix pass and its fold
  have hride : ∀ (q : dt.CtlIx → A) (a' : ιV) (i : ℕ),
      dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a')
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a')) v)) i ↔
      dt.readAcc PR.one q i := by
    intro q a' i
    have h2 : ∀ jj : Fin dt.naDim,
        dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf q a' (dt.accC jj) = q (dt.accC jj) :=
      fun jj => dt.ixRoundCtl_apply_accC (elt := elt) F (hhas := hhasP) (hinj := hinj)
        (helt := heltP) (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a')) v
        (semOf a') q jj
    have h1 : dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a')
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a')) v)) i ↔
        dt.readAcc PR.one (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a') i :=
      readAcc_setLeaf _ _ i
    rw [h1]
    exact exists_congr fun h => by rw [h2 ⟨i, h⟩]
  -- the leaf after a round's fold is the matrix's value there
  have hleafride : ∀ (q : dt.CtlIx → A) (a' : ιV),
      dt.ctlBit PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a')
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a')) v))
        dt.leafC ↔
      dt.roundLeaf (PR := PR) vi (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf q a') :=
    fun q a' => ctlBit_setLeaf hzo _ _
  induction a using order_induction generalizing j hj with
  | hmin z hz =>
    have hz0 : mV z = fun _ => False := by
      have hza : z = a₀ := le_antisymm (hz a₀) (hbotV z)
      rw [hza, hmV0]
    rw [show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG z =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v) from iterOrd_bot hz]
    have hjna : j < dt.naDim := by
      have hna : dt.naDim = dt.ki + 1 := rfl
      omega
    have hread : dt.readAcc PR.one
        ((dt.varArgsOf PR.zero PR.one vi).initSt fG
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt st (fun _ => False)) v)) j ↔
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
    rw [hread, hz0, ixAddr_empty]
    exact (accCVal_bot (fun i b => wmSetLe_of_empty hlinV
      (fun w hw => hw) b) j).symm
  | hstep w z hwz hnb ih =>
    -- the cover of the marks, and the cover of the addresses they stand for
    have hcovM : WMIncr F.le (mV w) (mV z) :=
      hIncr w z hwz (fun b hb => hnb b hb)
    obtain ⟨uc, hnuc, habovec, hnextc⟩ := id hcovM
    have hUc : Use uc := hUse z uc ((hnextc uc).mpr (Or.inl rfl))
    have hcov : WMIncr WMLe (ixAddr elt (mV w)) (ixAddr elt (mV z)) :=
      wmIncr_ixAddr hinj hmono hup (hUse z) hcovM
    obtain ⟨τ, hfull, hstepB, hbefore, hafter⟩ :=
      (wmIncr_lexRel_iff isLinOrd_le (ixAddr elt (mV w)) (ixAddr elt (mV z))).mp
        (ixWmIncr_lexRel_of_wmLe hord hcov)
    -- the carry tag is an inner block
    obtain ⟨u₂, hu₂, hab₂, htz⟩ := id hstepB
    have hmem : ixAddr elt (mV z) (τ, u₂) := (htz u₂).mpr (Or.inl rfl)
    obtain ⟨c, rfl⟩ := hKin z τ u₂ hmem
    -- the carry element is the register's chosen one
    have hab : ∀ y : Univ A R P dt.KIx dt.dd,
        WMLt WMLe (argIn dt.ko c, u₂) y → ixAddr elt (mV w) y := by
      intro y hy
      have hyL : WMLt (lexRel (· ≤ · : Tag R P dt.KIx →
          Tag R P dt.KIx → Prop) (tupLeLex (A := A) (d := dt.dd)))
          (argIn dt.ko c, u₂) y :=
        ⟨(Wide.tagTupleLe_iff_lexRel _ y).mp ((hord _ y).mp hy.1),
          fun hc => hy.2 ((hord y _).mpr
            ((Wide.tagTupleLe_iff_lexRel y _).mpr hc))⟩
      rcases (wmLt_lexRel_iff isLinOrd_le _ y).mp hyL with hfst | ⟨heq, hsnd⟩
      · exact hfull y.1 hfst y.2
      · have hblk : wmBlk (ixAddr elt (mV w)) (argIn dt.ko c) y.2 := hab₂ y.2 hsnd
        have hthis : ixAddr elt (mV w) (argIn dt.ko c, y.2) := hblk
        have hy1 : y.1 = argIn dt.ko c := heq.symm
        rw [← hy1] at hthis
        exact hthis
    -- the register the machine stores at is the one the addresses' carry names
    have hcarryReg : dt.ixValCarry F (mV w) = some uc :=
      dt.ixValCarry_eq F hix hnuc habovec
    have hcarry : elt uc = (argIn dt.ko c, u₂) := by
      have h1 : dt.valCarry (ixAddr elt (mV w)) = (argIn dt.ko c, u₂) :=
        valCarry_eq hlin hu₂ hab
      have h2 : dt.valCarry (ixAddr elt (mV w)) = elt uc := by
        refine valCarry_eq hlin ?_ ?_
        · rw [ixAddr_elt hinj]; exact hnuc
        · intro y hy
          obtain ⟨u', hu', rfl⟩ := hup uc y hUc hy
          rw [ixAddr_elt hinj]
          exact habovec u' ((hmono uc u').mpr hy)
      exact h2.symm.trans h1
    have hblkc : dt.ixCarryBlk F (mV w) =
        tagBlk (argIn dt.ko c : Tag R P dt.KIx) := by
      rw [ixCarryBlk, hcarryReg, show (some uc).bind F.blk = F.blk uc from rfl,
        hblkP uc, hcarry]
    -- the machine's step across the cover
    have hstep' := iterOrd_covers
      (init := (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v))
      (step := fun a q =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (dt.ixCarryBlk F (mV a))
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
      hwz hnb
    rw [show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG z = _
      from hstep', hblkc]
    -- the previous round's vector and leaf
    have hacc : ∀ i : ℕ, i < dt.ki →
        (dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v)) i ↔
        accCVal (dt.polOf vi) Ps (WMSetLe tupLeLex) i
          (ixBlk (argIn dt.ko) (ixAddr elt (mV w)))) :=
      fun i hi => (hride _ w i).trans (ih i hi)
    have hleaf' : dt.ctlBit PR.one
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v))
        dt.leafC ↔ Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV w))) :=
      (hleafride _ w).trans (hleaf w)
    -- the vector after the carry store
    have hnew : ∀ i : ℕ, i < dt.ki →
        (dt.readAcc PR.one
          ((dt.varArgsOf PR.zero PR.one vi).storeCarry
            (tagBlk (argIn dt.ko c : Tag R P dt.KIx))
            ((dt.varArgsOf PR.zero PR.one vi).postFold
              (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v)) i ↔
        (if i < (c : ℕ) then
            dt.readAcc PR.one
              ((dt.varArgsOf PR.zero PR.one vi).postFold
                (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                  (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v))
              i
          else if i = (c : ℕ) then
            (if dt.polOf vi (c : ℕ) = true then
                dt.readAcc PR.one
                  ((dt.varArgsOf PR.zero PR.one vi).postFold
                    (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                      (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                      (dt.ixRoundSt st (mV w)) v)) (c : ℕ) ∨
                  chainFrom (dt.polOf vi)
                    (dt.readAcc PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                          (dt.ixRoundSt st (mV w)) v)))
                    (dt.ctlBit PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                          (dt.ixRoundSt st (mV w)) v)) dt.leafC)
                    dt.ki ((c : ℕ) + 1)
              else
                dt.readAcc PR.one
                  ((dt.varArgsOf PR.zero PR.one vi).postFold
                    (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                      (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                      (dt.ixRoundSt st (mV w)) v)) (c : ℕ) ∧
                  chainFrom (dt.polOf vi)
                    (dt.readAcc PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                          (dt.ixRoundSt st (mV w)) v)))
                    (dt.ctlBit PR.one
                      ((dt.varArgsOf PR.zero PR.one vi).postFold
                        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
                          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG w) w)
                        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                          (dt.ixRoundSt st (mV w)) v)) dt.leafC)
                    dt.ki ((c : ℕ) + 1))
          else (dt.polOf vi i = false))) := by
      intro i hi
      exact readAcc_carryAcc hzo (dt.polOf vi) (c : ℕ) _
        (show i < dt.naDim by
          have hna : dt.naDim = dt.ki + 1 := rfl
          omega)
    -- the block families around the carry
    have hagree : ∀ i : Fin dt.ki, (i : ℕ) < (c : ℕ) →
        ixBlk (argIn dt.ko) (ixAddr elt (mV w)) i = ixBlk (argIn dt.ko) (ixAddr elt (mV z)) i := by
      intro i hic
      funext b
      exact propext (hbefore (argIn dt.ko i)
        ((kinSeg.mono i c).mpr hic) b).symm
    have htop : ∀ i : Fin dt.ki, (c : ℕ) < (i : ℕ) →
        ∀ b : (Fin dt.dd → A) → Prop,
        WMSetLe tupLeLex b (ixBlk (argIn dt.ko) (ixAddr elt (mV w)) i) :=
      fun i hic b => wmSetLe_of_full hlinV
        (fun x => hfull (argIn dt.ko i) ((kinSeg.mono c i).mpr hic) x) b
    have hbot : ∀ i : Fin dt.ki, (c : ℕ) < (i : ℕ) →
        ∀ b : (Fin dt.dd → A) → Prop,
        WMSetLe tupLeLex (ixBlk (argIn dt.ko) (ixAddr elt (mV z)) i) b :=
      fun i hic b => wmSetLe_of_empty hlinV
        (fun x hx => hafter (argIn dt.ko i)
          ((kinSeg.mono c i).mpr hic) x hx) b
    have hsucc : ∀ b : (Fin dt.dd → A) → Prop,
        WMLt (WMSetLe tupLeLex) b
          (ixBlk (argIn dt.ko) (ixAddr elt (mV z)) ⟨(c : ℕ), c.isLt⟩) ↔
        WMSetLe tupLeLex b (ixBlk (argIn dt.ko) (ixAddr elt (mV w)) ⟨(c : ℕ), c.isLt⟩) :=
      fun b => (wmLt_wmSetLe_iff hlinV b _).trans
        (wmSetLt_iff_of_wmIncr hlinV hstepB b)
    exact accCVal_step (isLinOrd_wmSetLe hlinV) c.isLt hagree htop hbot
      hsucc hacc hleaf' hnew j hj

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] in
include hlin hord hinj hix hmono hup hblkP in
/-- **The machinery's verdict is the inner prefix's value**: at the
exhausted register — every inner block full — the exit fold's bit is the
alternating quantifier prefix over the inner blocks, applied to the
matrix's value. -/
theorem ixAccVerdict_varFM
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (fG : dt.CtlIx → A)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV a)))) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) ↔
    altQuantFrom (dt.polOf vi) Ps 0 (ixBlk (argIn dt.ko) (ixAddr elt (mV aT))) := by
  classical
  have hzo := PR.zero_ne_one
  have hlinV : IsLinOrd (tupLeLex (A := A) (d := dt.dd)) :=
    Wide.isLinOrd_tupLeLex
  -- the accumulators ride through the last round's fold (as in the
  -- invariant)
  have hride : ∀ i : ℕ,
      dt.readAcc PR.one ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) i ↔
      dt.readAcc PR.one (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) i := by
    intro i
    have h2 : ∀ jj : Fin dt.naDim,
        dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT
          (dt.accC jj) =
        dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT (dt.accC jj) :=
      fun jj => dt.ixRoundCtl_apply_accC (elt := elt) F (hhas := hhasP) (hinj := hinj)
        (helt := heltP) (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV aT)) v
        (semOf aT) _ jj
    refine (readAcc_setLeaf _ _ i).trans ?_
    exact exists_congr fun h => by rw [h2 ⟨i, h⟩]
  -- the verdict is the fold from level 0
  have hfold := dt.accVerdict_iff_foldFrom
    (le := WMSetLe (tupLeLex (A := A) (d := dt.dd)))
    (P := Ps) (pol := dt.polOf vi) (v := ixBlk (argIn dt.ko) (ixAddr elt (mV aT)))
    (f := (dt.varArgsOf PR.zero PR.one vi).postFold
      (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT)
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v))
    (fun j hj => (hride j).trans
      (ixReadAcc_varFM (F := F) (hinj := hinj) (hhasP := hhasP) (heltP := heltP)
        (hix := hix) (hblkP := hblkP) (hord := hord) (hlin := hlin) (hmono := hmono)
        (hup := hup) (vi := vi) (st := st) (v := v) (mV := mV) (semOf := semOf)
        (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
        (hKin := hKin) (fG := fG) (hleaf := hleaf) (a := aT) (j := j) (hj := hj)))
    ((ctlBit_setLeaf hzo _ _).trans (hleaf aT))
  rw [hfold]
  -- the register is full on every inner block
  refine foldFrom_top_of_ix hlinV fun j x => ?_
  exact (hTop (argIn dt.ko j, x)).mpr ⟨j, rfl⟩

/-! ### The leaf, discharged -/

omit [Finite I] [Finite dt.KIx] [LinearOrder ιV] [Finite ιV] in
include hlin hinj heltP in
/-- **A round's leaf is the matrix's realization**: with the round's
semantic pack built by `ixMkKindSem` from the encoded valuation, the fold's
leaf after the matrix pass is the quantifier-free matrix's value at that
valuation — the concrete form of the invariant's `hleaf` hypothesis. -/
theorem ixPostLeaf_roundFX [LinearOrder (dt.X.Map A)]
    (σ : dt.d.B.Assignment (dt.X.Map A)) (a : ιV)
    (wa : Fin (dt.nOf vi) → dt.X.Map A)
    (hENCa : ∀ j : Fin (dt.nOf vi),
      wmBlk (ixAddr elt (dt.lvSet (dt.ixRoundSt st (mV a)) vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly PR.zero PR.one (wa j))
    (hOlda : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      (dt.ixRoundSt st (mV a)).old i
        (ixAddr elt (dt.ixStageTgt F hhasP vi ts
          { dt.ixRoundSt st (mV a) with sav := ixMark elt v }
          (dt.d.B.arity i))) ↔ σ i fun k => wa (ts k))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (q : dt.CtlIx → A) :
    dt.postLeaf PR.one vi
      (dt.ixMatFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
        (dt.varArgsOf PR.zero PR.one vi).enterAtomSt
        (fun b => dt.ixMkKindSem (elt := elt) PR.zero PR.one vi (dt.ixRoundSt st (mV a))
          wa hENCa (dt.kindOf vi b)) q (dt.natOf vi)) ↔
    qfValue (dt.matOf vi)
      (fun atm => (matAtom? atm).elim False (MatAtom.holds σ wa)) := by
  refine postLeaf_iff_qfValue fun k => ?_
  exact ctlBit_avC_ixMatFs_holds (F := F) (hhas := hhasP) (hinj := hinj)
    (helt := heltP) (hzo := PR.zero_ne_one) (hlin := hlin) (σ := σ) (w := wa)
    (hENC := hENCa) (hOld := hOlda) (hordP := hordP) (enterSt := _)
    (hEnterAv := fun _ _ _ _ => rfl) (f₀ := q) (a := k)

omit [Finite I] [Finite dt.KIx] in
include hlin hord hinj hix hmono hup hblkP heltP in
/-- **One variable's verdict, semantically**: with each round's pack built
by `ixMkKindSem` from an encoded valuation, the machinery's exit bit at the
exhausted register is the alternating quantifier prefix over the inner
blocks, applied to the quantifier-free matrix's realization. The remaining
interface (`hPs`) is the well-definedness of the matrix's value as a
function of the blocks alone — the encoding layer's obligation. -/
theorem ixAccVerdict_varFM_qfValue [LinearOrder (dt.X.Map A)]
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (wOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
      Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
      (j : Fin (dt.nOf vi)),
      wmBlk (ixAddr elt (dt.lvSet (dt.ixRoundSt st (mV a)) vi j))
        (Tag.arg (toLex (dt.lvBlk vi j)) : Tag R P dt.KIx) =
        encMap dt.ly PR.zero PR.one (wOf a hp j))
    (hOld : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
      (i : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      (dt.ixRoundSt st (mV a)).old i
        (ixAddr elt (dt.ixStageTgt F hhasP vi ts
          { dt.ixRoundSt st (mV a) with sav := ixMark elt v }
          (dt.d.B.arity i))) ↔ σ i fun k => wOf a hp (ts k))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    {Ps : (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop}
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf vi)),
      semOf a hp b = dt.ixMkKindSem (elt := elt) PR.zero PR.one vi (dt.ixRoundSt st (mV a))
        (wOf a hp) (hENC a hp) (dt.kindOf vi b))
    (fG : dt.CtlIx → A) {Ex Al : ιV → Prop}
    (hEx : ∀ a : ιV, dt.ctlBit PR.one
      (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
      dt.existGateC ↔ Ex a)
    (hAll : ∀ a : ιV, dt.ctlBit PR.one
      (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
      dt.allGateC ↔ Al a)
    (hPass : ∀ a : ιV, Ex a → Al a →
      ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
    (hPsPass : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ),
      (Ex a ∧ (Al a → qfValue (dt.matOf vi)
        (fun atm => (matAtom? atm).elim False
          (MatAtom.holds σ (wOf a hp))))) ↔
        Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV a))))
    (hPsFail : ∀ a : ιV, ¬(Ex a ∧ Al a) →
      (Ex a ↔ Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV a))))) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) ↔
    altQuantFrom (dt.polOf vi) Ps 0 (ixBlk (argIn dt.ko) (ixAddr elt (mV aT))) := by
  classical
  have hleaf : ∀ a : ιV, dt.roundLeaf (PR := PR) vi
      (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a) ↔
      Ps (ixBlk (argIn dt.ko) (ixAddr elt (mV a))) := by
    intro a
    -- the two flags of the round's exit are the inner gates' thread's
    have hExig : dt.ctlBit PR.one
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
        dt.existGateC ↔
        dt.ctlBit PR.one
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi))
          dt.existGateC := by
      rw [show dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a =
        dt.ixRoundCtl (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a)) v (semOf a)
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) from rfl,
        ctlBit, ctlBit,
        dt.ixRoundCtl_apply_roundFlag (elt := elt) F (hhas := hhasP) (hinj := hinj) (helt := heltP)
          (hzo := PR.zero_ne_one) (Or.inl rfl) vi (dt.ixRoundSt st (mV a))
          v (semOf a) (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a)]
    have hAlig : dt.ctlBit PR.one
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
        dt.allGateC ↔
        dt.ctlBit PR.one
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi))
          dt.allGateC := by
      rw [show dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a =
        dt.ixRoundCtl (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a)) v (semOf a)
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) from rfl,
        ctlBit, ctlBit,
        dt.ixRoundCtl_apply_roundFlag (elt := elt) F (hhas := hhasP) (hinj := hinj) (helt := heltP)
          (hzo := PR.zero_ne_one) (Or.inr rfl) vi (dt.ixRoundSt st (mV a))
          v (semOf a) (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a)]
    rw [roundLeaf]
    by_cases hEA : Ex a ∧ Al a
    · -- a passing round: the leaf is the matrix's value at its points
      have hp : ∀ ℓ : Fin (dt.nIn vi),
          dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ :=
        hPass a hEA.1 hEA.2
      -- its exit is the matrix thread at the ixMkKindSem packs
      have hmat : dt.ctlBit PR.one
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
            dt.existGateC →
          dt.ctlBit PR.one
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
              (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
            dt.allGateC →
          dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a =
            dt.ixMatFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
              (dt.varArgsOf PR.zero PR.one vi).enterAtomSt
              (fun b => dt.ixMkKindSem (elt := elt) PR.zero PR.one vi
                (dt.ixRoundSt st (mV a)) (wOf a hp) (hENC a hp)
                (dt.kindOf vi b))
              (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
                (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi))
              (dt.natOf vi) := by
        intro hex hal
        have hsem' : semOf a hp = fun b => dt.ixMkKindSem (elt := elt) PR.zero PR.one vi
            (dt.ixRoundSt st (mV a)) (wOf a hp) (hENC a hp)
            (dt.kindOf vi b) :=
          funext (hsem a hp)
        rw [show dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a =
          dt.ixRoundCtl (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a)) v (semOf a)
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) from rfl,
          dt.ixRoundCtl_of_flags (elt := elt) F (hhas := hhasP) (hinj := hinj) (helt := heltP)
          (hzo := PR.zero_ne_one) vi (dt.ixRoundSt st (mV a)) v (semOf a)
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) hp (hExig.mp hex)
            (hAlig.mp hal),
          hsem']
      refine Iff.trans ?_ (hPsPass a hp)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(hEx a).mp h1, fun hal => ?_⟩
        have h2' := h2 ((hAll a).mpr hal)
        rw [hmat h1 ((hAll a).mpr hal)] at h2'
        exact (dt.ixPostLeaf_roundFX (elt := elt) F hinj hhasP heltP vi st hlin mV σ a (wOf a hp)
          (hENC a hp) (hOld a hp) hordP
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi))).mp h2'
      · rintro ⟨h1, h2⟩
        have h1' := (hEx a).mpr h1
        refine ⟨h1', fun hal => ?_⟩
        rw [hmat h1' hal]
        exact (dt.ixPostLeaf_roundFX (elt := elt) F hinj hhasP heltP vi st hlin mV σ a (wOf a hp)
          (hENC a hp) (hOld a hp) hordP
          (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi))).mpr
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
  exact ixAccVerdict_varFM (F := F) (hinj := hinj) (hhasP := hhasP) (heltP := heltP)
    (hix := hix) (hblkP := hblkP) (hord := hord) (hlin := hlin) (hmono := hmono)
    (hup := hup) (vi := vi) (st := st) (v := v) (mV := mV) (semOf := semOf)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr) (hKin := hKin)
    (hTop := hTop) (fG := fG) (hleaf := hleaf)

end Threads

/-! ### The threaded twins of the VAL loop's two threads

A round's exit state is its entry state unless the round's matrix ran a
stage atom, which normalizes SAV and TARGET
(`DescriptiveComplexity.Draw.Data.ixRoundEndSt`). Whether it ran at all is
the gates' verdict, read off the control *entering* the round — so the two
have to be iterated **together**, one pair per round, exactly as the
spine's nodes are one scale up.

What is threaded is not the state but the **two scratch registers**
(`DescriptiveComplexity.Draw.Data.ixRoundEndSt_eq`): every other register
is the machinery's entry state's, definitionally. That is what keeps the
semantic packs available — a pack reads the tape state through the levels'
register sets, i.e. through the mirror and VAL alone, so one family
indexed by the two registers serves every round, and it can actually be
built, which a family over arbitrary states could not be. -/

section ThreadsT

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)

/-- The two registers one round of the VAL loop can change. -/
abbrev IxScratch (_dt : Data L) (_A _R _P I : Type) : Type :=
  (I → Prop) × (I → Prop)

/-- **The state a round is entered in**: the machinery's entry state with
the round's two scratch registers and the register it enumerates. -/
noncomputable def ixVarRdSt (p : IxScratch dt A R P I)
    (m : I → Prop) : TapeSt dt A R P I :=
  { st with sav := p.1, tgt := p.2, val := m }

variable (semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi
      (dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ)) elt (dt.kindOf vi b))

variable (v) in
/-- **The VAL loop's thread**: the two scratch registers beside the
control, the fold's start at the cleared register, and at each cover the
round's exit — the store taken against the background the round *ends*
in. -/
noncomputable def ixVarPairT (fG : dt.CtlIx → A) :
    ιV → IxScratch dt A R P I × (dt.CtlIx → A) :=
  iterOrd ((st.sav, st.tgt),
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixVarRdSt st (st.sav, st.tgt) (fun _ => False)) v))
    (fun a p =>
      (((dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP
        vi (dt.ixVarRdSt st p.1 (mV a)) v p.2).sav,
        (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP
          vi (dt.ixVarRdSt st p.1 (mV a)) v p.2).tgt),
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (dt.ixCarryBlk F (mV a))
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundCtlT (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixVarRdSt st p.1 (mV a)) v
              (semT p.1 a) p.2)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi
                (dt.ixVarRdSt st p.1 (mV a)) v p.2) v))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi
              (dt.ixVarRdSt st p.1 (mV a)) v p.2) v)))

variable (v) in
/-- The scratch family of the VAL loop. -/
noncomputable def ixVarSTT (fG : dt.CtlIx → A) (a : ιV) : IxScratch dt A R P I :=
  (dt.ixVarPairT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).1

variable (v) in
/-- The tape family of the VAL loop — the state each round is entered
in. -/
noncomputable def ixVarStT (fG : dt.CtlIx → A) (a : ιV) : TapeSt dt A R P I :=
  dt.ixVarRdSt st (dt.ixVarSTT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) (mV a)

variable (v) in
/-- The control family of the VAL loop, threaded — the twin of
`DescriptiveComplexity.Draw.Data.ixVarFM`. -/
noncomputable def ixVarFMT (fG : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  (dt.ixVarPairT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).2

variable (v) in
/-- **The state one round ends in** — the next round's entry state at a
cover, and the loop's exit state at the top. -/
noncomputable def ixVarStE (fG : dt.CtlIx → A) (a : ιV) : TapeSt dt A R P I :=
  dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi
    (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)

variable (v) in
/-- **The exit control of one VAL round, threaded** — the twin of
`DescriptiveComplexity.Draw.Data.ixRoundFX`, at the state the round's
atoms actually run at. -/
noncomputable def ixVarFXT (fG : dt.CtlIx → A) (a : ιV) : dt.CtlIx → A :=
  dt.ixRoundCtlT (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
    (semT (dt.ixVarSTT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) a)
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The registers a round leaves alone ride the whole loop** — by
construction now, since only the two scratch ones are threaded. -/
theorem ixVarStT_fields (fG : dt.CtlIx → A) (a : ιV) :
    (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).wk = st.wk ∧
      (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).mir = st.mir ∧
      (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).bot = st.bot ∧
      (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).old = st.old ∧
      (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).val = mV a :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- A round leaves the register it was entered with. -/
theorem ixVarStE_val (fG : dt.CtlIx → A) (a : ιV) :
    (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).val = mV a :=
  (dt.ixRoundEndSt_fields (elt := elt) F (zero := PR.zero) (one := PR.one)
    (hhas := hhasP) vi (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)).2.2.2.1

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The VAL loop never touches a stage track**: only the two scratch
registers are threaded, so the `new` tracks the spine writes ride the
whole loop. -/
theorem ixVarStE_new (fG : dt.CtlIx → A) (a : ιV) :
    (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).new = st.new := by
  rw [ixVarStE, dt.ixRoundEndSt_eq (elt := elt) F (zero := PR.zero) (one := PR.one)
    (hhas := hhasP) vi (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)]
  rfl

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **A round's exit state is the next round's entry state**, once the
next round's register is written over it. -/
theorem ixVarRdSt_varStE (fG : dt.CtlIx → A) (a : ιV)
    (m : I → Prop) :
    dt.ixVarRdSt st ((dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).sav,
        (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).tgt) m =
      dt.ixRoundSt (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) m := by
  conv_rhs => rw [ixVarStE, dt.ixRoundEndSt_eq (elt := elt) F (zero := PR.zero) (one := PR.one)
    (hhas := hhasP) vi (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
    v (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)]
  rfl

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The thread starts at the entry state. -/
theorem ixVarSTT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.ixVarSTT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a₀ = (st.sav, st.tgt) :=
  congrArg Prod.fst (iterOrd_bot hbotV)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The thread starts at the entry state. -/
theorem ixVarStT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.ixVarStT (elt := elt) F hinj hhasP heltP
      vi st v mV semT fG a₀ = dt.ixRoundSt st (mV a₀) := by
  rw [ixVarStT, dt.ixVarSTT_bot (elt := elt) F hinj hhasP heltP vi st mV semT hbotV fG]
  rfl

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- The control thread starts at the fold's start. -/
theorem ixVarFMT_bot {a₀ : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a)
    (fG : dt.CtlIx → A) :
    dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a₀ =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v) :=
  congrArg Prod.snd (iterOrd_bot hbotV)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The tape's cover equation**: the next round is entered in this
round's exit state, its own register written over it. -/
theorem ixVarStT_covers {a a' : ιV} (hlt : a < a')
    (hnb : ∀ b, ¬(a < b ∧ b < a')) (fG : dt.CtlIx → A) :
    dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a' =
      dt.ixRoundSt (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) (mV a') := by
  rw [ixVarStT, show dt.ixVarSTT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a' = _ from
    congrArg Prod.fst (iterOrd_covers hlt hnb)]
  exact dt.ixVarRdSt_varStE (elt := elt) F hinj hhasP heltP vi st mV semT fG a (mV a')

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The control's cover equation**: the round's exit control, folded and
stored at the block its increment carried. -/
theorem ixVarFMT_covers {a a' : ιV} (hlt : a < a')
    (hnb : ∀ b, ¬(a < b ∧ b < a')) (fG : dt.CtlIx → A) :
    dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a' =
      (dt.varArgsOf PR.zero PR.one vi).storeCarry
        (dt.ixCarryBlk F (mV a))
        ((dt.varArgsOf PR.zero PR.one vi).postFold
          (dt.ixVarFXT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v) :=
  congrArg Prod.snd (iterOrd_covers hlt hnb)

/-! ### The threaded loop is the unthreaded one

The VAL loop's rounds run at states that differ from the machinery's entry
state in SAV and TARGET alone, and every control they compute is blind to
that difference (`DescriptiveComplexity.Draw.Data.ixRoundCtlT_eq_ixRoundCtl`,
`DescriptiveComplexity.Draw.Data.ixRoundCtl_congr_scratch`). What the
threading *can* change is the semantic pack, since a family indexed by the
scratch registers may pick different points at different registers; so the
bridge is stated at a pack that is one unthreaded pack transported
(`ixSemCastT`), which is what a reduction supplies
(`DescriptiveComplexity.Draw.Data.gatedSem`, whose points are the
address's blocks and nothing else). -/

section ThreadBridge

variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)
variable (sem₀ : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi (dt.ixRoundSt st (mV a)) elt (dt.kindOf vi b))

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
/-- **A round's entry state is the round state up to the two scratch
registers.** -/
theorem ixScratchEq_varRdSt (p : IxScratch dt A R P I)
    (m : I → Prop) :
    dt.ScratchEq (dt.ixVarRdSt st p m) (dt.ixRoundSt st m) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (v) in
/-- **One unthreaded pack, at every state a round reaches**: the round's own
state and the states its matrix threads all share the mirror and VAL of the
round state, so `ixKindSemCast` carries the pack to each of them. -/
noncomputable def ixSemCastT (p : IxScratch dt A R P I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn vi),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixVarRdSt st p (mV a)) ℓ)
    (b : Fin (dt.natOf vi)) :
    dt.IxKindSem PR.zero PR.one vi
      (dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ)) elt (dt.kindOf vi b) :=
  dt.ixKindSemCast (st := dt.ixRoundSt st (mV a))
    (st' := dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ)) PR.zero PR.one vi
    ((dt.ixScratchEq_matSt (vi := vi) (st := dt.ixVarRdSt st p (mV a)) (v := v)
      (b : ℕ)).2.1).symm
    ((dt.ixScratchEq_matSt (vi := vi) (st := dt.ixVarRdSt st p (mV a)) (v := v)
      (b : ℕ)).2.2.1).symm
    (dt.kindOf vi b)
    (sem₀ a (fun ℓ => (dt.ixIGPassP_congr F PR.zero PR.one vi rfl ℓ).mp (hp ℓ)) b)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder ιV] [Finite ιV] in
/-- **One threaded round is the unthreaded round**: a round's own state is
the round state up to SAV and TARGET, its matrix threads those two further,
and the pack rides along — three transports that compose to none. -/
theorem ixRoundCtlT_semCastT (hreg : ¬∃ u : I, v = F.cell u)
    (p : IxScratch dt A R P I) (a : ιV) (q : dt.CtlIx → A) :
    dt.ixRoundCtlT (elt := elt) F (hinj := hinj) (hhas := hhasP) (helt := heltP)
    (hzo := PR.zero_ne_one) vi (dt.ixVarRdSt st p (mV a)) v
        (dt.ixSemCastT F vi st v mV sem₀ p a) q =
      dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV sem₀ q a := by
  classical
  rw [ixRoundFX, dt.ixRoundCtlT_eq_ixRoundCtl (elt := elt) F (hhas := hhasP) (hinj := hinj)
    (helt := heltP) (hzo := PR.zero_ne_one) hreg vi _ _ _,
    dt.ixRoundCtl_congr_scratch (elt := elt) F (hhas := hhasP) (hinj := hinj)
      (helt := heltP) (hzo := PR.zero_ne_one)
      (dt.ixScratchEq_varRdSt st p (mV a)) hreg vi _ _]
  congr 1
  funext hp b
  simp only [ixSemCastT]
  exact dt.ixKindSemCast_triple PR.zero PR.one vi _ _ _ _ _ _ (dt.kindOf vi b)
    (sem₀ a _ b)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [Finite ιV] in
/-- **The threaded round of the VAL loop is the unthreaded one**, at the
state the loop's own thread produced. -/
theorem ixVarFXT_eq_roundFX
    (hreg : ¬∃ u : I, v = F.cell u)
    (fG : dt.CtlIx → A) (a : ιV) :
    dt.ixVarFXT (elt := elt) F hinj hhasP heltP vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG a =
      dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV sem₀
        (dt.ixVarFMT (elt := elt) F hinj hhasP heltP
          vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG a) a :=
  dt.ixRoundCtlT_semCastT (elt := elt) F hinj hhasP heltP vi st mV sem₀ hreg
    (dt.ixVarSTT (elt := elt) F hinj hhasP heltP
      vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG a) a
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG a)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] in
/-- **The VAL loop's threaded control is its unthreaded control**: round by
round, `ixVarFXT_eq_roundFX`, the backgrounds agreeing because a round's exit
state is the round state up to SAV and TARGET. This is the bridge between
the control the machine's run produces and the control
`DescriptiveComplexity.Draw.Data.accVerdict_leafP` reads. -/
theorem ixVarFMT_eq_varFM
    (hreg : ¬∃ u : I, v = F.cell u)
    (fG : dt.CtlIx → A) (a : ιV) :
    dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG a =
      dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV sem₀ fG a := by
  classical
  induction a using order_induction with
  | hmin z hz =>
    rw [dt.ixVarFMT_bot (elt := elt) F hinj hhasP heltP
      vi st mV (dt.ixSemCastT F vi st v mV sem₀) hz fG,
      show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV sem₀ fG z = _ from iterOrd_bot hz]
  | hstep w z hwz hnb ih =>
    have hSE : dt.ScratchEq
        (dt.ixVarStE (elt := elt) F hinj hhasP heltP
          vi st v mV (dt.ixSemCastT F vi st v mV sem₀) fG w)
        (dt.ixRoundSt st (mV w)) :=
      (dt.ixScratchEq_roundEndSt (elt := elt) F (zero := PR.zero) (one := PR.one)
        (hhas := hhasP) vi
        (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV
          (dt.ixSemCastT F vi st v mV sem₀) fG w) v
        (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV
          (dt.ixSemCastT F vi st v mV sem₀) fG w)).trans
        (dt.ixScratchEq_varRdSt st _ (mV w))
    rw [dt.ixVarFMT_covers (elt := elt) F hinj hhasP heltP
      vi st mV (dt.ixSemCastT F vi st v mV sem₀) hwz hnb fG,
      show dt.ixVarFM (elt := elt) F hinj hhasP heltP
        vi st v mV sem₀ fG z = _ from iterOrd_covers hwz hnb,
      dt.ixVarFXT_eq_roundFX (elt := elt) F hinj hhasP heltP
        vi st mV sem₀ hreg fG w, hSE.ixBack hreg, ih]
    rfl

end ThreadBridge

end ThreadsT

section Cap

variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV → I → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr F.le (mV a) (mV a'))
-- The exhaustion test the machine runs, at the registers: the file's own
-- blocks, not the addresses'.
variable (hTestT : ∀ u : I, dt.InnerFull F.blk (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u : I, ¬dt.InnerFull F.blk (mV a) u)
variable (hmir : st.mir = ixMark elt v) (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi (dt.ixRoundSt st (mV a)) elt (dt.kindOf vi b))
variable (semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi
      (dt.ixMatSt (elt := elt) vi (dt.ixVarRdSt st p (mV a)) v (b : ℕ)) elt (dt.kindOf vi b))
variable (hDom : ∀ ℓ : Fin (dt.arOf vi),
  ExpExpansion.DomHolds (X := dt.X)
    (tOf ℓ, decRho dt.ly PR.zero PR.one
      (wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx))))

variable (v) in
/-- **The control the gates leave**, at the reduction's own budgets — what
both forms of the machinery's run start their VAL loop from. -/
noncomputable def ixVarFG (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi
  he₀ hmono hup hvh hxdUse hgap hwP hwR hwK hcostR
  hwkSt hcompatOf hbotV
  htopV hmV0 hIncr hTestT hTestF hmir hbotSt hsav htgt hDom in
/-- **One variable's machinery, fully instantiated**: from the entry
checkpoint at the marker, through the gates at a gated address, the VAL
clear and the rounds of matrix pass, exhaustion test and block-indexed
increment, to the exit checkpoint – the fold spelled by the concrete
threads, every leg the assembled runs of the layers below. -/
theorem ixVarMachine_reachesIn
    (hwitOf : ∀ (ℓ : Fin (dt.arOf vi)) (t' : dt.X.Tag),
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixVarCost A vi w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
              (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf
                (dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
                    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
                  (dt.arOf vi)) aT) aT)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v))),
        Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have htagOf : ∀ ℓ : Fin (dt.arOf vi),
      dt.dspTagOf PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)) =
      tOf ℓ :=
    fun ℓ => dspTagOf_eq_of_onehot (hwitOf ℓ)
  -- the gates' final control
  set fG := dt.ixGatesFs F PR.zero PR.one hhasP vi st v
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
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi) with hfG
  -- the verdict flag holds after the gates
  have hflag : fG dt.gateFlagC = PR.one := by
    rw [hfG]
    have hchar := dt.ctlBit_gateFlagC_ixGatesFs (st := st) (v := v)
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
      (F := F) (hhasP := hhasP) (hinj := hinj) (heltP := heltP) (hzo := hzo)
      (hEnter := fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    refine hchar.mpr ⟨?_, fun ℓ _ => ⟨hwitOf ℓ, hDom ℓ⟩⟩
    change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.gateFlagC True f₀)
      dt.gateFlagC
    exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
  refine dt.var_reachesIn F (fun i ρ => hrules i ρ) hR hlin hix htop hbot hv hvi
    (ixVarBg_back (F := F) (hix := hix) (htop := htop)
      (v := v) (stV := st) (hwkV := hwkSt))
    (wG := dt.ixVarGatesCost A vi w wP)
    (wM := dt.ixRoundCost A vi w wP wR wK) (wS := wP) (w := wG) (hgap := hgap)
    (hS := hwP)
    (hGates := ixVarGates_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (vi := vi)
      (st := st) (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap)
      (w := w) (wP := wP) (hwP := hwP) (hcostR := hcostR)
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf)
      (hTestOf := hTestOf)
      (f₀ := (dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
    hflag
    (ixVarBg_back (F := F) (hix := hix) (htop := htop) (v := v)
      (stV := dt.ixRoundSt st (fun _ => False)) (hwkV := hwkSt))
    (fun r s hs => dt.ixBack_roundSt_off F (st := st) _ _ r s hs)
    hbotV htopV hmV0
    (restO := fun a => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixRoundSt st (mV a)))
    (fun a => ixVarBg_back (F := F) (hix := hix) (htop := htop)
      (v := v) (stV := dt.ixRoundSt st (mV a)) (hwkV := hwkSt))
    (restM := fun a => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixRoundSt st (mV a)))
    ?_
    (fM := dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG)
    (fX := fun a => dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
      (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
    ?_ (hMatrix := ?_) hIncr ?_ ?_ hTestT hTestF
  · -- the first round's background is the cleared one
    exact congrArg (fun m => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixRoundSt st m)) hmV0
  · -- the thread starts at the fold's start
    exact iterOrd_bot hbotV
  · -- the round, per VAL content: the inner gates, the branch and the
    -- matrix — no semantic hypothesis, so every register the loop
    -- enumerates is covered
    intro a
    exact ixRound_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP) (hix := hix)
      (hinj := hinj) (heltP := heltP) (hord := hord) (he₀ := he₀) (vi := vi)
      (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop) (hbot := hbot)
      (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
      (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
      (hwK := hwK) (hcostR := hcostR)
      (stV := dt.ixRoundSt st (mV a)) (hwkV := hwkSt) (hmirV := hmir)
      (hbotV := hbotSt) (hsavV := hsav) (htgtV := htgt) (sem := semOf a)
      (f := dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a)
  · -- backgrounds agree across a cover, off VAL
    intro a a' hlt hnb r s hs
    exact dt.ixBack_roundSt_off F (st := st) _ _ r s hs
  · -- the store at a cover is the thread's step
    intro a a' hlt hnb u₀ h1 h2
    have hcov := iterOrd_covers
      (init := (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v))
      (step := fun a q =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (dt.ixCarryBlk F (mV a))
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q a)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
      hlt hnb
    rw [show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a' = _ from hcov,
      ixCarryBlk, dt.ixValCarry_eq F hix h1 h2]
    rfl

include hrules hR hlin hix hsepP hhasP hinj heltP hord htop hbot hwork hv hvi
  he₀ hmono hup hvh hxdUse hgap hwP hwR hwK hcostR
  hwkSt hcompatOf hbotV
  htopV hmV0 hIncr hTestT hTestF hmir hbotSt hDom in
/-- **One variable's machinery, fully instantiated — threaded**: as
`DescriptiveComplexity.Draw.Data.ixVarMachine_run` with no boundary
discipline assumed, so it applies at every address of a sweep and not
only at the one whose SAV and TARGET the advance happens to have left
behind. The rounds run at the states the thread produces, and the loop
ends in `DescriptiveComplexity.Draw.Data.ixVarStE` at the top, which
differs from the entry state in SAV and TARGET alone. -/
theorem ixVarMachine_run_thread_reachesIn
    (hwitOf : ∀ (ℓ : Fin (dt.arOf vi)) (t' : dt.X.Tag),
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (dt.ixVarCost A vi w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixVarFXT (elt := elt) F hinj hhasP heltP vi st v mV semT
              (dt.ixVarFG (PR := PR) F hhasP vi st v tOf f₀) aT)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixVarStE (elt := elt) F hinj hhasP heltP
                vi st v mV semT (dt.ixVarFG (PR := PR) F hhasP vi st v tOf f₀) aT) v))),
        Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixVarStE (elt := elt) F hinj hhasP heltP
              vi st v mV semT (dt.ixVarFG (PR := PR) F hhasP vi st v tOf f₀) aT))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have htagOf : ∀ ℓ : Fin (dt.arOf vi),
      dt.dspTagOf PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)) =
      tOf ℓ :=
    fun ℓ => dspTagOf_eq_of_onehot (hwitOf ℓ)
  set fG := dt.ixVarFG (PR := PR) F hhasP vi st v tOf f₀ with hfG
  -- the verdict flag holds after the gates
  have hflag : fG dt.gateFlagC = PR.one := by
    rw [hfG, ixVarFG]
    have hchar := dt.ctlBit_gateFlagC_ixGatesFs (st := st) (v := v)
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
      (F := F) (hhasP := hhasP) (hinj := hinj) (heltP := heltP) (hzo := hzo)
      (hEnter := fun ℓ f g => Iff.rfl)
      ((dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)) (dt.arOf vi)
    refine hchar.mpr ⟨?_, fun ℓ _ => ⟨hwitOf ℓ, hDom ℓ⟩⟩
    change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.gateFlagC True f₀)
      dt.gateFlagC
    exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
  -- the entry state's field equations ride every round's state
  have hwkA : ∀ a : ιV, (dt.ixVarStT (elt := elt) F hinj hhasP heltP
    vi st v mV semT fG a).wk = fun r => r = v :=
    fun a => ((dt.ixVarStT_fields (elt := elt) F hinj hhasP heltP vi st mV semT fG a).1).trans hwkSt
  have hmirA : ∀ a : ιV, (dt.ixVarStT (elt := elt) F hinj hhasP heltP
    vi st v mV semT fG a).mir = ixMark elt v :=
    fun a => ((dt.ixVarStT_fields (elt := elt) F hinj hhasP heltP
      vi st mV semT fG a).2.1).trans hmir
  have hbotA : ∀ a : ιV, (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a).bot =
      fun r => r = (fun _ => False) :=
    fun a => ((dt.ixVarStT_fields (elt := elt) F hinj hhasP heltP
      vi st mV semT fG a).2.2.1).trans hbotSt
  have hvalE : ∀ a : ιV, (dt.ixVarStE (elt := elt) F hinj hhasP heltP
    vi st v mV semT fG a).val = mV a :=
    fun a => dt.ixVarStE_val (elt := elt) F hinj hhasP heltP vi st mV semT fG a
  refine dt.var_reachesIn F (fun i ρ => hrules i ρ) hR hlin hix htop hbot hv hvi
    (ixVarBg_back (F := F) (hix := hix) (htop := htop)
      (v := v) (stV := st) (hwkV := hwkSt))
    (wG := dt.ixVarGatesCost A vi w wP)
    (wM := dt.ixRoundCost A vi w wP wR wK) (wS := wP) (w := wG) (hgap := hgap)
    (hS := hwP)
    (hGates := ixVarGates_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (vi := vi)
      (st := st) (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hgap := hgap)
      (w := w) (wP := wP) (hwP := hwP) (hcostR := hcostR)
      (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf) (htagOf := htagOf)
      (hTestOf := hTestOf)
      (f₀ := (dt.varArgsOf PR.zero PR.one vi).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))
    hflag
    (ixVarBg_back (F := F) (hix := hix) (htop := htop) (v := v)
      (stV := dt.ixRoundSt st (fun _ => False)) (hwkV := hwkSt))
    (fun r s hs => dt.ixBack_roundSt_off F (st := st) _ _ r s hs)
    hbotV htopV hmV0
    (restO := fun a => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a))
    (fun a => (hvalE a) ▸ ixVarBg_back (F := F) (hix := hix)
      (htop := htop) (v := v)
      (stV := dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
      (hwkV := ((dt.ixRoundEndSt_fields (elt := elt) F (zero := PR.zero)
        (one := PR.one) (hhas := hhasP) vi
        (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
        (dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)).1).trans
        (hwkA a)))
    (restM := fun a => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a))
    ?_
    (fM := dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG)
    (fX := dt.ixVarFXT (elt := elt) F hinj hhasP heltP vi st v mV semT fG)
    ?_ (hMatrix := ?_) hIncr ?_ ?_ hTestT hTestF
  · -- the first round's background is the cleared one
    rw [show dt.ixVarStT (elt := elt) F hinj hhasP heltP
      vi st v mV semT fG a₀ = dt.ixRoundSt st (mV a₀) from
      dt.ixVarStT_bot (elt := elt) F hinj hhasP heltP vi st mV semT hbotV fG, hmV0]
  · -- the thread starts at the fold's start
    exact dt.ixVarFMT_bot (elt := elt) F hinj hhasP heltP vi st mV semT hbotV fG
  · -- the round, at the state the thread produced for it
    intro a
    have hrun := ixRound_run_thread_reachesIn (F := F) (hhasP := hhasP)
      (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (hord := hord) (he₀ := he₀)
      (vi := vi) (hrules := hrules) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot) (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono)
      (hup := hup) (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP)
      (hwR := hwR) (hwK := hwK) (hcostR := hcostR)
      (stV := dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
      (hwkV := hwkA a) (hmirV := hmirA a) (hbotV := hbotA a)
      (sem := semT (dt.ixVarSTT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) a)
      (f := dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a)
    rw [show (dt.ixRoundEndSt (elt := elt) F PR.zero PR.one hhasP vi
        (dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) v
        (dt.ixVarFMT (elt := elt) F hinj hhasP heltP
          vi st v mV semT fG a)).val = mV a from hvalE a] at hrun
    exact hrun
  · -- backgrounds agree across a cover, off VAL
    intro a a' hlt hnb r s hs
    rw [show dt.ixVarStT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a' =
      dt.ixRoundSt (dt.ixVarStE (elt := elt) F hinj hhasP heltP vi st v mV semT fG a) (mV a') from
      dt.ixVarStT_covers (elt := elt) F hinj hhasP heltP vi st mV semT hlt hnb fG]
    exact dt.ixBack_roundSt_off F (st := dt.ixVarStE (elt := elt) F hinj hhasP heltP
      vi st v mV semT fG a)
      _ _ r s hs
  · -- the store at a cover is the thread's step
    intro a a' hlt hnb u₀ h1 h2
    rw [show dt.ixVarFMT (elt := elt) F hinj hhasP heltP vi st v mV semT fG a' = _ from
      dt.ixVarFMT_covers (elt := elt) F hinj hhasP heltP vi st mV semT hlt hnb fG,
      ixCarryBlk, dt.ixValCarry_eq F hix h1 h2]
    rfl
end Cap

end VarCapstone

end VarInst

end Data

end Draw

end DescriptiveComplexity
