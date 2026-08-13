/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpRun
import DescriptiveComplexity.Problems.Wide.PfpInstEval

/-!
# The outer composition: the sweep's rounds

One round of the outer sweep, at the concrete program: the whole per-address
evaluation (`DescriptiveComplexity.Pfp.PfpData.evalSpine_run`), the boundary
dispatch into ADVANCE (the last checkpoint's erasing rule, off the `ltp`
cell), the advance itself
(`DescriptiveComplexity.Pfp.PfpData.reaches_sweepAdv`), the exit dispatch
into the next address's first checkpoint and its walk back. The walk is
handed between the VAL track (the evaluation's presentation) and the MIRROR
track (the advance's) by
`DescriptiveComplexity.Pfp.PfpData.trackTape_back_swap`, which costs
nothing because the background carries every register's digits at its own
slot.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A : Type} (zero one : A)
variable [LinearOrder A] [Fintype dt.SlotIx]
variable (hzo : zero ≠ one)
variable (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := dt.CtlIx) v)
variable [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]
variable (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
variable [Language.wide.Structure
  (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
variable [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
variable [Finite dt.KIx]

/-! ### The evaluation's rules, at the program -/

omit [Language.wide.Structure
  (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
  [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- The program's rule at an evaluation site is the evaluation's. -/
theorem prog_rules_eval (e : dt.SEF) (ρ : dt.SESh e) :
    (dt.prog zero one hzo args hpl).rules ⟨.eval e, ρ⟩ =
      dt.evalRuleF zero one args e ρ := rfl

omit [LinearOrder A] [LinearOrder (dt.RIx zero one hzo args)]
  [LinearOrder dt.PF]
  [Language.wide.Structure
    (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
  [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- The assembly's rule at an evaluation site, in projection form. -/
theorem progAsm_rule_eval (e : dt.SEF) (ρ : dt.SESh e) :
    (dt.progAsm zero one hzo args).rule (.eval e) ρ =
      dt.evalRuleF zero one args e ρ := rfl

variable {dt zero one hzo args hpl}

omit [Language.wide.Structure
  (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
  [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- An evaluation rule with a true guard is a `HasRight` witness of the
program. -/
theorem prog_hasRight_eval {e : dt.SEF} {ρ : dt.SESh e}
    {f f' : dt.CtlIx → A} {g g' : dt.SlotIx → A} {p p' : dt.PF}
    (hg : (dt.evalRuleF zero one args e ρ).guard f g)
    (hp : (dt.evalRuleF zero one args e ρ).srcPh = p)
    (hp' : (dt.evalRuleF zero one args e ρ).dstPh = p')
    (hf' : (dt.evalRuleF zero one args e ρ).dstSt f g = f')
    (hg' : (dt.evalRuleF zero one args e ρ).wr f g = g')
    (hmr : (dt.evalRuleF zero one args e ρ).moveRight) :
    (dt.prog zero one hzo args hpl).HasRight p f g p' f' g' :=
  ⟨⟨.eval e, ρ⟩, by rw [prog_rules_eval]; exact hg,
    by rw [prog_rules_eval, hp], by rw [prog_rules_eval, hp'],
    by rw [prog_rules_eval, hf'], by rw [prog_rules_eval, hg'],
    by rw [prog_rules_eval]; exact hmr⟩

omit [Language.wide.Structure
  (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
  [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- An evaluation rule with a true guard is a `HasLeft` witness of the
program. -/
theorem prog_hasLeft_eval {e : dt.SEF} {ρ : dt.SESh e}
    {f f' : dt.CtlIx → A} {g g' : dt.SlotIx → A} {p p' : dt.PF}
    (hg : (dt.evalRuleF zero one args e ρ).guard f g)
    (hp : (dt.evalRuleF zero one args e ρ).srcPh = p)
    (hp' : (dt.evalRuleF zero one args e ρ).dstPh = p')
    (hf' : (dt.evalRuleF zero one args e ρ).dstSt f g = f')
    (hg' : (dt.evalRuleF zero one args e ρ).wr f g = g')
    (hml : ¬(dt.evalRuleF zero one args e ρ).moveRight) :
    (dt.prog zero one hzo args hpl).HasLeft p f g p' f' g' :=
  ⟨⟨.eval e, ρ⟩, by rw [prog_rules_eval]; exact hg,
    by rw [prog_rules_eval, hp], by rw [prog_rules_eval, hp'],
    by rw [prog_rules_eval, hf'], by rw [prog_rules_eval, hg'],
    fun hc => hml (by rw [prog_rules_eval] at hc; exact hc)⟩

/-! ### The two boundary pieces of a round -/

/-- **The walk back into a checkpoint**: an entering dispatch lands one
cell right of the marker; the checkpoint's stay rule steps back to it. -/
theorem step_evalChk_back
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {k : Fin (dt.nv + 1)} {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {mval v v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v) (hvi : WMIncr WMLe v v') :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.evalP (.chk k)) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st) mval)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.evalP (.chk k)) fc),
        Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st) mval)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkv' : (dt.prog zero one hzo args hpl).passTracks Slot.val
      (dt.back zero one dt.dd0Le st) mval v' Slot.wk ≠
      (dt.prog zero one hzo args hpl).one := by
    rw [Prog.passTracks_of_ne hne_wk_val, back_wk, hwk,
      bitVal_neg (Ne.symm hvv')]
    exact hzo
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  exact prog_hasLeft_eval (e := .chk k) (ρ := .stay)
    hwkv' rfl rfl rfl rfl not_false

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- **Erasing the marker is presenting the marker-free state**: the written
symbol of both boundary dispatches out of the last checkpoint, at the
MIRROR-walked presentation. -/
private theorem update_wk_offSt
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop} :
    Function.update
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le st) st.mir v) Slot.wk zero =
      (dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le (dt.offSt st)) st.mir v := by
  classical
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  funext s
  by_cases hs : s = Slot.wk
  · subst hs
    rw [Function.update_self, Prog.passTracks_of_ne hne_wk_mir, back_wk]
    exact (bitVal_neg not_false).symm
  · rw [Function.update_of_ne hs]
    by_cases hsm : s = Slot.mir
    · rw [hsm]
      change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
        (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
      rw [if_pos rfl, if_pos rfl]
    · rw [Prog.passTracks_of_ne hsm, Prog.passTracks_of_ne hsm]
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir
      | .tgt | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl

/-- **The erasing dispatch into the advance**, as the `HasRight` the
advance's round theorem consumes: at the last checkpoint below the `ltp`
cell, erase the marker and enter the advance — stated at the MIRROR-walked
presentation the advance runs on. -/
theorem hasRight_evalAdv
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (hbot : ∀ y, WMLe gbot y)
    {v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v (wmSeg gbot))
    {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = v) (hltp : ¬st.ltp v) :
    (dt.prog zero one hzo args hpl).HasRight
      (.evalP (.chk (Fin.last dt.nv))) fc
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le st) st.mir v)
      (.advP .a1) fc
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le (dt.offSt st)) st.mir v) := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_reg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_ltp_mir : (Slot.ltp : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hnl : ¬((Fin.last dt.nv : Fin (dt.nv + 1)) : ℕ) < dt.nv := by
    simp [Fin.last]
  have hupd := update_wk_offSt (hpl := hpl) (st := st) (v := v)
  have hruleAdv : dt.evalRuleF zero one args (.chk (Fin.last dt.nv))
      (.dspA) =
      { guard := fun _ g => dt.exitG one g ∧ g Slot.ltp ≠ one
        srcPh := .evalP (.chk (Fin.last dt.nv))
        dstPh := .advP .a1
        dstSt := fun f _ => f
        wr := fun _ g => Function.update g Slot.wk zero
        moveRight := True } := dif_neg hnl
  refine prog_hasRight_eval (e := .chk (Fin.last dt.nv)) (ρ := .dspA)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hruleAdv]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Prog.passTracks_of_ne hne_wk_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_mir, back_reg,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact hzo
    · rw [Prog.passTracks_of_ne hne_ltp_mir, back_ltp, bitVal_neg hltp]
      exact hzo
  · rw [hruleAdv]
  · rw [hruleAdv]
  · rw [hruleAdv]
  · rw [hruleAdv]
    exact hupd
  · rw [hruleAdv]
    trivial

/-- **The erasing dispatch into the post-sweep reset**: at the last
checkpoint on the `ltp` cell, erase the marker and enter the reset. -/
theorem hasRight_evalReset
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (hbot : ∀ y, WMLe gbot y)
    {v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v (wmSeg gbot))
    {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = v) (hltp : st.ltp v) :
    (dt.prog zero one hzo args hpl).HasRight
      (.evalP (.chk (Fin.last dt.nv))) fc
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le st) st.mir v)
      (.reset2P .scan) fc
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le (dt.offSt st)) st.mir v) := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_reg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_ltp_mir : (Slot.ltp : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hnl : ¬((Fin.last dt.nv : Fin (dt.nv + 1)) : ℕ) < dt.nv := by
    simp [Fin.last]
  have hupd := update_wk_offSt (hpl := hpl) (st := st) (v := v)
  have hruleRst : dt.evalRuleF zero one args (.chk (Fin.last dt.nv))
      (.dspB) =
      { guard := fun _ g => dt.exitG one g ∧ g Slot.ltp = one
        srcPh := .evalP (.chk (Fin.last dt.nv))
        dstPh := .reset2P .scan
        dstSt := fun f _ => f
        wr := fun _ g => Function.update g Slot.wk zero
        moveRight := True } := if_neg hnl
  refine prog_hasRight_eval (e := .chk (Fin.last dt.nv)) (ρ := .dspB)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hruleRst]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Prog.passTracks_of_ne hne_wk_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_mir, back_reg,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact hzo
    · rw [Prog.passTracks_of_ne hne_ltp_mir, back_ltp]
      exact bitVal_pos hltp
  · rw [hruleRst]
  · rw [hruleRst]
  · rw [hruleRst]
  · rw [hruleRst]
    exact hupd
  · rw [hruleRst]
    trivial

/-! ### The post-sweep reset and mirror clear -/

/-- **The reset's leg after a completed sweep**, the last checkpoint's
erasing exit included: from the `ltp` cell to the reset's landing phase at
the empty address, the bottom marker rewritten. -/
theorem reaches_reset2
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (hbot : ∀ y, WMLe gbot y)
    {vT : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvT : WMSetLt WMLe vT (wmSeg gbot))
    {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = vT) (hltp : st.ltp vT)
    (hbotSt : st.bot = fun r => r = (fun _ => False)) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk (Fin.last dt.nv))) fc), Sum.inl vT,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.reset2P .done) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.atSt (dt.offSt st) (fun _ => False))) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  -- the `ltp` cell is not the full set, so it has a successor
  have hnotfull : ∃ x, ¬vT x := by
    by_contra hc
    have hfull' : ∀ x, vT x :=
      fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
    have hfull := wmSetLe_of_full hlin hfull' (wmSeg gbot)
    rw [wmSetLt_iff] at hvT
    exact hvT.2 (hset.2.2.1 _ _ hvT.1 hfull)
  refine ResetKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := ResetKit.mk (A := A) (Q := dt.CtlIx) (P := dt.PF) Slot.mir Slot.bot
      Slot.wk OuterPh.reset2P)
    (rEmb := fun ρ => ⟨OuterSite.reset2, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_reset2 zero one hzo args hpl ρ)
    hR hlin dt.bot_ne_mir dt.wk_ne_mir (v := vT) hnotfull (m := st.mir)
    (restA := dt.back zero one dt.dd0Le st)
    (restN := dt.back zero one dt.dd0Le (dt.offSt st))
    (restB := dt.back zero one dt.dd0Le
      (dt.atSt (dt.offSt st) (fun _ => False)))
    ?_ ?_ ?_ (fun _ => rfl) ?_ (fc := fc)
    (hasRight_evalReset hlin hbot hvT hwk hltp)
  · intro r hr
    funext sl
    match sl with
    | .wk =>
      rw [back_wk, back_wk, hwk]
      exact bitVal_congr ⟨False.elim, fun hc => absurd hc hr⟩
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
  · intro r hr
    funext sl
    match sl with
    | .wk =>
      rw [back_wk, back_wk]
      exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
  · intro r
    rw [back_bot]
    exact bitVal_congr (iff_of_eq (congrFun
      (show (dt.offSt st).bot = fun r => r = (fun _ => False) from hbotSt) r))
  · intro sl hsl
    match sl with
    | .wk => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl

/-- **The post-sweep reset's exit**: off the marker, rightwards, into the
mirror clear. -/
theorem step_reset2_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.reset2P .done) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir2P .up) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.reset2
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo args hpl .reset2 (Sum.inr ()) hg trivial

/-- **The pre-compare mirror clear's leg**: the trip that empties the
mirror register, returning to the marker at the empty address. -/
theorem reaches_clearMir2
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    {s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop} :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir2P .up) fc),
        Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir2P .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le { st with mir := fun _ => False })
          (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have htrip := ClearKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := dt.clearMirKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
      OuterPh.clearMir2P)
    (rEmb := fun ρ => ⟨OuterSite.clearMir2, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_clearMir2 zero one hzo args hpl ρ)
    hR hlin dt.mir_ne_reg dt.regLast_ne_mir dt.wk_ne_mir htop hbot
    (rest := dt.back zero one dt.dd0Le st) (m := st.mir)
    (wkAddr := fun _ => False) (wmSetLt_empty_wmSeg hlin gbot)
    (dt.back_reg (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st))
    (dt.back_regLast (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st)
      hlin htop hord)
    (fun r => by
      simp only [clearMirKit]
      rw [back_wk, hwk]
      rfl)
    (fc := fc) (s := s)
  simp only [clearMirKit] at htrip
  refine htrip.trans ?_
  have hagree : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd → Prop) (sl : dt.SlotIx), sl ≠ Slot.mir →
      dt.back zero one dt.dd0Le st r sl =
        dt.back zero one dt.dd0Le { st with mir := fun _ => False } r sl := by
    intro r sl hsl
    match sl with
    | .mir => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
    | .sav | .val | .wk | .bot | .ltp | .old _ | .new _ => rfl
  have hmir : ∀ r, dt.back zero one dt.dd0Le
      { st with mir := fun _ => False } r Slot.mir =
      bitVal zero one (regBit (fun _ => False) r) := fun _ => rfl
  rw [dt.trackTape_back zero one hzo args hpl hagree hmir,
    ← dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl)
      (dt.back_mir zero one hzo args { st with mir := fun _ => False })]

/-! ### One round of the sweep -/

/-- **One round of the outer sweep, with its evaluation**: from the first
checkpoint at the marker, through the whole per-address evaluation (given
as a hypothesis — the caller instantiates it by
`DescriptiveComplexity.Pfp.PfpData.evalSpine_run`), out through the erasing
boundary dispatch, the advance, and back into the first checkpoint at the
next address. The marker, the mirror and the head all step on in
lockstep. -/
theorem sweepRound
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {v v' v'' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v') (hvi' : WMIncr WMLe v' v'')
    (hv : WMSetLt WMLe v (wmSeg gbot)) (hv' : WMSetLt WMLe v' (wmSeg gbot))
    {st₀ stE : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {fs₀ fsE : dt.CtlIx → A}
    (hspine : Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs₀), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st₀) st₀.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk (Fin.last dt.nv))) fsE), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le stE) stE.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (hwkE : stE.wk = fun r => r = v) (hmirE : stE.mir = v)
    (hltpE : ¬stE.ltp v) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs₀), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st₀) st₀.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fsE), Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le { dt.atSt stE v' with mir := v' })
          stE.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hvnr' := not_reg_of_lt_bot hlin hbot hv'
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  -- the evaluation
  refine hspine.trans ?_
  -- hand the walk from VAL to MIRROR for the advance
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_val zero one hzo args stE) (dt.back_mir zero one hzo args stE)]
  -- the boundary dispatch and the advance
  refine (dt.reaches_sweepAdv zero one hzo args hpl hR hlin hord htop hbot
    hwkE hvi hv' (by rw [hmirE]; exact hvi)
    (hasRight_evalAdv hlin hbot hv hwkE hltpE)).trans ?_
  -- hand the walk back from MIRROR to VAL
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_mir zero one hzo args { dt.atSt stE v' with mir := v' })
    (dt.back_val zero one hzo args { dt.atSt stE v' with mir := v' })]
  -- the exit dispatch into the next checkpoint
  have hexit : (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.advP .a4) fsE),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le { dt.atSt stE v' with mir := v' })
          stE.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fsE), Sum.inl v'',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le { dt.atSt stE v' with mir := v' })
          stE.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
    refine Prog.step_move hR hlin hvi' (fun _ _ => rfl) ?_
    refine dt.prog_hasRight zero one hzo args hpl .sweepAdv (Sum.inr ())
      ?_ trivial
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_val, back_wk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_val, back_reg,
        bitVal_neg (fun hc => hvnr' hc.choose hc.choose_spec)]
      exact hzo
  refine (Relation.ReflTransGen.single hexit).trans ?_
  -- the walk back to the new marker
  exact Relation.ReflTransGen.single
    (step_evalChk_back hR hlin rfl hvi')

/-! ### The whole sweep -/

/-- **The outer sweep**: from the first checkpoint at the bottom of the
stretch to the first checkpoint at its top, one round per address — each
round the per-address evaluation and the advance, glued by
`DescriptiveComplexity.Pfp.PfpData.sweepRound`. The evaluation runs, the
end-state facts and the two cover equations (the tape and control threads
across addresses) are per-address hypotheses; everything else is
`DescriptiveComplexity.reaches_of_wideRounds`. -/
theorem reaches_sweep
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {s₀ s₁ : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hs₀ : WMSetLe WMLe s₀ s₁) (hs₁ : WMSetLt WMLe s₁ (wmSeg gbot))
    {SW stE : (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop) →
      TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {FS fsE : (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop) →
      dt.CtlIx → A}
    (hspine : ∀ v, WMSetLe WMLe s₀ v → WMSetLt WMLe v s₁ →
      Relation.ReflTransGen
        (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
          dt.dd)).Step
        ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
            (.evalP (.chk 0)) (FS v)), Sum.inl v,
          wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
            (dt.back zero one dt.dd0Le (SW v)) (SW v).val)
            ((dt.prog zero one hzo args hpl).syElt
              (dt.prog zero one hzo args hpl).blank)⟩
        ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
            (.evalP (.chk (Fin.last dt.nv))) (fsE v)), Sum.inl v,
          wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
            (dt.back zero one dt.dd0Le (stE v)) (stE v).val)
            ((dt.prog zero one hzo args hpl).syElt
              (dt.prog zero one hzo args hpl).blank)⟩)
    (hwkE : ∀ v, WMSetLe WMLe s₀ v → WMSetLt WMLe v s₁ →
      (stE v).wk = fun r => r = v)
    (hmirE : ∀ v, WMSetLe WMLe s₀ v → WMSetLt WMLe v s₁ → (stE v).mir = v)
    (hltpE : ∀ v, WMSetLe WMLe s₀ v → WMSetLt WMLe v s₁ → ¬(stE v).ltp v)
    (hSW : ∀ v v', WMIncr WMLe v v' → WMSetLe WMLe s₀ v →
      WMSetLe WMLe v' s₁ → SW v' = { dt.atSt (stE v) v' with mir := v' })
    (hFS : ∀ v v', WMIncr WMLe v v' → WMSetLe WMLe s₀ v →
      WMSetLe WMLe v' s₁ → FS v' = fsE v) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (FS s₀)), Sum.inl s₀,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (SW s₀)) (SW s₀).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (FS s₁)), Sum.inl s₁,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (SW s₁)) (SW s₁).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  -- `≤` then `<` gives `<`
  have hlelt : ∀ a b c :
      Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop,
      WMSetLe WMLe a b → WMSetLt WMLe b c → WMSetLt WMLe a c := by
    intro a b c hab hbc
    rw [wmSetLt_iff] at hbc ⊢
    refine ⟨hset.2.1 a b c hab hbc.1, fun hac => hbc.2 ?_⟩
    subst hac
    exact hset.2.2.1 b a hbc.1 hab
  refine reaches_of_wideRounds hlin
    (conf := fun v =>
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (FS v)), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (SW v)) (SW v).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (s₀ := s₀) (s₁ := s₁) ?_ s₁ hs₀ (hset.1 s₁)
  intro v v' hcov hlb hub
  -- position facts for the round
  have hvv' : WMSetLt WMLe v v' :=
    (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hcov, ne_of_wmIncr hcov⟩
  have hvS : WMSetLt WMLe v s₁ := by
    rw [wmSetLt_iff]
    refine ⟨hset.2.1 v v' s₁ (wmSetLe_of_wmIncr hcov) hub, fun hvs => ?_⟩
    subst hvs
    exact ne_of_wmIncr hcov
      (hset.2.2.1 v v' (wmSetLe_of_wmIncr hcov) hub)
  have hv : WMSetLt WMLe v (wmSeg gbot) :=
    hlelt _ _ _ ((wmSetLt_iff _ _).mp hvS).1 hs₁
  have hv' : WMSetLt WMLe v' (wmSeg gbot) := hlelt _ _ _ hub hs₁
  -- the next address exists: `v'` is not the full set
  have hnotfull : ∃ x, ¬v' x := by
    by_contra hc
    have hfull' : ∀ x, v' x :=
      fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
    have hfull := wmSetLe_of_full hlin hfull' (wmSeg gbot)
    rw [wmSetLt_iff] at hv'
    exact hv'.2 (hset.2.2.1 _ _ hv'.1 hfull)
  obtain ⟨v'', hvi'⟩ := exists_wmIncr hlin hnotfull
  -- the round
  rw [hSW v v' hcov hlb hub, hFS v v' hcov hlb hub]
  exact sweepRound hR hlin hord htop hbot hcov hvi'
    hv hv' (hspine v hlb hvS) (hwkE v hlb hvS) (hmirE v hlb hvS)
    (hltpE v hlb hvS)

/-! ### Entering the convergence sweep

A plain sweep cannot be entered from the left of the empty address, so
`clearMir2`'s verdict exit *is* COMPARE's first step: it tests the empty
address's cell and lands at its successor, in exactly the sweep's state
there. The sweep then continues from the successor
(`DescriptiveComplexity.Pfp.FlagSweepKit.reaches` is general in its
stretch, which `reaches_compareFrom` exposes). -/

/-- **The convergence sweep from an arbitrary start**: the generalization
of `DescriptiveComplexity.Pfp.PfpData.reaches_compare` the folded first
step needs. -/
theorem reaches_compareFrom
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : dt.CtlIx → A} {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr)
    {s₀ : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe s₀ ltpAddr) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) s₀),
        Sum.inl s₀,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) ltpAddr),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  refine FlagSweepKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := dt.compareKit (Q := dt.CtlIx) (P := dt.PF) one OuterPh.cmpP)
    (rEmb := fun ρ => ⟨OuterSite.compare, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_compare zero one hzo args hpl ρ)
    hR hlin dt.ltp_ne_mir (rest := dt.back zero one dt.dd0Le st)
    (m := st.mir) (ltpAddr := ltpAddr)
    (fun r => by
      simp only [compareKit]
      rw [back_ltp, hltp]
      rfl)
    (Test := fun r => ∀ i, (st.old i r ↔ st.new i r))
    (fun r => by
      simp only [compareKit]
      refine forall_congr' fun i => ?_
      rw [Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h),
        Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h), back_old, back_new]
      exact iff_congr (bitVal_iff hzo) (bitVal_iff hzo))
    (fc := fc) hle ((isLinOrd_wmSetLe hlin).1 ltpAddr)

/-- **COMPARE's folded first step**: `clearMir2`'s verdict exit tests the
empty address's cell and lands at its successor, in the sweep's state
there. -/
theorem step_clearMir2_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir2P .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) v'),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  set b : Bool := decide (∀ i, (st.old i (fun _ => False) ↔
    st.new i (fun _ => False))) with hbdef
  -- below the successor of the empty address there is only the empty address
  have hbelow : ∀ r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd → Prop, WMSetLt WMLe r v' → r = fun _ => False := by
    intro r hr
    have hle := (wmSetLt_iff_of_wmIncr hlin hvi r).mp hr
    exact hset.2.2.1 r _ hle (wmSetLe_of_empty hlin (fun _ hc => hc) r)
  -- the sweep's state at the successor is the verdict of the empty address
  have hsw : sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
      ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
      ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) v' =
      (dt.prog zero one hzo args hpl).stElt
        (.cmpP (if b then .py else .pn)) fc := by
    by_cases hb : ∀ i, (st.old i (fun _ => False) ↔
        st.new i (fun _ => False))
    · rw [sweepState, if_pos (fun r hr => hbelow r hr ▸ hb),
        show b = true from decide_eq_true hb]
      rfl
    · rw [sweepState, if_neg (fun hc => hb (hc _
          ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_empty hlin (fun _ hc' => hc') v',
            fun hc' => ne_of_wmIncr hvi hc'⟩))),
        show b = false from decide_eq_false hb]
      rfl
  rw [hsw]
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.clearMir2
      (Sum.inr b)).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
    · constructor
      · intro hcmp
        refine decide_eq_true fun i => ?_
        have h := hcmp i
        rw [Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir
            from fun h => nomatch h),
          Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir
            from fun h => nomatch h), back_old, back_new] at h
        exact (iff_congr (bitVal_iff hzo) (bitVal_iff hzo)).mp h
      · intro hbt i
        have h' : ∀ i, (st.old i (fun _ => False) ↔
            st.new i (fun _ => False)) :=
          of_decide_eq_true (hbdef ▸ hbt)
        have h := h' i
        rw [Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir
            from fun h => nomatch h),
          Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir
            from fun h => nomatch h), back_old, back_new]
        exact (iff_congr (bitVal_iff hzo) (bitVal_iff hzo)).mpr h
  exact dt.prog_hasRight zero one hzo args hpl .clearMir2 (Sum.inr b) hg
    trivial

/-! ### The compare verdicts, and the copy-back ring

At the `ltp` cell the sweep's verdict dispatches: passing to the output's
walk home, failing to the copy-back's. The copy-back has the same folded
entry as the sweep it corrects: `homeCmp`'s exit rewrites the empty
address's cell and lands at its successor, and the copy exits at the `ltp`
cell into its own walk home, whose exit re-enters the evaluation. -/

/-- **The passing verdict**: at the `ltp` cell with every address below
agreed, step off it into the output's walk home. -/
theorem step_compare_exit_pos
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : dt.CtlIx → A} {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr vp : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr) (hvp : WMIncr WMLe vp ltpAddr)
    (hyes : ∀ r, WMSetLt WMLe r ltpAddr → ∀ i, (st.old i r ↔ st.new i r)) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) ltpAddr),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeOutP fc),
        Sum.inl vp,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  rw [sweepState, if_pos hyes]
  refine Prog.step_moveBack hR hlin hvp (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.compare
      (Sum.inr true)).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir ltpAddr) := by
    change (dt.prog zero one hzo args hpl).passTracks Slot.mir
      (dt.back zero one dt.dd0Le st) st.mir ltpAddr Slot.ltp = one
    rw [Prog.passTracks_of_ne dt.ltp_ne_mir, back_ltp, hltp]
    exact bitVal_pos rfl
  exact dt.prog_hasLeft zero one hzo args hpl .compare (Sum.inr true) hg
    not_false

/-- **The failing verdict**: at the `ltp` cell with some address below
disagreed, step off it into the copy-back's walk home. -/
theorem step_compare_exit_neg
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : dt.CtlIx → A} {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr vp : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr) (hvp : WMIncr WMLe vp ltpAddr)
    (hno : ¬∀ r, WMSetLt WMLe r ltpAddr →
      ∀ i, (st.old i r ↔ st.new i r)) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) ltpAddr),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCmpP fc),
        Sum.inl vp,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  rw [sweepState, if_neg hno]
  refine Prog.step_moveBack hR hlin hvp (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.compare
      (Sum.inr false)).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir ltpAddr) := by
    change (dt.prog zero one hzo args hpl).passTracks Slot.mir
      (dt.back zero one dt.dd0Le st) st.mir ltpAddr Slot.ltp = one
    rw [Prog.passTracks_of_ne dt.ltp_ne_mir, back_ltp, hltp]
    exact bitVal_pos rfl
  exact dt.prog_hasLeft zero one hzo args hpl .compare (Sum.inr false) hg
    not_false

/-- **COPY's folded first step**: `homeCmp`'s exit rewrites the empty
address's cell — every `old` track taking its `new` digit — and lands at
its successor, in the copy-back's frontier presentation there. -/
theorem step_homeCmp_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCmpP fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args st v')) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have h0v' : WMSetLt WMLe (fun _ => False) v' :=
    (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hvi, ne_of_wmIncr hvi⟩
  -- the frontier's presentation differs from the state's only at the cell
  have hframe : ∀ r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd → Prop, r ≠ (fun _ => False) →
      dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st v') r =
        dt.back zero one dt.dd0Le st r := by
    intro r hr
    funext sl
    match sl with
    | .old i =>
      change bitVal zero one
        ((dt.copySt zero one hzo args st v').old i r) = _
      simp only [copySt]
      have hne : ¬WMSetLt WMLe r v' := fun hlt => hr
        ((isLinOrd_wmSetLe hlin).2.2.1 r (fun _ => False)
          ((wmSetLt_iff_of_wmIncr hlin hvi r).mp hlt)
          (wmSetLe_of_empty hlin (fun _ hc => hc) r))
      rw [if_neg hne]
      rfl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
  -- the written symbol is the frontier's presentation at the cell
  have hwr : (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
        OuterPh.copyP).wrG
      ((dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) =
      (dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st v'))
        st.mir (fun _ => False) := by
    funext sl
    by_cases ho : ∃ i, sl = Slot.old i
    · obtain ⟨i, rfl⟩ := ho
      have hL : (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
            OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le st) st.mir (fun _ => False))
            (Slot.old i) =
          (dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)
            (Slot.new i) := rfl
      rw [hL, Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir
          from fun h => nomatch h),
        Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir
          from fun h => nomatch h)]
      change bitVal zero one (st.new i (fun _ => False)) =
        bitVal zero one
          ((dt.copySt zero one hzo args st v').old i (fun _ => False))
      simp only [copySt]
      rw [if_pos h0v']
    · have hL : (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
            OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) sl =
          (dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le st) st.mir (fun _ => False) sl := by
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
      rw [hL]
      by_cases hm : sl = Slot.mir
      · subst hm
        change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
          (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .mir => exact absurd rfl hm
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
  refine Prog.step_move hR hlin hvi hframe ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.homeCmp
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  have h := dt.prog_hasRight zero one hzo args hpl .homeCmp (Sum.inr ()) hg
    trivial
  rw [show ((dt.progAsm zero one hzo args).rule OuterSite.homeCmp
      (Sum.inr ())).wr fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) =
      (dt.prog zero one hzo args hpl).passTracks Slot.mir
        (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st v'))
        st.mir (fun _ => False) from hwr] at h
  exact h

/-- **The copy-back from an arbitrary start**: the generalization of
`DescriptiveComplexity.Pfp.PfpData.reaches_copy` the folded first step
needs. -/
theorem reaches_copyFrom
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : dt.CtlIx → A} {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr)
    {s₀ : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe s₀ ltpAddr) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl s₀,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args st s₀)) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args st ltpAddr)) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  refine WriteSweepKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF) OuterPh.copyP)
    (rEmb := fun ρ => ⟨OuterSite.copy, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_copy zero one hzo args hpl ρ)
    hR hlin dt.ltp_ne_mir (m := st.mir)
    (restAt := fun s => dt.back zero one dt.dd0Le
      (dt.copySt zero one hzo args st s))
    (ltpAddr := ltpAddr)
    (fun k r => by
      simp only [copyKit]
      rw [back_ltp]
      simp only [copySt, hltp]
      rfl)
    (fc := fc) hle ((isLinOrd_wmSetLe hlin).1 ltpAddr) ?_ ?_
  · intro s u hi _ _ r hr
    funext sl
    match sl with
    | .old i =>
      change bitVal zero one ((dt.copySt zero one hzo args st u).old i r) =
        bitVal zero one ((dt.copySt zero one hzo args st s).old i r)
      simp only [copySt]
      have hiff : WMSetLt WMLe r u ↔ WMSetLt WMLe r s := by
        rw [wmSetLt_iff_of_wmIncr hlin hi r, wmSetLt_iff r s]
        exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩
      by_cases hc : WMSetLt WMLe r s
      · rw [if_pos (hiff.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
  · intro s u hi _ _
    have hsu : WMSetLt WMLe s u :=
      (wmSetLt_iff s u).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
    funext sl
    rw [show (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
      OuterPh.copyP).t = (Slot.mir : dt.SlotIx) from rfl]
    by_cases ho : ∃ i, sl = Slot.old i
    · obtain ⟨i, rfl⟩ := ho
      have hL : (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
            OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s) (Slot.old i) =
          (dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s (Slot.new i) := rfl
      rw [hL, Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir
          from fun h => nomatch h),
        Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h)]
      change bitVal zero one ((dt.copySt zero one hzo args st s).new i s) =
        bitVal zero one ((dt.copySt zero one hzo args st u).old i s)
      simp only [copySt, if_pos hsu]
    · have hL : (dt.copyKit (A := A) (Q := dt.CtlIx) (P := dt.PF)
            OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s) sl =
          (dt.prog zero one hzo args hpl).passTracks Slot.mir
            (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s sl := by
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
      rw [hL]
      by_cases hm : sl = Slot.mir
      · subst hm
        change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
          (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .mir => exact absurd rfl hm
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl

/-- **The copy-back's exit**: at the `ltp` cell, step off it into its walk
home. -/
theorem step_copy_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : dt.CtlIx → A} {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr vp : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr) (hvp : WMIncr WMLe vp ltpAddr) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args st ltpAddr)) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCopyP fc),
        Sum.inl vp,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args st ltpAddr)) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  refine Prog.step_moveBack hR hlin hvp (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.copy
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le
          (dt.copySt zero one hzo args st ltpAddr)) st.mir ltpAddr) := by
    change (dt.prog zero one hzo args hpl).passTracks Slot.mir
      (dt.back zero one dt.dd0Le (dt.copySt zero one hzo args st ltpAddr))
      st.mir ltpAddr Slot.ltp = one
    rw [Prog.passTracks_of_ne dt.ltp_ne_mir, back_ltp]
    change bitVal zero one (st.ltp ltpAddr) = one
    rw [hltp]
    exact bitVal_pos rfl
  exact dt.prog_hasLeft zero one hzo args hpl .copy (Sum.inr ()) hg not_false

/-- **The copy-back's walk home exits into the next sweep**: off the marker,
rightwards, into the first checkpoint. -/
theorem step_homeCopy_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCopyP fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fc), Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.homeCopy
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo args hpl .homeCopy (Sum.inr ()) hg
    trivial

/-- **The output's walk home exits into the out machinery**: off the
marker, rightwards, into its entry checkpoint. -/
theorem step_homeOut_exit
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe (fun _ => False) v') {fc : dt.CtlIx → A}
    {st : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeOutP fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.sub (dt.smEntryOut))) fc), Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.mir
          (dt.back zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.homeOut
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracks
        Slot.mir (dt.back zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo args hpl .homeOut (Sum.inr ()) hg
    trivial

/-! ### Closing a stage

After the sweep's last round the machine stands at the first checkpoint on
the `ltp` cell. One more evaluation runs there (its writes are junk the
copy never propagates and nothing reads), then the erasing `.dspB` exit,
the reset, the mirror clear and the convergence sweep. Its verdict closes
the stage: failing, the copy-back rewrites every `old` track and the walk
home re-enters the evaluation — the next stage's entry; passing, the walk
home enters the out machinery. -/

/-- **A failed stage closes into the next**: from the first checkpoint on
the `ltp` cell (the evaluation there a hypothesis) to the first checkpoint
at the empty address, every `old` track below the top rewritten to its
`new` digit. -/
theorem stageClose_neg
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot)) (hneT : ∃ x, ltpAddr x)
    {st0 stT : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {fs0 fsT : dt.CtlIx → A}
    (hspineT : Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs0), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st0) st0.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk (Fin.last dt.nv))) fsT), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le stT) stT.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (hwkT : stT.wk = fun r => r = ltpAddr)
    (hltpT : stT.ltp = fun r => r = ltpAddr)
    (hbotT : stT.bot = fun r => r = (fun _ => False))
    (hno : ¬∀ r, WMSetLt WMLe r ltpAddr →
      ∀ i, (stT.old i r ↔ stT.new i r)) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs0), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st0) st0.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fsT), Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            (dt.copySt zero one hzo args
              { dt.atSt (dt.offSt stT) (fun _ => False) with
                mir := fun _ => False } ltpAddr))
          (dt.copySt zero one hzo args
              { dt.atSt (dt.offSt stT) (fun _ => False) with
                mir := fun _ => False } ltpAddr).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  obtain ⟨v₁, hiE⟩ := exists_wmIncr (Le := WMLe
    (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)) hlin
    (s := fun _ => False) ⟨gbot, not_false⟩
  have hregE : ¬∃ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have h := wmSetLt_empty_wmSeg (A := Univ A (dt.RIx zero one hzo args)
      dt.PF dt.KIx dt.dd) hlin u
    rw [hu] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  obtain ⟨vp, hvp⟩ := exists_wmPred hlin hneT
  have hle_vp : WMSetLe WMLe (fun _ => False) vp :=
    wmSetLe_of_empty hlin (fun _ hc => hc) vp
  -- the successor of the empty address stays within the stretch
  have hle₁ : WMSetLe WMLe v₁ ltpAddr := by
    rcases hset.2.2.2 v₁ ltpAddr with hc | hc
    · exact hc
    · have hlt' : ¬WMSetLt WMLe ltpAddr v₁ := by
        intro h
        have hle0 := (wmSetLt_iff_of_wmIncr hlin hiE ltpAddr).mp h
        obtain ⟨x, hx⟩ := hneT
        have := hset.2.2.1 ltpAddr (fun _ => False) hle0
          (wmSetLe_of_empty hlin (fun _ hc' => hc') ltpAddr)
        rw [this] at hx
        exact hx
      rw [wmSetLt_iff] at hlt'
      rcases Classical.em (ltpAddr = v₁) with heq | hne
      · exact heq ▸ hset.1 v₁
      · exact absurd ⟨hc, hne⟩ hlt'
  set stR : TapeSt dt A (dt.RIx zero one hzo args) dt.PF :=
    dt.atSt (dt.offSt stT) (fun _ => False) with hstR
  set stC : TapeSt dt A (dt.RIx zero one hzo args) dt.PF :=
    { stR with mir := fun _ => False } with hstC
  -- the evaluation at the top address
  refine hspineT.trans ?_
  -- hand the walk to MIRROR, reset, clear
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_val zero one hzo args stT) (dt.back_mir zero one hzo args stT)]
  refine (reaches_reset2 hR hlin hbot hlt hwkT (by rw [hltpT]) hbotT).trans
    ?_
  refine (Relation.ReflTransGen.single
    (step_reset2_exit hR hlin hiE rfl hregE)).trans ?_
  refine (reaches_clearMir2 hR hlin hord htop hbot (st := stR) rfl).trans ?_
  -- the convergence sweep, its first step folded into the clear's exit
  refine (Relation.ReflTransGen.single
    (step_clearMir2_exit hR hlin hiE (st := stC) rfl hregE)).trans ?_
  refine (reaches_compareFrom hR hlin (st := stC) hltpT hle₁).trans ?_
  -- the failing verdict, the walk home, the copy-back and its walk home
  refine (Relation.ReflTransGen.single
    (step_compare_exit_neg hR hlin (st := stC) hltpT hvp hno)).trans ?_
  refine (dt.reaches_homeCmp zero one hzo args hpl hR hlin (st := stC) rfl hle_vp).trans ?_
  refine (Relation.ReflTransGen.single
    (step_homeCmp_exit hR hlin hiE (st := stC) rfl hregE)).trans ?_
  refine (reaches_copyFrom hR hlin (st := stC) hltpT hle₁).trans ?_
  refine (Relation.ReflTransGen.single
    (step_copy_exit hR hlin (st := stC) hltpT hvp)).trans ?_
  refine (dt.reaches_homeCopy zero one hzo args hpl hR hlin
    (st := dt.copySt zero one hzo args stC ltpAddr) rfl hle_vp).trans ?_
  refine (Relation.ReflTransGen.single
    (step_homeCopy_exit hR hlin hiE rfl hregE)).trans ?_
  -- hand the walk back to VAL and step back to the marker
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_mir zero one hzo args (dt.copySt zero one hzo args stC ltpAddr))
    (dt.back_val zero one hzo args
      (dt.copySt zero one hzo args stC ltpAddr))]
  exact Relation.ReflTransGen.single (step_evalChk_back hR hlin rfl hiE)

/-- **A passed stage closes into the output**: the same ring up to the
verdict, then the walk home and the dispatch into the out machinery's
entry checkpoint. -/
theorem stageClose_pos
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot)) (hneT : ∃ x, ltpAddr x)
    {v₁ : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hiE : WMIncr WMLe (fun _ => False) v₁)
    {st0 stT : TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {fs0 fsT : dt.CtlIx → A}
    (hspineT : Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs0), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st0) st0.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk (Fin.last dt.nv))) fsT), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le stT) stT.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (hwkT : stT.wk = fun r => r = ltpAddr)
    (hltpT : stT.ltp = fun r => r = ltpAddr)
    (hbotT : stT.bot = fun r => r = (fun _ => False))
    (hyes : ∀ r, WMSetLt WMLe r ltpAddr →
      ∀ i, (stT.old i r ↔ stT.new i r)) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) fs0), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le st0) st0.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.sub (dt.smEntryOut))) fsT), Sum.inl v₁,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            { dt.atSt (dt.offSt stT) (fun _ => False) with
              mir := fun _ => False })
          { dt.atSt (dt.offSt stT) (fun _ => False) with
              mir := fun _ => False }.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have hset := isLinOrd_wmSetLe hlin
  have hregE : ¬∃ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have h := wmSetLt_empty_wmSeg (A := Univ A (dt.RIx zero one hzo args)
      dt.PF dt.KIx dt.dd) hlin u
    rw [hu] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  obtain ⟨vp, hvp⟩ := exists_wmPred hlin hneT
  have hle_vp : WMSetLe WMLe (fun _ => False) vp :=
    wmSetLe_of_empty hlin (fun _ hc => hc) vp
  have hle₁ : WMSetLe WMLe v₁ ltpAddr := by
    rcases hset.2.2.2 v₁ ltpAddr with hc | hc
    · exact hc
    · have hlt' : ¬WMSetLt WMLe ltpAddr v₁ := by
        intro h
        have hle0 := (wmSetLt_iff_of_wmIncr hlin hiE ltpAddr).mp h
        obtain ⟨x, hx⟩ := hneT
        have := hset.2.2.1 ltpAddr (fun _ => False) hle0
          (wmSetLe_of_empty hlin (fun _ hc' => hc') ltpAddr)
        rw [this] at hx
        exact hx
      rw [wmSetLt_iff] at hlt'
      rcases Classical.em (ltpAddr = v₁) with heq | hne
      · exact heq ▸ hset.1 v₁
      · exact absurd ⟨hc, hne⟩ hlt'
  set stR : TapeSt dt A (dt.RIx zero one hzo args) dt.PF :=
    dt.atSt (dt.offSt stT) (fun _ => False) with hstR
  set stC : TapeSt dt A (dt.RIx zero one hzo args) dt.PF :=
    { stR with mir := fun _ => False } with hstC
  refine hspineT.trans ?_
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_val zero one hzo args stT) (dt.back_mir zero one hzo args stT)]
  refine (reaches_reset2 hR hlin hbot hlt hwkT (by rw [hltpT]) hbotT).trans
    ?_
  refine (Relation.ReflTransGen.single
    (step_reset2_exit hR hlin hiE rfl hregE)).trans ?_
  refine (reaches_clearMir2 hR hlin hord htop hbot (st := stR) rfl).trans ?_
  refine (Relation.ReflTransGen.single
    (step_clearMir2_exit hR hlin hiE (st := stC) rfl hregE)).trans ?_
  refine (reaches_compareFrom hR hlin (st := stC) hltpT hle₁).trans ?_
  refine (Relation.ReflTransGen.single
    (step_compare_exit_pos hR hlin (st := stC) hltpT hvp hyes)).trans ?_
  refine (dt.reaches_homeOut zero one hzo args hpl hR hlin (st := stC) rfl hle_vp).trans ?_
  refine (Relation.ReflTransGen.single
    (step_homeOut_exit hR hlin hiE (st := stC) rfl hregE)).trans ?_
  rw [dt.trackTape_back_swap zero one hzo args hpl
    (dt.back_mir zero one hzo args stC) (dt.back_val zero one hzo args stC)]

/-! ### MAIN

The loop: one sweep and one stage-closing ring per stage, iterated while
the convergence sweep fails, and the passing ring at the first stage that
stabilizes. Everything semantic — the per-stage tape and control families
and the runs themselves — is a hypothesis family; the loop is a plain
induction on the first converged index. -/

/-- **The MAIN loop**: from the first stage's entry at the empty address,
through one sweep and one closing ring per stage, to the out machinery's
entry checkpoint at the first stage whose convergence sweep passes. -/
theorem reaches_main
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd
      (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hlt : WMSetLt WMLe ltpAddr (wmSeg gbot)) (hneT : ∃ x, ltpAddr x)
    {v₁ : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hiE : WMIncr WMLe (fun _ => False) v₁)
    {N : ℕ}
    {entrySt topSt stT : ℕ → TapeSt dt A (dt.RIx zero one hzo args) dt.PF}
    {entryFs topFs fsT : ℕ → dt.CtlIx → A}
    (hsweep : ∀ n, n ≤ N → Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (entryFs n)), Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (entrySt n)) (entrySt n).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (topFs n)), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (topSt n)) (topSt n).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (hspineT : ∀ n, n ≤ N → Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (topFs n)), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (topSt n)) (topSt n).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk (Fin.last dt.nv))) (fsT n)), Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (stT n)) (stT n).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩)
    (hwkT : ∀ n, n ≤ N → (stT n).wk = fun r => r = ltpAddr)
    (hltpT : ∀ n, n ≤ N → (stT n).ltp = fun r => r = ltpAddr)
    (hbotT : ∀ n, n ≤ N → (stT n).bot = fun r => r = (fun _ => False))
    (hnotconv : ∀ n, n < N → ¬∀ r, WMSetLt WMLe r ltpAddr →
      ∀ i, ((stT n).old i r ↔ (stT n).new i r))
    (hconv : ∀ r, WMSetLt WMLe r ltpAddr →
      ∀ i, ((stT N).old i r ↔ (stT N).new i r))
    (hnextSt : ∀ n, n < N → entrySt (n + 1) =
      dt.copySt zero one hzo args
        { dt.atSt (dt.offSt (stT n)) (fun _ => False) with
          mir := fun _ => False } ltpAddr)
    (hnextFs : ∀ n, n < N → entryFs (n + 1) = fsT n) :
    Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (entryFs 0)), Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (entrySt 0)) (entrySt 0).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.sub (dt.smEntryOut))) (fsT N)), Sum.inl v₁,
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le
            { dt.atSt (dt.offSt (stT N)) (fun _ => False) with
              mir := fun _ => False })
          { dt.atSt (dt.offSt (stT N)) (fun _ => False) with
              mir := fun _ => False }.val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  -- reach every stage's entry, by induction
  have key : ∀ n, n ≤ N → Relation.ReflTransGen
      (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (entryFs 0)), Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (entrySt 0)) (entrySt 0).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt
          (.evalP (.chk 0)) (entryFs n)), Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTape Slot.val
          (dt.back zero one dt.dd0Le (entrySt n)) (entrySt n).val)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
    intro n
    induction n with
    | zero => exact fun _ => Relation.ReflTransGen.refl
    | succ n ih =>
      intro hn
      have hnN : n < N := hn
      have hclose := stageClose_neg hR hlin hord htop hbot hlt hneT
        (hspineT n (Nat.le_of_lt hnN)) (hwkT n (Nat.le_of_lt hnN))
        (hltpT n (Nat.le_of_lt hnN)) (hbotT n (Nat.le_of_lt hnN))
        (hnotconv n hnN)
      rw [hnextSt n hnN, hnextFs n hnN]
      exact (ih (Nat.le_of_lt hnN)).trans
        ((hsweep n (Nat.le_of_lt hnN)).trans hclose)
  refine (key N le_rfl).trans ((hsweep N le_rfl).trans ?_)
  exact stageClose_pos hR hlin hord htop hbot hlt hneT hiE
    (hspineT N le_rfl) (hwkT N le_rfl) (hltpT N le_rfl) (hbotT N le_rfl)
    hconv

end PfpData

end Pfp

end DescriptiveComplexity
