/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpVar
import DescriptiveComplexity.Problems.Wide.PfpRunElem

/-!
# One variable's machinery: the run

The run theorem of `DescriptiveComplexity.Pfp.PfpData.varRule` – the spine of
the per-variable evaluation. The two abstract machineries stay abstract: the
gates' run and the matrix's runs enter as *hypotheses*, one per VAL-loop
round, and this file contributes exactly the spine – the entry dispatch, the
VAL clear (`DescriptiveComplexity.Pfp.ClearKit`), the rounds of matrix pass,
exhaustion test (`DescriptiveComplexity.Pfp.TestKit`) and block-indexed
increment (`DescriptiveComplexity.Pfp.IncrKit`) with the fold updates riding
in the dispatches, and the arrival at the exit checkpoint once VAL is
exhausted.

The background conditions every kit reads are bundled once
(`DescriptiveComplexity.Pfp.PfpData.VarBg`); the VAL register's contents over
the rounds are an abstract family `mV` over an abstract enumeration, exactly
as in the element loop's run.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)
variable {A R P Q PG PX SG SX : Type}
variable [Fintype Q] [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {ShG : SG → Type} {ShX : SX → Type}
variable {PR : Prog A R P Q dt.SlotIx dt.KIx dt.dd}

/-- **The background conditions of the VAL loop's kits**, bundled: the
working-cell marker sits at `v`, the register file's marks are in place, and
the VAL slot backs the given track. -/
def VarBg (zero one : A) (v : Univ A R P dt.KIx dt.dd → Prop)
    (gtop : Univ A R P dt.KIx dt.dd)
    (rest : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A)
    (mval : Univ A R P dt.KIx dt.dd → Prop) : Prop :=
  (∀ r, rest r Slot.wk = bitVal zero one (r = v)) ∧
  (∀ r, rest r Slot.reg =
    bitVal zero one (∃ u : Univ A R P dt.KIx dt.dd, r = wmSeg u)) ∧
  (∀ r, rest r Slot.regLast = bitVal zero one (r = wmSeg gtop)) ∧
  (∀ (u : Univ A R P dt.KIx dt.dd) (b : Option (Fin dt.ko ⊕ Fin dt.ki)),
    rest (wmSeg u) (Slot.blk b) = bitVal zero one (tagBlk u.1 = b)) ∧
  (∀ r, rest r Slot.val = bitVal zero one (regBit mval r))

/-- **The exhaustion condition of a VAL-loop round**: the register's bit at
an element is set exactly when the element lies in an inner block – the
"VAL = Kin-top" pattern the exhaustion test decides. -/
def InnerFull (mv : Univ A R P dt.KIx dt.dd → Prop)
    (u : Univ A R P dt.KIx dt.dd) : Prop :=
  mv u ↔ ∃ j : Fin dt.ki, tagBlk u.1 = some (Sum.inr j)

section VarRun

variable {emb : VarPh dt.CarryB PG PX → P}
variable {ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P}
variable {ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P}
variable {pgEntry pxEntry exitPh : P}
variable {newSlot : dt.SlotIx} {gateFlag : Q}
variable {accBit : (Q → A) → Prop}
variable {enterSt initSt postFold : (Q → A) → (dt.SlotIx → A) → Q → A}
variable {storeCarry : dt.CarryB → (Q → A) → (dt.SlotIx → A) → Q → A}
variable {rEmb : ∀ i : VarSite SG SX, VarSh SG SX ShG ShX dt.CarryB i → R}
variable (hrules : ∀ (i : VarSite SG SX) (ρ : VarSh SG SX ShG ShX dt.CarryB i),
  PR.rules (rEmb i ρ) = dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry
    pxEntry exitPh newSlot gateFlag accBit enterSt initSt postFold
    storeCarry i ρ)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : VarSite SG SX}
    {ρ : VarSh SG SX ShG ShX dt.CarryB i}
    {f f' : Q → A} {g g' : dt.SlotIx → A} {p p' : P}
    (hg : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).guard f g)
    (hp : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).srcPh = p)
    (hp' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).dstPh = p')
    (hf' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).dstSt f g
        = f')
    (hg' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).wr f g
        = g')
    (hmr : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : VarSite SG SX}
    {ρ : VarSh SG SX ShG ShX dt.CarryB i}
    {f f' : Q → A} {g g' : dt.SlotIx → A} {p p' : P}
    (hg : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).guard f g)
    (hp : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).srcPh = p)
    (hp' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).dstPh = p')
    (hf' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).dstSt f g
        = f')
    (hg' : (dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).wr f g
        = g')
    (hml : ¬(dt.varRule PR.zero PR.one emb ruleG ruleX pgEntry pxEntry exitPh
      newSlot gateFlag accBit enterSt initSt postFold storeCarry i ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable {rest : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable {mval : Univ A R P dt.KIx dt.dd → Prop}
variable (hbg : dt.VarBg PR.zero PR.one v gtop rest mval)
variable {f₀ fG : Q → A}
variable (hGates : Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
  ⟨Sum.inr (PR.stElt pgEntry (enterSt f₀ (rest v))), Sum.inl v',
    wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
  ⟨Sum.inr (PR.stElt (emb .vchk1) fG), Sum.inl v,
    wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩)

include hrules hR hlin hbot hv hvi hbg hGates in
/-- **The machinery, entered**: from the entry checkpoint at the marker,
through the gates, to the verdict checkpoint. -/
theorem var_run_gates :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk1) fG), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩ := by
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  obtain ⟨hwkS, hrg, -, -, hval⟩ := hbg
  have hentry : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pgEntry (enterSt f₀ (rest v))), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule dt hrules (i := .vchk0) (ρ := .dspA) ?_ rfl rfl
      ?_ rfl trivial
    · constructor
      · rw [Prog.passTracks_of_ne hne_wk_val, hwkS]
        exact bitVal_pos rfl
      · rw [Prog.passTracks_of_ne hne_reg_val, hrg,
          bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
        exact PR.zero_ne_one
    · change enterSt f₀ (PR.passTracks Slot.val rest mval v) =
        enterSt f₀ (rest v)
      rw [passTracks_of_back hval v]
  exact (Relation.ReflTransGen.single hentry).trans hGates

variable (hflag : fG gateFlag = PR.one)
variable {restC : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable (hbgC : dt.VarBg PR.zero PR.one v gtop restC (fun _ => False))
variable (hCoff : ∀ r s, s ≠ Slot.val → restC r s = rest r s)
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a, a₀ ≤ a) (htopV : ∀ a, a ≤ aT)
variable {mV : ιV → Univ A R P dt.KIx dt.dd → Prop}
variable (hmV0 : mV a₀ = fun _ => False)
variable {restM restO : ιV → (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable (hbgM : ∀ a, dt.VarBg PR.zero PR.one v gtop (restM a) (mV a))
variable (hbgO : ∀ a, dt.VarBg PR.zero PR.one v gtop (restO a) (mV a))
variable (hM0 : restM a₀ = restC)
variable {fM fX : ιV → Q → A}
variable (hfM0 : fM a₀ = initSt fG (restC v))
variable (hMatrix : ∀ a : ιV,
  Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
    ⟨Sum.inr (PR.stElt pxEntry (fM a)), Sum.inl v',
      wideTape (PR.trackTape Slot.val (restM a) (mV a)) (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (emb .mchk1) (fX a)), Sum.inl v,
      wideTape (PR.trackTape Slot.val (restO a) (mV a)) (PR.syElt PR.blank)⟩)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr WMLe (mV a) (mV a'))
variable (hOMagree : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  ∀ r s, s ≠ Slot.val → restM a' r s = restO a r s)
variable (hStore : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  ∀ u₀ : Univ A R P dt.KIx dt.dd, ¬mV a u₀ →
    (∀ w, WMLt WMLe u₀ w → mV a w) →
    storeCarry (tagBlk u₀.1) (postFold (fX a) (restO a v)) (restO a v) = fM a')
variable (hTestT : ∀ u, dt.InnerFull (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (mV a) u)

omit hbgM in
include hrules hR hlin htop hbot hv hvi hbg hGates hflag hbgC hCoff hbotV htopV
  hmV0 hbgO hM0 hfM0 hMatrix hIncr hOMagree hStore hTestT hTestF in
/-- **One variable's machinery runs**: from the entry checkpoint at the
marker, through the gates, the VAL clear and the rounds of matrix pass, test
and increment, to the exit checkpoint – VAL exhausted, the verdict spelled by
the accumulators the dispatches folded. -/
theorem var_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2) (postFold (fX aT) (restO aT v))),
        Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hzo := PR.zero_ne_one
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_blk_val : ∀ b, (Slot.blk b : dt.SlotIx) ≠ Slot.val :=
    fun _ h => nomatch h
  -- marker-side guard facts, for an arbitrary VAL-backed background
  have hgwk : ∀ (rst : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A)
      (mv mw : Univ A R P dt.KIx dt.dd → Prop),
      dt.VarBg PR.zero PR.one v gtop rst mv →
      PR.passTracks Slot.val rst mw v Slot.wk = PR.one := by
    intro rst mv mw hb
    rw [Prog.passTracks_of_ne hne_wk_val, hb.1]
    exact bitVal_pos rfl
  have hgrg : ∀ (rst : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A)
      (mv mw : Univ A R P dt.KIx dt.dd → Prop),
      dt.VarBg PR.zero PR.one v gtop rst mv →
      PR.passTracks Slot.val rst mw v Slot.reg ≠ PR.one := by
    intro rst mv mw hb
    rw [Prog.passTracks_of_ne hne_reg_val, hb.2.1,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact hzo
  -- the marker symbol under any VAL-walked presentation is the background's
  have hsym : ∀ (rst : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A)
      (mv mw : Univ A R P dt.KIx dt.dd → Prop),
      dt.VarBg PR.zero PR.one v gtop rst mv →
      PR.passTracks Slot.val rst mw v = rst v := by
    intro rst mv mw hb
    funext s
    by_cases hs : s = Slot.val
    · rw [hs]
      change (if (Slot.val : dt.SlotIx) = Slot.val
        then bitVal PR.zero PR.one (regBit mw v) else rst v Slot.val) =
        rst v Slot.val
      rw [if_pos rfl,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec.1), hb.2.2.2.2,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec.1)]
    · exact Prog.passTracks_of_ne hs mw v
  -- entry through the gates
  have hopen := dt.var_run_gates hrules hR hlin hbot hv hvi
    ⟨hbg.1, hbg.2.1, hbg.2.2.1, hbg.2.2.2.1, hbg.2.2.2.2⟩ hGates
  -- the dispatch into the VAL clear
  have hdspC : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk1) fG), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.clearValP .up)) fG), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .vchk1) (ρ := .dspA)
      ⟨⟨hgwk rest mval mval hbg, hgrg rest mval mval hbg⟩, hflag⟩
      rfl rfl rfl rfl trivial
  -- the VAL clear
  have hclear := ClearKit.reaches
    (κ := ClearKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
      (fun t => emb (.clearValP t)))
    (fun ρ => hrules .clearVal (Sum.inl ρ)) hR hlin
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
    htop hbot hv hbg.2.1 hbg.2.2.1 hbg.1 (fc := fG) (s := v') (m := mval)
  -- hand the cleared track to the cleared background
  have hclearedT : PR.trackTape Slot.val rest (fun _ => False) =
      PR.trackTape Slot.val restC (fun _ => False) := by
    refine funext fun r => ?_
    change PR.syElt (fun s => if s = Slot.val
        then bitVal PR.zero PR.one (regBit (fun _ => False) r) else rest r s) =
      PR.syElt (fun s => if s = Slot.val
        then bitVal PR.zero PR.one (regBit (fun _ => False) r) else restC r s)
    refine congrArg _ (funext fun s => ?_)
    by_cases hs : s = Slot.val
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      exact (hCoff r s hs).symm
  -- the dispatch into the first matrix pass
  have hdspM : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.clearValP .run)) fG), Sum.inl v,
        wideTape (PR.trackTape Slot.val restC (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pxEntry (fM a₀)), Sum.inl v',
        wideTape (PR.trackTape Slot.val restC (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule dt hrules (i := .clearVal) (ρ := Sum.inr ())
      ⟨hgwk restC _ _ hbgC, hgrg restC _ _ hbgC⟩ rfl rfl ?_ rfl trivial
    change initSt fG (PR.passTracks Slot.val restC (fun _ => False) v) = fM a₀
    rw [hsym restC _ _ hbgC, hfM0]
  -- the tape at the first matrix entry
  have hMT0 : PR.trackTape Slot.val restC (fun _ => False) =
      PR.trackTape Slot.val (restM a₀) (mV a₀) := by
    rw [hM0, hmV0]
  -- one full round from the post-matrix checkpoint to the next
  have hstepRound : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb .mchk1) (fX a)), Sum.inl v,
          wideTape (PR.trackTape Slot.val (restO a) (mV a))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb .mchk1) (fX a')), Sum.inl v,
          wideTape (PR.trackTape Slot.val (restO a') (mV a'))
            (PR.syElt PR.blank)⟩ := by
    intro a a' hlt hnb
    -- the post-fold dispatch into the exhaustion test
    have hdspT : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb .mchk1) (fX a)), Sum.inl v,
          wideTape (PR.trackTape Slot.val (restO a) (mV a))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.valTestP .up))
            (postFold (fX a) (restO a v))), Sum.inl v',
          wideTape (PR.trackTape Slot.val (restO a) (mV a))
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule dt hrules (i := .mchk1) (ρ := .dspA)
        ⟨hgwk (restO a) _ _ (hbgO a), hgrg (restO a) _ _ (hbgO a)⟩
        rfl rfl ?_ rfl trivial
      change postFold (fX a) (PR.passTracks Slot.val (restO a) (mV a) v) =
        postFold (fX a) (restO a v)
      rw [hsym (restO a) _ _ (hbgO a)]
    -- the failing exhaustion test
    have hcompat : ∀ u : Univ A R P dt.KIx dt.dd,
        ((PR.passTracks Slot.val (restO a) (mV a) (wmSeg u)) Slot.val = PR.one ↔
          ∃ j : Fin dt.ki, (PR.passTracks Slot.val (restO a) (mV a) (wmSeg u))
            (Slot.blk (some (Sum.inr j))) = PR.one) ↔
          dt.InnerFull (mV a) u := by
      intro u
      rw [Prog.passTracks_wmSeg_apply hlin]
      refine iff_congr (bitVal_iff hzo) (exists_congr fun j => ?_) |>.trans
        Iff.rfl
      rw [Prog.passTracks_of_ne (hne_blk_val _), (hbgO a).2.2.2.1 u]
      exact bitVal_iff hzo
    obtain ⟨u, hu⟩ := hTestF a (lt_of_lt_of_le hlt (htopV a'))
    have htest := TestKit.reaches_neg
      (κ := TestKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
        (fun g => (g Slot.val = PR.one ↔
          ∃ j : Fin dt.ki, g (.blk (some (Sum.inr j))) = PR.one))
        (fun t => emb (.valTestP t)))
      (fun ρ => hrules .valTest (Sum.inl ρ)) hR hlin
      (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
      htop hbot hv (hbgO a).2.1 (hbgO a).2.2.1 (hbgO a).1
      (Test := dt.InnerFull (mV a)) hcompat
      (fc := postFold (fX a) (restO a v)) (s := v') hu
    -- the dispatch into the increment
    have hdspI : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.valTestP .tn))
            (postFold (fX a) (restO a v))), Sum.inl v,
          wideTape (PR.trackTape Slot.val (restO a) (mV a))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.valIncrP .up))
            (postFold (fX a) (restO a v))), Sum.inl v',
          wideTape (PR.trackTape Slot.val (restO a) (mV a))
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      exact hasRight_of_rule dt hrules (i := .valTest) (ρ := Sum.inr false)
        ⟨hgwk (restO a) _ _ (hbgO a), hgrg (restO a) _ _ (hbgO a)⟩
        rfl rfl rfl rfl trivial
    -- the increment
    obtain ⟨u₀, hu₀, hincr⟩ := IncrKit.reaches
      (κ := IncrKit.mk (A := A) (Q := Q) (B := dt.CarryB) Slot.val Slot.reg
        Slot.regLast Slot.wk (fun b => Slot.blk b) (fun t => emb (.valIncrP t)))
      (fun ρ => hrules .valIncr (Sum.inl ρ)) hR hlin
      (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
      (fun b h => nomatch h) htop hbot hv (hbgO a).2.1 (hbgO a).2.2.1
      (hbgO a).1 (blkOf := fun u => tagBlk u.1)
      (fun u b => (hbgO a).2.2.2.1 u b)
      (fc := postFold (fX a) (restO a v)) (s := v')
      (hIncr a a' hlt hnb)
    -- the store dispatch back into the matrix
    have hdspS : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.valIncrP (.pd (tagBlk u₀.1))))
            (postFold (fX a) (restO a v))), Sum.inl v,
          wideTape (PR.trackTape Slot.val (restO a) (mV a'))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pxEntry (fM a')), Sum.inl v',
          wideTape (PR.trackTape Slot.val (restO a) (mV a'))
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule dt hrules (i := .valIncr)
        (ρ := Sum.inr (tagBlk u₀.1))
        ⟨hgwk (restO a) _ _ (hbgO a), hgrg (restO a) _ _ (hbgO a)⟩
        rfl rfl ?_ rfl trivial
      change storeCarry (tagBlk u₀.1) (postFold (fX a) (restO a v))
        (PR.passTracks Slot.val (restO a) (mV a') v) = fM a'
      rw [hsym (restO a) _ _ (hbgO a)]
      exact hStore a a' hlt hnb u₀ hu₀.1 hu₀.2
    -- hand the incremented track to the next round's background
    have hMT : PR.trackTape Slot.val (restO a) (mV a') =
        PR.trackTape Slot.val (restM a') (mV a') := by
      refine funext fun r => ?_
      change PR.syElt (fun s => if s = Slot.val
          then bitVal PR.zero PR.one (regBit (mV a') r) else restO a r s) =
        PR.syElt (fun s => if s = Slot.val
          then bitVal PR.zero PR.one (regBit (mV a') r) else restM a' r s)
      refine congrArg _ (funext fun s => ?_)
      by_cases hs : s = Slot.val
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs]
        exact (hOMagree a a' hlt hnb r s hs).symm
    refine (Relation.ReflTransGen.single hdspT).trans ?_
    refine htest.trans ?_
    refine (Relation.ReflTransGen.single hdspI).trans ?_
    refine hincr.trans ?_
    refine (Relation.ReflTransGen.single hdspS).trans ?_
    rw [show wideTape (PR.trackTape Slot.val (restO a) (mV a'))
        (PR.syElt PR.blank) =
      wideTape (PR.trackTape Slot.val (restM a') (mV a'))
        (PR.syElt PR.blank) from
      congrArg (wideTape · (PR.syElt PR.blank)) hMT]
    exact hMatrix a'
  -- the loop over the rounds
  have hloop : Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .mchk1) (fX a₀)), Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO a₀) (mV a₀))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .mchk1) (fX aT)), Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩ := by
    refine reflTransGen_of_ordLoop (conf := fun a =>
      (⟨Sum.inr (PR.stElt (emb .mchk1) (fX a)), Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO a) (mV a))
          (PR.syElt PR.blank)⟩ :
          Config (WPoint (Univ A R P dt.KIx dt.dd)))) ?_ hbotV aT
    exact fun a a' hlt hnb => hstepRound a a' hlt hnb
  -- the passing exhaustion test at the top round
  have hcompatT : ∀ u : Univ A R P dt.KIx dt.dd,
      ((PR.passTracks Slot.val (restO aT) (mV aT) (wmSeg u)) Slot.val =
          PR.one ↔
        ∃ j : Fin dt.ki, (PR.passTracks Slot.val (restO aT) (mV aT) (wmSeg u))
          (Slot.blk (some (Sum.inr j))) = PR.one) ↔
        dt.InnerFull (mV aT) u := by
    intro u
    rw [Prog.passTracks_wmSeg_apply hlin]
    refine iff_congr (bitVal_iff hzo) (exists_congr fun j => ?_) |>.trans
      Iff.rfl
    rw [Prog.passTracks_of_ne (hne_blk_val _), (hbgO aT).2.2.2.1 u]
    exact bitVal_iff hzo
  have hdspT2 : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .mchk1) (fX aT)), Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.valTestP .up))
          (postFold (fX aT) (restO aT v))), Sum.inl v',
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule dt hrules (i := .mchk1) (ρ := .dspA)
      ⟨hgwk (restO aT) _ _ (hbgO aT), hgrg (restO aT) _ _ (hbgO aT)⟩
      rfl rfl ?_ rfl trivial
    change postFold (fX aT) (PR.passTracks Slot.val (restO aT) (mV aT) v) =
      postFold (fX aT) (restO aT v)
    rw [hsym (restO aT) _ _ (hbgO aT)]
  have htestT := TestKit.reaches_pos
    (κ := TestKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
      (fun g => (g Slot.val = PR.one ↔
        ∃ j : Fin dt.ki, g (.blk (some (Sum.inr j))) = PR.one))
      (fun t => emb (.valTestP t)))
    (fun ρ => hrules .valTest (Sum.inl ρ)) hR hlin
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
    htop hbot hv (hbgO aT).2.1 (hbgO aT).2.2.1 (hbgO aT).1
    (Test := dt.InnerFull (mV aT)) hcompatT
    (fc := postFold (fX aT) (restO aT v)) (s := v') hTestT
  -- the dispatch into the exit checkpoint, and its walk back
  have hdspX : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.valTestP .ty))
          (postFold (fX aT) (restO aT v))), Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2) (postFold (fX aT) (restO aT v))),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .valTest) (ρ := Sum.inr true)
      ⟨hgwk (restO aT) _ _ (hbgO aT), hgrg (restO aT) _ _ (hbgO aT)⟩
      rfl rfl rfl rfl trivial
  have hbackX : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk2) (postFold (fX aT) (restO aT v))),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk2) (postFold (fX aT) (restO aT v))),
        Sum.inl v,
        wideTape (PR.trackTape Slot.val (restO aT) (mV aT))
          (PR.syElt PR.blank)⟩ := by
    have hwkv' : PR.passTracks Slot.val (restO aT) (mV aT) v' Slot.wk ≠
        PR.one := by
      rw [Prog.passTracks_of_ne hne_wk_val, (hbgO aT).1,
        bitVal_neg (Ne.symm hvv')]
      exact hzo
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule dt hrules (i := .vchk2) (ρ := .stay)
      hwkv' rfl rfl rfl rfl not_false
  -- assemble
  refine hopen.trans ?_
  refine (Relation.ReflTransGen.single hdspC).trans ?_
  refine hclear.trans ?_
  rw [show wideTape (PR.trackTape Slot.val rest (fun _ => False))
      (PR.syElt PR.blank) =
    wideTape (PR.trackTape Slot.val restC (fun _ => False))
      (PR.syElt PR.blank) from
    congrArg (wideTape · (PR.syElt PR.blank)) hclearedT]
  refine (Relation.ReflTransGen.single hdspM).trans ?_
  rw [show wideTape (PR.trackTape Slot.val restC (fun _ => False))
      (PR.syElt PR.blank) =
    wideTape (PR.trackTape Slot.val (restM a₀) (mV a₀))
      (PR.syElt PR.blank) from
    congrArg (wideTape · (PR.syElt PR.blank)) hMT0]
  refine (hMatrix a₀).trans ?_
  refine hloop.trans ?_
  refine (Relation.ReflTransGen.single hdspT2).trans ?_
  refine htestT.trans ?_
  exact (Relation.ReflTransGen.single hdspX).trans
    (Relation.ReflTransGen.single hbackX)

/-! ### The two boundary steps a caller owes

A spine dispatches into the machinery at the successor of the marker, and
receives the exit at the successor again: the walk back into the entry
checkpoint, and the written exit step out of `vchk2`. -/

include hrules hR hlin hvi in
/-- **The walk back into the entry checkpoint**: arriving from a caller's
dispatch one cell right of the marker, the checkpoint steps back to it. -/
theorem step_var_back
    {rest : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {mval : Univ A R P dt.KIx dt.dd → Prop} {f : Q → A}
    (hwk : rest v' Slot.wk = bitVal PR.zero PR.one (v' = v)) :
    (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .vchk0) f), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩ := by
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkv' : PR.passTracks Slot.val rest mval v' Slot.wk ≠ PR.one := by
    rw [Prog.passTracks_of_ne hne_wk_val, hwk, bitVal_neg (Ne.symm hvv')]
    exact PR.zero_ne_one
  refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
  exact hasLeft_of_rule dt hrules (i := .vchk0) (ρ := .stay)
    hwkv' rfl rfl rfl rfl not_false

include hrules hR hlin hbot hv hvi in
/-- **The written exit step**: at the marker, the exit checkpoint writes
the variable's verdict into its stage slot and leaves right into the exit
phase, the control untouched. -/
theorem step_var_exit
    {rest rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {mval : Univ A R P dt.KIx dt.dd → Prop} {f : Q → A}
    (hbgV : dt.VarBg PR.zero PR.one v gtop rest mval)
    (hns : newSlot ≠ Slot.val)
    (hoff : ∀ r, r ≠ v → rest' r = rest r)
    (hupd : rest' v = Function.update (rest v) newSlot
      (bitVal PR.zero PR.one (accBit f))) :
    (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk2) f), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh f), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest' mval) (PR.syElt PR.blank)⟩ := by
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hupd' : Function.update (PR.passTracks Slot.val rest mval v) newSlot
      (bitVal PR.zero PR.one (accBit f)) =
        PR.passTracks Slot.val rest' mval v := by
    funext s
    by_cases hs : s = newSlot
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hns, hupd,
        Function.update_self]
    · rw [Function.update_of_ne hs]
      by_cases hsv : s = Slot.val
      · rw [hsv]
        change (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (regBit mval v) else rest v Slot.val) =
          (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (regBit mval v) else rest' v Slot.val)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hsv, Prog.passTracks_of_ne hsv, hupd,
          Function.update_of_ne hs]
  refine Prog.step_move hR hlin hvi hoff ?_
  have h := hasRight_of_rule dt hrules (i := .vchk2) (ρ := .dspA)
    ?_ rfl rfl rfl hupd' trivial
  · exact h
  · constructor
    · rw [Prog.passTracks_of_ne hne_wk_val, hbgV.1]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_val, hbgV.2.1,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact PR.zero_ne_one

include hrules hR hlin hbot hv hvi in
/-- **The failing exit step**: at the marker with the gates' verdict flag
clear, the verdict checkpoint erases the variable's stage slot and leaves
right into the exit phase, skipping the whole VAL loop. -/
theorem step_var_failExit
    {rest rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {mval : Univ A R P dt.KIx dt.dd → Prop} {f : Q → A}
    (hbgV : dt.VarBg PR.zero PR.one v gtop rest mval)
    (hflagF : f gateFlag ≠ PR.one)
    (hns : newSlot ≠ Slot.val)
    (hoff : ∀ r, r ≠ v → rest' r = rest r)
    (hupd : rest' v = Function.update (rest v) newSlot PR.zero) :
    (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk1) f), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh f), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest' mval) (PR.syElt PR.blank)⟩ := by
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hupd' : Function.update (PR.passTracks Slot.val rest mval v) newSlot
      PR.zero = PR.passTracks Slot.val rest' mval v := by
    funext s
    by_cases hs : s = newSlot
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hns, hupd,
        Function.update_self]
    · rw [Function.update_of_ne hs]
      by_cases hsv : s = Slot.val
      · rw [hsv]
        change (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (regBit mval v) else rest v Slot.val) =
          (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (regBit mval v) else rest' v Slot.val)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hsv, Prog.passTracks_of_ne hsv, hupd,
          Function.update_of_ne hs]
  refine Prog.step_move hR hlin hvi hoff ?_
  have h := hasRight_of_rule dt hrules (i := .vchk1) (ρ := .dspB)
    (f := f) ?_ rfl rfl rfl hupd' trivial
  · exact h
  · refine ⟨⟨?_, ?_⟩, hflagF⟩
    · rw [Prog.passTracks_of_ne hne_wk_val, hbgV.1]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_val, hbgV.2.1,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact PR.zero_ne_one

include hrules hR hlin hbot hv hvi hbg hGates in
/-- **The machinery on a failing address**: through the gates to the
verdict checkpoint, whose clear flag routes straight to the exit — the
stage slot erased, the VAL loop never entered. -/
theorem var_run_fail (hflagF : fG gateFlag ≠ PR.one)
    (hns : newSlot ≠ Slot.val)
    {rest' : (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hoff : ∀ r, r ≠ v → rest' r = rest r)
    (hupd : rest' v = Function.update (rest v) newSlot PR.zero) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .vchk0) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val rest mval) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh fG), Sum.inl v',
        wideTape (PR.trackTape Slot.val rest' mval) (PR.syElt PR.blank)⟩ :=
  (dt.var_run_gates hrules hR hlin hbot hv hvi hbg hGates).trans
    (Relation.ReflTransGen.single
      (dt.step_var_failExit hrules hR hlin hbot hv hvi hbg hflagF hns hoff
        hupd))

end VarRun

end PfpData

end Pfp

end DescriptiveComplexity
