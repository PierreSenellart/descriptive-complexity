/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpRunSpine
import DescriptiveComplexity.Problems.Wide.PfpValEnum

/-!
# A partial fixed point that holds makes the machine accept

The forward half of the EXPSPACE reduction, assembled: from the initial
configuration – the marks over the blank – through the startup, MAIN and the
output evaluation, to the accepting phase. Every leg is a theorem of the run
layer; what this file does is choose the parameters those legs are stated at
and discharge their hypotheses.

The choices, once:

* the **end marker** is the last logical address
  (`DescriptiveComplexity.Pfp.logicalTop`), which is what the startup's
  pattern write leaves in TARGET
  (`DescriptiveComplexity.Pfp.PfpData.tgtTopSt_tgt`);
* the **VAL enumeration** is the increment chain of
  `DescriptiveComplexity.Pfp.PfpData.exists_valEnum`, indexed by `Fin (n + 1)`
  so that its bottom and top are `0` and `Fin.last n`;
* the **stage** the machine stops at is the first stable one
  (`DescriptiveComplexity.StepDef.exists_least_stable`), which exists because
  a definition whose value is read converges.

The two constraints on the layout the assembly needs are the ones
`DescriptiveComplexity.Pfp.wmSetLt_stageTgtD_logicalTop` asks for: one
coordinate of slack beyond the encoding budget (`dd0 < dd`) and one argument
block to name (`dt.KIx` nonempty).
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

/-! ### The end marker the startup plants -/

section Startup

variable {L : Language.{0, 0}} (dt : PfpData L) {A R' P' : Type}

/-- **The pattern the startup writes into TARGET is the last logical
address**: a tag has a block exactly when it is an argument tag. This is what
pins the end marker of the whole run, and with it the interval every
dictionary statement of the layer is read over. -/
theorem tgtTopSt_tgt :
    (dt.tgtTopSt (A := A) (R' := R') (P' := P')).tgt = logicalTop := by
  funext u
  refine propext ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    match hg : u.1 with
    | .arg i => exact ⟨i, hg⟩
    | .ctrl r => exact absurd (hg ▸ hb) (by simp [tagBlk])
    | .sym => exact absurd (hg ▸ hb) (by simp [tagBlk])
    | .phase p => exact absurd (hg ▸ hb) (by simp [tagBlk])
  · rintro ⟨i, hi⟩
    exact ⟨ofLex i, by rw [hi]; rfl⟩

variable {dt}

/-- The startup leaves the marker at the empty address. -/
theorem startupSt_wk :
    (dt.startupSt (A := A) (R' := R') (P' := P')).wk = fun r => r = fun _ => False :=
  rfl

/-- The startup leaves the mirror home. -/
theorem startupSt_mir :
    (dt.startupSt (A := A) (R' := R') (P' := P')).mir = fun _ => False :=
  rfl

/-- The startup leaves the bottom mark at the empty address. -/
theorem startupSt_bot :
    (dt.startupSt (A := A) (R' := R') (P' := P')).bot = fun r => r = fun _ => False :=
  rfl

/-- The startup leaves the end marker at the last logical address. -/
theorem startupSt_ltp :
    (dt.startupSt (A := A) (R' := R') (P' := P')).ltp =
      fun r => r = logicalTop := by
  rw [show (dt.startupSt (A := A) (R' := R') (P' := P')).ltp =
    fun r => r = (dt.tgtTopSt (A := A) (R' := R') (P' := P')).tgt from rfl,
    tgtTopSt_tgt]

/-- The startup leaves every stage track clear. -/
theorem startupSt_old (i : dt.d.B.ι) :
    (dt.startupSt (A := A) (R' := R') (P' := P')).old i = fun _ => False :=
  rfl

end Startup

/-! ### The forward run -/

section Congr

variable {α : Type} {Le Le' : α → α → Prop}

/-- The strict order on addresses depends on the order of the elements only
through its extension – the companion of
`DescriptiveComplexity.Pfp.Table.wmSetLe_congr_rel`, and what carries the
layout's own placement lemmas to the instance's order. -/
theorem wmSetLt_congr_rel (h : ∀ x y, Le x y ↔ Le' x y) (s u : α → Prop) :
    WMSetLt Le s u ↔ WMSetLt Le' s u := by
  refine exists_congr fun x => and_congr_left fun _ => forall_congr' fun y => ?_
  exact imp_congr (and_congr (h y x) (not_congr (h x y))) Iff.rfl

end Congr

section Yes

variable {L : Language.{0, 0}} {dt : PfpData L} {A : Type} {zero one : A}
variable [LinearOrder A] [Fintype dt.SlotIx]
variable [Finite A] [Finite dt.KIx]
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable {hzo : zero ≠ one}
variable [LinearOrder (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [LinearOrder dt.PF]
variable {hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd}
variable [Language.wide.Structure (Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd)]
variable [Finite (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [Finite dt.PF]
variable [LinearOrder (dt.X.Map A)]

/-- **The output leg lands in the accepting phase with the output sentence as
its verdict**, at any state whose tracks hold a stage. The output variable is
nullary, so its argument block is empty and every hypothesis the machinery
asks about the working address's blocks is a function on `Fin 0`; what is left
is the verdict, which is
`DescriptiveComplexity.Pfp.PfpData.accVerdict_out` — an *equivalence*, so this
one leg settles both the accepting and the rejecting case. -/
theorem outLeg_verdict
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)))
    (hord : ∀ x y : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {v₁ : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      dt.PF dt.KIx dt.dd → Prop}
    (hiE : WMIncr WMLe (fun _ => False) v₁)
    {nV : ℕ} (mV : Fin (nV + 1) → Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop)
    (hmV0 : mV 0 = fun _ => False)
    (hIncr : ∀ a a' : Fin (nV + 1), a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (mV (Fin.last nV)) u)
    (hTestF : ∀ a, a < Fin.last nV → ∃ u, ¬dt.InnerFull (mV a) u)
    (hKin : ∀ (a : Fin (nV + 1)) (t : PfpTag
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx)
      (w : Fin dt.dd → A), mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (st : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
    (hwkSt : st.wk = fun r => r = fun _ => False)
    (hmirSt : st.mir = fun _ => False)
    (hbotSt : st.bot = fun r => r = fun _ => False)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (hdict : ∀ (iv : dt.d.B.ι) (s : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd → Prop), WMSetLt WMLe s logicalTop →
      (st.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (a : Fin (nV + 1)) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      WMSetLt WMLe (dt.stageTgtD zero none iv ts (dt.roundSt st (mV a))
        (fun _ => False) (dt.d.B.arity iv)) logicalTop)
    (f₀ : dt.CtlIx → A) :
    ∃ (cfg : Config (WPoint (Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd)))
      (f : dt.CtlIx → A),
      Relation.ReflTransGen (wideData (Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd)).Step
        ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt
            (.evalP (.sub (dt.smEntryOut))) f₀), Sum.inl v₁,
          wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.val
            (dt.back zero one dt.dd0Le st) st.val)
            ((dt.progOf zero one hzo hpl).syElt
              (dt.progOf zero one hzo hpl).blank)⟩ cfg ∧
      cfg.state = Sum.inr ((dt.progOf zero one hzo hpl).stElt .acceptP f) ∧
      ((dt.progOf zero one hzo hpl).accept .acceptP f ↔
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) := by
  classical
  -- the empty address is nobody's register
  have hreg : ¬∃ u : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have hc : (fun _ : Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd => False) gbot := by rw [hu]; exact wmSeg_bot hbot u
    exact hc
  have hv : WMSetLt WMLe (fun _ : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd => False) (wmSeg gbot) :=
    wmSetLt_wmSeg_of_not_bot hbot not_false gbot
  -- the semantic pack: no gate to condition it on, the variable being nullary
  set sem₀ := fun (a : Fin (nV + 1))
      (hp : ∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP zero one none (dt.roundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf (none : dt.VarIx))) =>
    dt.passSem hzo hlin none (dt.roundSt st (mV a)) hp
      (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b with hsem₀
  -- the verdict the machinery computes is the output sentence
  have hacc : (dt.varArgsOf zero one (none : dt.VarIx)).accBit
      (dt.outCtlT (PR := dt.progOf zero one hzo hpl) (v := fun _ => False)
        (aT := Fin.last nV) mV st (Fin.elim0)
        (dt.semCastT none st (fun _ => False) mV sem₀) f₀) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out := by
    rw [dt.outCtlT_eq_outCtl (PR := dt.progOf zero one hzo hpl) (hreg := hreg)
      (st := st) (tOf := Fin.elim0) (sem₀ := sem₀) (f₀ := f₀)]
    exact dt.accVerdict_out (PR := dt.progOf zero one hzo hpl) st mV sem₀
      hlin hord (fun a : Fin (nV + 1) => Fin.zero_le a) hmV0 hIncr hKin
      hTestT σ hdict (fun a iv ts => hbelow a iv ts) hordP
      (fun _ _ _ => rfl) _
  refine ⟨_, _, dt.outLeg_run_verdict
    (fun i ρ => dt.prog_rules_eval zero one hzo _ hpl i ρ) hR hlin hord htop
    hbot hv hiE (fun a : Fin (nV + 1) => Fin.zero_le a)
    (fun a : Fin (nV + 1) => Fin.le_last a) mV hmV0 hIncr hTestT hTestF st
    hwkSt (Fin.elim0) (fun ℓ => ℓ.elim0) (Fin.elim0)
    (fun ℓ => ℓ.elim0) hmirSt hbotSt
    (dt.semCastT none st (fun _ => False) mV sem₀) (fun ℓ => ℓ.elim0)
    (fun ℓ => ℓ.elim0) f₀, rfl, and_iff_right rfl |>.trans hacc⟩

/-- **The whole run, from the initial configuration to the accepting phase**,
with the accepting predicate at the state it stops in *equivalent* to the
value of the partial fixed point. Convergence is all that is asked: it is what
makes MAIN's loop stop, and the verdict the output leg then writes is the
sentence read at the stable stage
(`DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt` making that stage
the one `PFPHolds` speaks of). -/
theorem reaches_outVerdict
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hdd : dt.dd0 < dt.dd) (i₀ : dt.KIx)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hcv : dt.d.PFPConverges (dt.X.Map A)) :
    ∃ (cfg : Config (WPoint (Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd)))
      (f : dt.CtlIx → A),
      Relation.ReflTransGen (wideData (Univ A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
        dt.dd)).Step
        ⟨Sum.inr ((dt.progOf zero one hzo hpl).stElt
            (dt.progOf zero one hzo hpl).startPh
            (dt.progOf zero one hzo hpl).startSt),
          Sum.inl (fun _ => False),
          wideTape ((dt.progOf zero one hzo hpl).trackTape Slot.mir
            (dt.progOf zero one hzo hpl).initBack (fun _ => False))
            ((dt.progOf zero one hzo hpl).syElt
              (dt.progOf zero one hzo hpl).blank)⟩ cfg ∧
      cfg.state = Sum.inr ((dt.progOf zero one hzo hpl).stElt .acceptP f) ∧
      ((dt.progOf zero one hzo hpl).accept .acceptP f ↔
        dt.d.PFPHolds (dt.X.Map A)) := by
  classical
  have hlin : IsLinOrd (WMLe (A := Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)) := (dt.progOf zero one hzo hpl).table.isLinOrd_wmLe hR
  have hord := hR.le
  -- the two extremes of the universe
  obtain ⟨gtop, -, htop⟩ := exists_greatest (Le := WMLe (A := Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)) hlin (P := fun _ => True) ⟨(PfpTag.arg i₀, fun _ => zero), trivial⟩
  obtain ⟨gbot, -, hbot⟩ := exists_least (Le := WMLe (A := Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)) hlin (P := fun _ => True) ⟨(PfpTag.arg i₀, fun _ => zero), trivial⟩
  simp only [forall_const] at htop hbot
  -- the logical interval
  have hnotbot : ¬logicalTop gbot := by
    rintro ⟨i, hi⟩
    have h := tagBlk_eq_none_of_least (ko := dt.ko) (ki := dt.ki)
      (fun y => (hord gbot y).mp (hbot y))
    rw [hi] at h
    exact absurd h (by simp [tagBlk])
  have hlt : WMSetLt WMLe (logicalTop (R := dt.RIx zero one hzo
      (fun w => dt.varArgsOf zero one w)) (P := dt.PF) (K := dt.KIx)
      (V := Fin dt.dd → A)) (wmSeg gbot) :=
    wmSetLt_wmSeg_of_not_bot hbot hnotbot gbot
  have hneT : ∃ x, logicalTop (R := dt.RIx zero one hzo
      (fun w => dt.varArgsOf zero one w)) (P := dt.PF) (K := dt.KIx)
      (V := Fin dt.dd → A) x := ⟨(PfpTag.arg i₀, fun _ => zero), i₀, rfl⟩
  obtain ⟨v₁, hiE⟩ := exists_wmIncr hlin (s := fun _ : Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd => False) ⟨gbot, not_false⟩
  -- the layout's own placement lemmas, at the instance's order
  have hordL : ∀ x y : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, WMLe x y ↔ lexRel (· ≤ · : PfpTag (dt.RIx zero one hzo
        (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx →
        PfpTag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
          dt.KIx → Prop) (tupLeLex (A := A) (d := dt.dd)) x y :=
    fun x y => (hord x y).trans (Wide.tagTupleLe_iff_lexRel x y)
  -- the VAL enumeration
  obtain ⟨nV, mV, hmV0, hIncr, hTestT, hTestF, hKin⟩ :=
    exists_valEnum (dt := dt) (A := A)
      (R := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P := dt.PF) hlin hord
  -- the first stable stage
  obtain ⟨N, hstable, hleast⟩ := dt.d.exists_least_stable (dt.X.Map A) hcv
  -- every address the dictionary is read at lies in the logical interval
  have hbelow : ∀ (j : Fin dt.nv) (a : Fin (nV + 1)) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeSt dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) logicalTop :=
    fun _ _ _ _ _ _ => (wmSetLt_congr_rel hordL _ _).mpr
      (dt.wmSetLt_stageTgtD_logicalTop hzo Wide.isLinOrd_tupLeLex hdd i₀ _)
  have hS : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      WMSetLt WMLe (tupAddr dt.ly zero one
        (R := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        (P := dt.PF) (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) logicalTop :=
    fun iv x => (wmSetLt_congr_rel hordL _ _).mpr
      (wmSetLt_tupAddr_logicalTop' hzo Wide.isLinOrd_tupLeLex i₀
        (dt.arOf_le_ko (some iv)) x)
  -- the initial tape is stage zero
  have hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop), WMSetLt WMLe s logicalTop →
      ((dt.startupSt (A := A)
          (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
          (P' := dt.PF)).old iv s ↔
        trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
          (dt.d.partStage (dt.X.Map A) 0) s) :=
    fun iv s _ => old_trackOf_zero_of_blank (fun _ _ hc => hc) iv s
  -- the two semantic hypotheses of MAIN: the first stable stage
  have hconv := dt.stageEnd_conv_of_eq (hpl := hpl) (hlin := hlin) (hord := hord)
    (hbot := hbot) (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a) (mV := mV)
    (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
    (hordP := hordP) (hKin := hKin) (hlt := hlt) (hold₀ := hold₀)
    (hbelow := hbelow) (hN := hstable)
  have hnotconv := fun n (hn : n < N) => dt.stageEnd_not_conv_of_ne
    (hpl := hpl) (hlin := hlin) (hord := hord) (hbot := hbot)
    (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a) (mV := mV)
    (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
    (hordP := hordP) (hKin := hKin) (hlt := hlt) (hold₀ := hold₀)
    (hbelow := hbelow) (hS := hS) (hN := hleast n hn)
  -- the semantic pack of the branched sweep, and the stage families
  set semG : ∀ (w : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop) (j : Fin dt.nv)
    (st : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF),
    dt.gatedAt (PR := dt.progOf zero one hzo hpl) j st → _ :=
    fun w j st hg => dt.gatedSem (PR := dt.progOf zero one hzo hpl) hzo hlin
      mV (v := w) j st hg with hsemG
  set stX : TapeSt dt A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF :=
    { dt.atSt (dt.offSt (dt.stageEnd hpl hlin (aT := Fin.last nV) mV semG
        logicalTop
        (dt.stageSt hpl hlin (aT := Fin.last nV) mV semG logicalTop
          dt.startupSt (fun _ => zero) N)
        (dt.stageFs hpl hlin (aT := Fin.last nV) mV semG logicalTop
          dt.startupSt (fun _ => zero) N))) (fun _ => False) with
      mir := fun _ => False } with hstX
  -- MAIN, from the first stage's entry to the out machinery's
  have hmain := dt.reaches_mainB (hpl := hpl) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot)
    (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a)
    (htopV := fun a : Fin (nV + 1) => Fin.le_last a) (mV := mV)
    (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT) (hTestF := hTestF)
    (semAt := semG)
    (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
    (hlt := hlt) (hneT := hneT) (hiE := hiE) (hwk₀ := startupSt_wk)
    (hmir₀ := startupSt_mir) (hbot₀ := startupSt_bot)
    (hltp₀ := startupSt_ltp) (hnotconv := hnotconv) (hconv := hconv)
  -- the startup, into MAIN's first stage
  have hentry := dt.reaches_evalEntry (hpl := hpl) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot)
  -- the markers MAIN leaves behind
  have hfields := fun n => dt.stageSt_fields (hpl := hpl) (hlin := hlin)
    (aT := Fin.last nV) (mV := mV) (semAt := semG) (st₀ := dt.startupSt)
    (f₀ := fun _ => zero) (ltpAddr := logicalTop) (hwk₀ := startupSt_wk)
    (hmir₀ := startupSt_mir) (hbot₀ := startupSt_bot)
    (hltp₀ := startupSt_ltp) (n := n)
  have hbotX : stX.bot = fun r => r = fun _ => False :=
    Eq.trans (dt.stageEnd_ride hlin mV semG logicalTop (fun st => st.bot)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ _ => (dt.legStB_fields
        (PR := dt.progOf zero one hzo hpl) (aT := Fin.last nV) mV _ _ _ _).2.2.1)
      _ _) (hfields N).2.2.1
  -- the tracks hold the stable stage, and the output sentence holds of it
  have hdictX : ∀ (iv : dt.d.B.ι) (s : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop), WMSetLt WMLe s logicalTop →
      (stX.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
        (dt.d.partStage (dt.X.Map A) N) s) :=
    fun iv s hs => dt.stageEnd_old_trackOf (hpl := hpl) (hlin := hlin)
      (hord := hord) (hbot := hbot)
      (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a) (mV := mV)
      (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
      (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
      (hordP := hordP) (hKin := hKin) (hlt := hlt) (hold₀ := hold₀)
      (hbelow := hbelow) (n := N) (iv := iv) (hs := hs)
  have hbelowOut : ∀ (a : Fin (nV + 1)) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      WMSetLt WMLe (dt.stageTgtD zero none iv ts (dt.roundSt stX (mV a))
        (fun _ => False) (dt.d.B.arity iv)) logicalTop :=
    fun _ _ _ => (wmSetLt_congr_rel hordL _ _).mpr
      (dt.wmSetLt_stageTgtD_logicalTop hzo Wide.isLinOrd_tupLeLex hdd i₀ _)
  have hfixN : Function.IsFixedPt dt.d.next (dt.d.partStage (dt.X.Map A) N) :=
    (dt.d.partStage_succ (A := dt.X.Map A) N).symm.trans hstable.symm
  -- the value of the fixed point is the sentence at the stable stage
  have hpfpN : @Sentence.Realize _ (dt.X.Map A)
      (dt.d.B.structure₁ (dt.d.partStage (dt.X.Map A) N)) dt.d.out ↔
      dt.d.PFPHolds (dt.X.Map A) :=
    ⟨fun h => ⟨N, hfixN, h⟩, fun ⟨_, hfix, hout⟩ =>
      dt.d.partStage_eq_of_isFixedPt hfix hfixN ▸ hout⟩
  -- the output leg, and the whole run
  obtain ⟨cfg, f, hrun, hstate, hiff⟩ := dt.outLeg_verdict (hR := hR)
    (hlin := hlin) (hord := hord) (htop := htop) (hbot := hbot) (hiE := hiE)
    (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (hTestF := hTestF) (hKin := hKin) (hordP := hordP) (st := stX)
    (hwkSt := rfl) (hmirSt := rfl) (hbotSt := hbotX)
    (σ := dt.d.partStage (dt.X.Map A) N) (hdict := hdictX)
    (hbelow := hbelowOut)
    (f₀ := dt.stageFs hpl hlin (aT := Fin.last nV) mV semG logicalTop
      dt.startupSt (fun _ => zero) (N + 1))
  refine ⟨cfg, f, ?_, hstate, hiff.trans hpfpN⟩
  rw [dt.initBack_eq_back zero one hzo (fun w => dt.varArgsOf zero one w) hpl
    hlin]
  exact (hentry.trans hmain).trans hrun

/-- **A partial fixed point that holds makes the emitted instance a
yes-instance**: the two promises of `DescriptiveComplexity.DWideAcceptSpace` –
well-formedness for free, determinism from the program's separation argument –
together with the run of
`DescriptiveComplexity.Pfp.PfpData.reaches_accept`. -/
theorem dwideAcceptSpace_of_pfpHolds
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hdd : dt.dd0 < dt.dd) (i₀ : dt.KIx)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hpfp : dt.d.PFPHolds (dt.X.Map A)) :
    DWideAcceptSpace (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd) := by
  obtain ⟨cfg, f, hrun, hstate, hiff⟩ :=
    dt.reaches_outVerdict hR hdd i₀ hordP hpfp.converges
  exact ⟨(dt.progOf zero one hzo hpl).table.wellFormed hR,
    (dt.progOf zero one hzo hpl).table.deterministic hR
      (dt.prog_sep zero one hzo (fun w => dt.varArgsOf zero one w) hpl),
    Prog.acceptsSpace_prog hR
      ((dt.progOf zero one hzo hpl).table.isLinOrd_wmLe hR)
      (fun x => prog_mark_mir hpl x) (prog_blank_mir hpl) hrun hstate
      (hiff.mpr hpfp)⟩

end Yes

end PfpData

end Pfp

end DescriptiveComplexity
