/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelEntry
import DescriptiveComplexity.Problems.Wide.RegChannelEval
import DescriptiveComplexity.Problems.Wide.RegChannelJoin

/-!
# The evaluation with its verdict read, and the two exits

The forward run of a clocked program at the file the register channel hands it
assumes the sentence and runs into the accepting phase. A *backward* reading
cannot assume it – the verdict is what it is trying to determine – so this file
carries the evaluation in the other form: the run exists whatever the stage says,
and the accepting bit it leaves *is* the sentence's value
(`nexProgHanded_reachesIn_eval_verdict`).

The two exits of the walks home come with it (`exitG_at_marker`): they are facts
about where the marker is, and nothing about what the machine has written, so
both directions of the correctness supply them the same way.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section OpeningHandedAt

variable {L : Language.{0, 0}} {dt : Data L} {A : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Nonempty A] [Finite A] [Finite dt.KIx] [Nonempty dt.KIx]
variable [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd} {bot : Option dt.KIx}
variable {zero one : A}

/-! ### The two exits, at the marker -/

section Exits

variable {L' : Language.{0, 0}} {dt' : Data L'} {A' R'' P'' I' : Type}
variable [Fintype dt'.SlotIx] [LinearOrder A'] [LinearOrder R''] [LinearOrder P'']
variable [Language.wide.Structure (Univ A' R'' P'' dt'.KIx dt'.dd)]
variable [Finite A'] [Finite R''] [Finite P''] [Finite dt'.KIx]
variable {PR' : Prog A' R'' P'' dt'.CtlIx dt'.SlotIx dt'.KIx dt'.dd}

omit [LinearOrder A'] [LinearOrder R''] [LinearOrder P''] [Finite A'] [Finite R'']
  [Finite P''] [Finite dt'.KIx] [Language.wide.Structure (Univ A' R'' P'' dt'.KIx dt'.dd)] in
/-- **The exit condition holds at the marker**: the head is on the address the
`wk` track marks, and that address is nobody's register. Both are what the entry
state says, so the two exits an opening asks for are facts about *where the
marker is*, not about what the machine has written. -/
theorem exitG_at_marker {lay : Layout dt' A' R'' P'' I'}
    {st : TapeSt dt' A' R'' P'' I'}
    {v : Univ A' R'' P'' dt'.KIx dt'.dd → Prop} (hwk : st.wk v)
    (hnc : ∀ u : I', v ≠ lay.cell u) :
    dt'.exitG PR'.one (PR'.passTracksAt lay.cell Slot.mir
      (dt'.ixBack lay PR'.zero PR'.one dt'.dd0Le st) (fun _ => False) v) := by
  classical
  constructor
  · change (if (Slot.wk : dt'.SlotIx) = Slot.mir then _ else
      dt'.ixBack lay PR'.zero PR'.one dt'.dd0Le st v Slot.wk) = PR'.one
    rw [if_neg (by rintro hc; exact nomatch hc)]
    exact bitVal_pos hwk
  · change (if (Slot.reg : dt'.SlotIx) = Slot.mir then _ else
      dt'.ixBack lay PR'.zero PR'.one dt'.dd0Le st v Slot.reg) ≠ PR'.one
    rw [if_neg (by rintro hc; exact nomatch hc)]
    change bitVal PR'.zero PR'.one (∃ u : I', v = lay.cell u) ≠ PR'.one
    rw [bitVal_neg (by rintro ⟨u, hu⟩; exact hnc u hu)]
    exact PR'.zero_ne_one

end Exits

/-! ### The evaluation, at the handed program -/

omit [Nonempty dt.KIx] in
/-- **The clocked evaluation, at the program, with the verdict read rather than
assumed**: the clocked evaluation without the sentence as a hypothesis,
the accepting bit coming back as the sentence's own value. This is the form a
*backward* reading needs – the run exists whatever the verdict, and the bit says
which. -/
theorem nexProgHanded_reachesIn_eval_verdict
    (hE : NexEmitted PR bot)
    (h : IsLinOrd (WMLe (A := Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hR : PR.table.Reads)
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {e₀ : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ x : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, x.1 = Tag.arg i) → WMHasInp x)
    (hupinp : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y → WMHasInp x → WMHasInp y)
    {botE : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (hbotm : WMHasInp botE)
    (hleast : ∀ y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMHasInp y → WMLe botE y)
    (hbotarg : ∀ i : dt.KIx, botE.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A (R') (Option dt.KIx))
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {v v' : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hv : WMSetLt WMLe v ((dt.regLaid h hord).cell gbot))
    (hvlog : ∀ x, v x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (hvi : WMIncr WMLe v v')
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A (R') (Option dt.KIx) → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (st₀ : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (dt.NexRegIx A (R') (Option dt.KIx)))
    (f₀ : dt.CtlIx → A)
    (hwk₀ : st₀.wk = fun r => r = v)
    (hmir₀ : st₀.mir = ixMark (dt.regElt A (R') (Option dt.KIx)) v)
    (hbot₀ : st₀.bot = fun r => r = (fun _ => False))
    (stL : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (dt.NexRegIx A (R') (Option dt.KIx)))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt :=
      dt.regElt A (R') (Option dt.KIx))
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A
        (R') (Option dt.KIx))
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSemP PR h hord mV) (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt :=
      dt.regElt A (R') (Option dt.KIx))
      (v := v) (aT := aT) (dt.regLaid h hord) (dt.regElt_injective A
        (R') (Option dt.KIx))
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV st₀ f₀ (dt.regGatedSemP PR h hord mV) (Fin.last dt.nv))
    (hmirL : stL.mir = ixMark (dt.regElt A (R') (Option dt.KIx)) v)
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark (dt.regElt A (R') (Option dt.KIx)) v)
    (htgtL : stL.tgt = ixMark (dt.regElt A (R') (Option dt.KIx)) v)
    -- What the verdict is read against: the stage the guess wrote, the
    -- enumeration's own facts, and the order on the expanded universe.
    {Use : dt.NexRegIx A (R') (Option dt.KIx) → Prop}
    (hUse : ∀ (a : ιV) (u : dt.NexRegIx A
      (R') (Option dt.KIx)), mV a u → Use u)
    (hmono : ∀ u u', WMLt (dt.regLaid h hord).le u u' ↔
      WMLt WMLe (dt.regElt A (R') (Option dt.KIx) u)
        (dt.regElt A (R') (Option dt.KIx) u'))
    (hup : ∀ (u : dt.NexRegIx A (R') (Option dt.KIx))
        (x : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      Use u → WMLt WMLe (dt.regElt A (R') (Option dt.KIx) u) x →
      ∃ u', Use u' ∧ dt.regElt A (R') (Option dt.KIx) u' = x)
    (hKin : ∀ (a : ιV) (t : Tag (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx)
        (w : Fin dt.dd → A),
      ixAddr (dt.regElt A (R') (Option dt.KIx)) (mV a) (t, w) →
        ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1)
      (ixAddr (dt.regElt A (R') (Option dt.KIx)) (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R')
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st₀.old iv (tupAddr dt.ly PR.zero PR.one (R := R')
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr (dt.regElt A (R') (Option dt.KIx))
        (dt.ixStageTgt (dt.regLaid h hord) (dt.hasName_regLaid PR.zero harg)
          none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark (dt.regElt A (R') (Option dt.KIx)) v }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    :
    ∃ (fq : dt.CtlIx → A) (cT : Config (WPoint (Univ A
      (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))),
    (wideData (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).ReachesIn
      (1 + ((dt.ixLegCost A (dt.nexRegW A (R') (Option dt.KIx))
        (dt.nexRegWP A (R') (Option dt.KIx))
        (dt.nexRegWR A (R') (Option dt.KIx))
        (dt.nexRegWK A (R') (Option dt.KIx))
        (Nat.card ιV) + 2) * dt.nv) + 1 +
        dt.ixOutLegCost A (dt.nexRegW A (R') (Option dt.KIx))
          (dt.nexRegWP A (R') (Option dt.KIx))
          (dt.nexRegWR A (R') (Option dt.KIx))
          (dt.nexRegWK A (R') (Option dt.KIx))
          (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (NexPh.evalP (.chk 0)) f₀),
        Sum.inl v',
        wideTape (PR.trackTapeAt
          (dt.regLaid h hord).cell Slot.val
          (dt.ixBack (dt.regLaid h hord).toLayout
            PR.zero PR.one
            dt.dd0Le st₀)
          st₀.val) (PR.syElt
            PR.blank)⟩
      cT ∧ cT.state = Sum.inr
        (PR.stElt NexPh.acceptP fq) ∧
      ((dt.varArgsOf PR.zero
        PR.one none).accBit fq ↔
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) := by
  -- no leg of the spine writes the stage tracks, so the dictionary the
  -- evaluation reads is the entry state's own
  have holdL : stL.old = st₀.old := by
    rw [hstL]
    exact dt.ixSpineStOfB_old
      (elt := dt.regElt A (R') (Option dt.KIx))
      (v := v) (aT := aT) (dt.regLaid h hord)
      (dt.regElt_injective A (R') (Option dt.KIx))
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c) mV st₀ f₀
      (dt.regGatedSemP PR h hord mV) (Fin.last dt.nv)
  exact dt.nexIxEvalOut_regLaid_verdict_reachesIn h
    (rEmb := fun i ρ => hE.site (.eval i) ρ)
    (fun i ρ => hE.rules_site (.eval i) ρ) hR
    PR.zero_ne_one hord he₀ harg hargall
    hupinp hbotm hleast hbotarg gtop gbot htopF hbotF hv hvlog hvi hbotV htopV mV
    hmV0 hIncr hTestT hTestF st₀ f₀ hwk₀ hmir₀ hbot₀
    stL fsL hstL hfsL (rEmbO := fun i ρ => hE.site (.eval (.sub (Sum.inr i))) ρ)
    (hrulesOut := fun i ρ => hE.rules_site (.eval (.sub (Sum.inr i))) ρ)
    (hmirL := hmirL) (hbotL := hbotL)
    (hsavL := hsavL) (htgtL := htgtL) (hUse := hUse) (hmono := hmono)
    (hup := hup) (hKin := hKin) (hTop := hTop) σ
    (hdict := fun iv x hb =>
      (iff_of_eq (congrFun (congrFun holdL iv) _)).trans (hdict iv x hb))
    (hbelow := hbelow) (hordP := hordP)

end OpeningHandedAt

end Data

end Draw

end DescriptiveComplexity
