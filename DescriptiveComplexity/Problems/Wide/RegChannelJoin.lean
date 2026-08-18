/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelEval
import DescriptiveComplexity.Problems.Wide.RegChannelPad

/-!
# The two legs, joined at any program with the clocked rules

`DescriptiveComplexity.Draw.Data.wideRegAccept_of_legs` packages an opening and
an evaluation as a yes-instance of `DescriptiveComplexity.WideRegAccept`, and
`DescriptiveComplexity.Draw.Data.reachesIn_openingReg` runs the opening – both
at an arbitrary program. This file joins them, at an arbitrary program too: the
opening at the file the channel hands over, the evaluation at the same file, the
guess writing an assignment's tracks inside the region it sweeps, and the clock
met by the region's size, the evaluation's width and its rounds.

What the join reads of the program is only what a hypothesis can carry: its
rules at named sites, its channel's marks, its constants and its accepting
predicate. So the program a reduction emits and the *padded* one that buys the
clock its room (`RegChannelPad.lean`) are both instances of one statement, and
nothing here has to be proved twice.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section JoinGen

variable {L : Language.{0, 0}} {dt : Data L} {A R' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Nonempty A] [Finite A] [Finite dt.KIx] [Nonempty dt.KIx]
variable [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A R'
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

variable (PR) in
/-- **The semantic packs a run of this evaluation is threaded by, pinned at the
program**: the packs are built once and for all (`regGatedSem`), and the only
thing this adds is *which* program the gates they answer for belong to – which a
term whose type mentions the program cannot leave to inference. -/
noncomputable def regGatedSemP
    (h : IsLinOrd (WMLe (A := Univ A R'
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {ιV : Type} (mV : ιV → dt.NexRegIx A R' (Option dt.KIx) → Prop) :
 ∀ (w : Univ A R'
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
        (j : Fin dt.nv)
        (st : TapeSt dt A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
          (dt.NexRegIx A R' (Option dt.KIx))),
      dt.ixGatedAt (PR := PR)
          (elt := dt.regElt A R' (Option dt.KIx)) (F := dt.regLaid h hord) j st →
      ∀ (p : IxScratch dt A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
          (dt.NexRegIx A R' (Option dt.KIx))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := dt.regElt A R' (Option dt.KIx))
          (dt.regLaid h hord) PR.zero PR.one (dt.varAt j)
          (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := dt.regElt A R' (Option dt.KIx))
            (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
          (dt.regElt A R' (Option dt.KIx)) (dt.kindOf (dt.varAt j) b) :=
  dt.regGatedSem h hord PR.zero_ne_one mV

/-- **A program with the clocked rules accepts, at the file the channel gives
it**: the opening and the evaluation at that one file, joined. Nothing of the
program is read but its rules at named sites, its channel and its constants, so
the same statement serves the program a reduction emits and the padded one that
buys the clock its room. -/
theorem wideRegAccept_regLaid_of_rules
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {v' v₁ x y y' s₀ top : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
    (hvi₁ : WMIncr WMLe (fun _ => False) v₁) (hwalk : WMSetLe WMLe v₁ x)
    (hxy : WMIncr WMLe x y) (hyy' : WMIncr WMLe y y')
    (hyv : WMSetLe WMLe (fun _ => False) y)
    (hs₀ : WMIncr WMLe (fun _ => False) s₀)
    (hvi' : WMIncr WMLe (fun _ => False) v')
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (htop : WMSetLe WMLe s₀ top)
    (htopne : ∃ z, top z)
    (hexB : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid h hord).cell Slot.mir
      (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one
        dt.dd0Le (dt.nexEntrySt (fun _ => False))) (fun _ => False)
      (fun _ => False)))
    (hexG : dt.exitG PR.one (PR.passTracksAt
      (dt.regLaid h hord).cell Slot.mir
      (dt.ixBack (dt.regLaid h hord).toLayout PR.zero PR.one
        dt.dd0Le { dt.nexEntrySt (fun _ => False) with
          old := dt.guessTracks PR.zero PR.one σ s₀ top })
      (fun _ => False) (fun _ => False)))
    {e₀ : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (he₀ : ∀ y, WMLe e₀ y)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) PR.zero c) : Univ A
        (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (hargall : ∀ z : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      (∃ i : dt.KIx, z.1 = Tag.arg i) → WMHasInp z)
    (hupinp : ∀ z w : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe z w → WMHasInp z → WMHasInp w)
    {botE : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (hbotm : WMHasInp botE)
    (hleast : ∀ z : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd, WMHasInp z → WMLe botE z)
    (hbotarg : ∀ i : dt.KIx, botE.1 ≠ Tag.arg i)
    (gtop gbot : dt.NexRegIx A (R') (Option dt.KIx))
    (htopF : ∀ u, (dt.regLaid h hord).le u gtop)
    (hbotF : ∀ u, (dt.regLaid h hord).le gbot u)
    {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
    (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
    (mV : ιV → dt.NexRegIx A (R') (Option dt.KIx) → Prop)
    (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr (dt.regLaid h hord).le (mV a) (mV a'))
    (hTestT : ∀ u, dt.InnerFull (dt.regLaid h hord).blk (mV aT) u)
    (hTestF : ∀ a, a < aT →
      ∃ u, ¬dt.InnerFull (dt.regLaid h hord).blk (mV a) u)
    (stL : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
        (dt.NexRegIx A (R') (Option dt.KIx)))
    (fsL : dt.CtlIx → A)
    (hstL : stL = dt.ixSpineStOfB (elt := dt.regElt A
      (R') (Option dt.KIx))
      (v := (fun _ => False)) (aT := aT) (dt.regLaid h hord)
        (dt.regElt_injective A (R') (Option dt.KIx))
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV { dt.nexEntrySt (fun _ => False) with
        old := dt.guessTracks PR.zero PR.one σ s₀ top }
      ((fun _ => PR.zero))
      (dt.regGatedSemP PR h hord mV)
      (Fin.last dt.nv))
    (hfsL : fsL = dt.ixSpineFsOfB (elt := dt.regElt A
      (R') (Option dt.KIx))
      (v := (fun _ => False)) (aT := aT) (dt.regLaid h hord)
        (dt.regElt_injective A (R') (Option dt.KIx))
      (dt.hasName_regLaid PR.zero harg)
      (fun b c => dt.elt_reg_regLaid PR.zero harg b c)
      mV { dt.nexEntrySt (fun _ => False) with
        old := dt.guessTracks PR.zero PR.one σ s₀ top }
      ((fun _ => PR.zero))
      (dt.regGatedSemP PR h hord mV)
      (Fin.last dt.nv))
    (hmirL : stL.mir = ixMark
      (dt.regElt A (R') (Option dt.KIx)) (fun _ => False))
    (hbotL : stL.bot = fun r => r = (fun _ => False))
    (hsavL : stL.sav = ixMark
      (dt.regElt A (R') (Option dt.KIx)) (fun _ => False))
    (htgtL : stL.tgt = ixMark
      (dt.regElt A (R') (Option dt.KIx)) (fun _ => False))
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
    {Below : (Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R')
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (stL.old iv (tupAddr dt.ly PR.zero PR.one (R := R')
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr (dt.regElt A (R') (Option dt.KIx))
        (dt.ixStageTgt (dt.regLaid h hord)
          (dt.hasName_regLaid PR.zero harg) none ts
          { dt.ixRoundSt stL (mV a) with
            sav := ixMark
              (dt.regElt A (R')
                (Option dt.KIx)) (fun _ => False) }
          (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out)    {a b k j m : ℕ}
    (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (ha : dt.ixEvalWidth A (dt.nexRegW A (R') (Option dt.KIx))
      (dt.nexRegWP A (R') (Option dt.KIx))
      (dt.nexRegWR A (R') (Option dt.KIx))
      (dt.nexRegWK A (R') (Option dt.KIx)) ≤ a)
    (haa : a ≤ 2 ^ (k * m)) (hb : Nat.card ιV + 1 ≤ b) (hbb : b ≤ 2 ^ (k * m))
    (hopenle : (wideRank x - wideRank v₁) +
        (wideRank y - wideRank (fun _ : Univ A (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => False)) +
        ((wideRank top - wideRank s₀) +
          (wideRank top - wideRank (fun _ : Univ A (R')
            (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => False))) + 7 + 1 ≤
      2 ^ ((k + 1) * m)) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)  := by
  obtain ⟨fq, cT, hrun, hstate, hacc⟩ :=
    dt.nexIxEvalOut_regLaid_realize_reachesIn h
      (rEmb := fun i ρ => hE.site (.eval i) ρ)
      (fun i ρ => hE.rules_site (.eval i) ρ)
      hR PR.zero_ne_one hord he₀ harg hargall
      hupinp hbotm hleast hbotarg gtop gbot htopF hbotF
      (dt.work_regLaid hbotm hleast hbotarg (fun _ hz => hz.elim) gbot)
      (fun z hz => hz.elim) hvi' hbotV htopV mV hmV0 hIncr hTestT hTestF _ _ rfl
      rfl rfl stL fsL hstL hfsL
      (rEmbO := fun i ρ => hE.site (.eval (.sub (Sum.inr i))) ρ)
      (hrulesOut := fun i ρ => hE.rules_site (.eval (.sub (Sum.inr i))) ρ)
      (hmirL := hmirL) (hbotL := hbotL) (hsavL := hsavL) (htgtL := htgtL)
      (hUse := hUse) (hmono := hmono) (hup := hup) (hKin := hKin) (hTop := hTop)
      σ (hdict := hdict) (hbelow := hbelow) (hordP := hordP) (hout := hout)
  refine dt.wideRegAccept_of_legs hR h (fun x => by rw [hE.mark x]; rfl)
    (hE.blank Slot.mir)
    (F := dt.regLaid h hord)
    (st := { dt.nexEntrySt (fun _ => False) with
      old := dt.guessTracks PR.zero PR.one σ s₀ top }) rfl
    (dt.reachesIn_openingReg hpl hE.rules_site hE.rules_homeBuild
      hE.rules_homeGuess hE.mark hE.marked hE.blank hE.startPh hE.startSt hR h hord
      (fun z hz => fun hcz => by
        obtain ⟨w, hw⟩ :=
          wmRegSeg_nonempty h
            ((Table.wmHasInp_iff_marked hR z).mpr ((hE.marked z).mpr hz))
        exact (congrFun hcz w ▸ hw : False))
      hvi₁ hwalk hxy hyy' hyv hs₀ htop htopne hvi' hexB _
      (fun i r hr => not_guessTracks_out h hr i) hexG)
    hrun hk hkj hm hcard ?_ haa hbb hopenle hstate ((hE.accept_iff _ _).mpr ⟨rfl, hacc⟩)
  exact le_trans (dt.ixEvalCost_le_mul _ _ _ _ _) (Nat.mul_le_mul ha hb)

end JoinGen

end Data

end Draw

end DescriptiveComplexity
