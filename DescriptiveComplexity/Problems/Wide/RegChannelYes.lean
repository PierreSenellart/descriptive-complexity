/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelAccept
import DescriptiveComplexity.Problems.Wide.RegChannelWalk
import DescriptiveComplexity.Problems.Wide.SpineSav
import DescriptiveComplexity.Problems.Wide.PfpYes

/-!
# The handed program accepts, from the sentence alone

`DescriptiveComplexity.Pfp.PfpData.wideRegAccept_regLaid_of_rules` joins the
two legs of the run at the file the register channel hands over, and asks the
caller for some thirty facts. Most of them are not about the instance at all:
they follow from the *marking* (`hasInp_up`, `exists_regBotElt`), from the
*order* (`exists_openingWalkReg`, `exists_regValEnum`), from where the *marker*
is (`exitG_at_marker`), from what the guess wrote (`guessTracks_hdict_of_old`) and
from what a leg leaves behind (`parked_ixSpineStOfB`).

This file supplies all of those, so that what is left of the run is what the
*reduction* decides: the assignment its guess writes, the sentence being true,
the order on the expanded universe, and the three numbers of the clock.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

section Yes

variable {L : Language.{0, 0}} {dt : PfpData L} {A : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [Nonempty A] [Finite A] [Finite dt.KIx] [Nonempty dt.KIx]
variable [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
variable [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
variable {R' : Type} [LinearOrder R'] [Finite R']
variable [Language.wide.Structure (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite (Univ A (R')
  (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
  dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Fintype dt.SlotIx] [LinearOrder A] [Finite A] [Finite dt.KIx]
  [L.IsRelational] [L.Structure A] [LinearOrder (dt.X.Map A)]
  [LinearOrder (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [LinearOrder (R')]
  [Finite (R')]
  [Language.wide.Structure (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **An argument element**: the drawn universe has one, the argument blocks
and the alphabet being nonempty. It is what puts an element above the one the
channel marks below them, which is what the opening's walk needs. -/
theorem exists_argElt :
    ∃ x : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      ∃ i : dt.KIx, x.1 = PfpTag.arg i :=
  ⟨(PfpTag.arg (Classical.arbitrary dt.KIx), fun _ => Classical.arbitrary A),
    Classical.arbitrary dt.KIx, rfl⟩

omit [Finite dt.KIx] [LinearOrder (dt.X.Map A)] [Finite A] [L.IsRelational]
  [L.Structure A]
  [Finite (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))]
  [Finite (R')]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **An element above the one the channel marks below the argument tags**: any
argument element is one, the argument tags being the greatest. This is what the
opening's walk asks of the instance, and the drawing always has it. -/
theorem exists_above_botElt (hR : PR.table.Reads)
    {botE : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (hbotarg : ∀ i : dt.KIx, botE.1 ≠ PfpTag.arg i) :
    ∃ z : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd, WMLt WMLe botE z := by
  obtain ⟨x, i, hi⟩ := exists_argElt (dt := dt) (A := A)
  have hlt : botE.1 < x.1 := hi ▸ lt_arg botE.1 i hbotarg
  refine ⟨x, (hR.le _ _).mpr (Or.inl hlt), fun hc => ?_⟩
  rcases (hR.le _ _).mp hc with hb | ⟨hb, -⟩
  · exact absurd hb (asymm hlt)
  · exact absurd hb (ne_of_gt hlt)


/-! ### The stage addresses lie in the logical interval -/

omit [LinearOrder (dt.X.Map A)] [L.IsRelational] [L.Structure A]
  [Finite (Univ A (R')
    (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)] in
/-- **Every address a stage atom reads is below the logical top**, at the handed
file: `wmSetLt_ixStageTgt_logicalTop`, read against the machine's own order.
This is the `hbelow` an evaluation asks for, and it asks nothing of the
instance. -/
theorem belowTop_regLaid (hlin : IsLinOrd (WMLe (A := Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    (hdd : dt.dd0 < dt.dd)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((PfpTag.arg (toLex b), padTup (dt := dt) PR.zero c) :
        Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    {vi : dt.VarIx} {iv : dt.d.B.ι}
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    (st : TapeSt dt A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))
      (dt.NexRegIx A (R') (Option dt.KIx))) (n : ℕ) :
    WMSetLt WMLe
      (ixAddr (dt.regElt A (R') (Option dt.KIx))
        (dt.ixStageTgt (dt.regLaid hlin hord)
          (dt.hasName_regLaid (h :=
            hlin) (hord := hord) PR.zero harg)
          vi ts st n))
      logicalTop := by
  have hordL : ∀ x y : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      WMLe x y ↔ lexRel (· ≤ · : PfpTag (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx →
        PfpTag (R')
          (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx → Prop)
        (tupLeLex (A := A) (d := dt.dd)) x y :=
    fun x y => (hord x y).trans (Wide.tagTupleLe_iff_lexRel x y)
  refine (wmSetLt_congr_rel hordL _ _).mpr ?_
  exact dt.wmSetLt_ixStageTgt_logicalTop
    (F := dt.regLaid (hlin) hord)
    (hhas := dt.hasName_regLaid (h :=
      hlin) (hord := hord) PR.zero harg)
    (elt := dt.regElt A (R') (Option dt.KIx))
    (helt := fun b c => dt.elt_reg_regLaid (h :=
      hlin) (hord := hord)
      PR.zero harg b c)
    (vi := vi) (ts := ts) PR.zero_ne_one Wide.isLinOrd_tupLeLex hdd
    (Classical.arbitrary dt.KIx) st n

/-! ### The run, from the sentence and the clock -/

/-- **The handed program accepts, from the sentence alone.**
`wideRegAccept_regLaid_of_rules` with everything the *drawing* decides
supplied: the marking and its consequences (`regFacts_of_marked`), the
file's two ends (`exists_regTop`, `exists_regBot`), the opening's walk
(`exists_openingWalkReg`), the rounds (`exists_regValEnum`), the two exits
(`exitG_at_marker`), the dictionary the guess wrote (`guessTracks_hdict_of_old`),
the scratch it parks (`parked_ixSpineStOfB`) and the region the stage atoms stay
inside (`belowTop_regLaid`).

What is left is what the **reduction** decides: the assignment its guess writes,
the sentence being true at it, the order on the expanded universe, and the three
numbers of the clock – the last stated against the file's own bound, so that a
reduction proves them of its *drawing* and of nothing else. -/
theorem wideRegAccept_of_out_of_rules
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd) {bot : Option dt.KIx}
    (hE : NexEmitted PR bot)
    (hR : PR.table.Reads)
    (hdd : dt.dd0 < dt.dd) (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (hordP : ∀ p q : dt.X.Map A, p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hout : @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out)
    {a b k j m : ℕ} (hk : 1 ≤ k) (hkj : k + 1 < j) (hm : 0 < m)
    (hcard : (k + j) * m ≤ Nat.card (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
    (ha : dt.ixEvalWidth A (dt.nexRegW A (R') (Option dt.KIx))
      (dt.nexRegWP A (R') (Option dt.KIx))
      (dt.nexRegWR A (R') (Option dt.KIx))
      (dt.nexRegWK A (R') (Option dt.KIx)) ≤ a)
    (haa : a ≤ 2 ^ (k * m))
    (hb : dt.regBound (A := A) (R' := (R'))
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) + 1 ≤ b)
    (hbb : b ≤ 2 ^ (k * m))
    (hopenle : 4 * dt.regBound (A := A) (R' := (R'))
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) + 8 ≤ 2 ^ ((k + 1) * m)) :
    WideRegAccept (Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) := by
  classical
  have hlin := PR.table.isLinOrd_wmLe hR
  obtain ⟨harg, hargall, hupinp, botE, hbotm, hleast, hbotarg⟩ :=
    regFacts_of_marked hR hE.marked
  obtain ⟨gtop, htopF⟩ := dt.exists_regTop hlin hR.le ⟨botE, hbotm⟩
  obtain ⟨gbot, hbotF⟩ := dt.exists_regBot hlin hR.le ⟨botE, hbotm⟩
  obtain ⟨v₁, xw, y', hvi₁, hwalk, hxy, hyy', hyv⟩ :=
    exists_openingWalkReg hlin hbotm hleast (exists_above_botElt hR hbotarg)
  obtain ⟨n, mV, hmV0, hIncr, hTestT, hTestF, hKin, hUse, hTop, hnb⟩ :=
    dt.exists_regValEnum hlin hR.le hargall
  have hcellne : ∀ u : dt.RegIx (A := A) (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)),
      (fun _ => False) ≠ (dt.regLaid hlin hR.le).cell u := by
    intro u hc
    obtain ⟨w, hw⟩ := wmRegSeg_nonempty hlin u.2
    exact (congrFun hc w ▸ hw : ((fun _ => False) : Univ A
      (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) w).elim
  have hlogne : ∃ z : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd, logicalTop z := by
    obtain ⟨x, i, hi⟩ := exists_argElt (dt := dt) (A := A)
    exact ⟨x, i, hi⟩
  obtain ⟨e₀, -, he₀⟩ := exists_least hlin
    (P := fun _ : Univ A (R')
      (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => True)
    ⟨(PfpTag.sym, fun _ => Classical.arbitrary A), trivial⟩
  refine dt.wideRegAccept_regLaid_of_rules (PR := PR) hpl hE hR hlin hR.le
    (v₁ := v₁) (x := xw) (y := wmRegSeg botE) (y' := y') (s₀ := v₁)
    (top := logicalTop) (v' := v₁)
    hvi₁ hwalk hxy hyy' hyv hvi₁ hvi₁ σ
    (wmSetLe_succ_bot_of_nonempty hlin hvi₁ hlogne) hlogne
    (exitG_at_marker (PR' := PR) rfl hcellne)
    (exitG_at_marker (PR' := PR) rfl hcellne)
    (e₀ := e₀) (fun y => he₀ y trivial) harg hargall hupinp hbotm hleast hbotarg
    gtop gbot htopF hbotF
    (a₀ := 0) (aT := Fin.last n) (fun c => Fin.zero_le c) (fun c => Fin.le_last c)
    mV hmV0 hIncr hTestT hTestF _ _ rfl rfl ?_ ?_ ?_ ?_
    (Use := dt.RegUse (A := A) (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)))
    hUse (fun u u' => dt.mono_regLaid u u')
    (fun _ _ hu hlt => dt.up_regLaid (hord := hR.le) hargall hu hlt) hKin hTop
    (Below := fun s => WMSetLt WMLe s logicalTop)
    (fun iv x hs =>
      (guessTracks_hdict_of_old hlin
        (dt.ixSpineStOfB_old _ _ _ _ mV _ _ _ (Fin.last dt.nv))
        hvi₁ harity hs iv).trans
        (trackOf_of_blocks PR.zero_ne_one (dt.arOf_le_ko (some iv)) σ
          (fun ℓ => wmBlk_tupAddr (dt.arOf_le_ko (some iv)) x ℓ)))
    (fun c iv ts => belowTop_regLaid hlin hR.le hdd harg ts _ _)
    hordP hout hk hkj hm hcard ha haa ?_ hbb ?_
  · exact dt.ixSpineStOfB_mir _ _ _ _ mV _ _ _ (Fin.last dt.nv)
  · exact dt.ixSpineStOfB_bot _ _ _ _ mV _ _ _ (Fin.last dt.nv)
  · exact (dt.parked_ixSpineStOfB _ _ _ _ mV ⟨rfl, rfl⟩ (Fin.last dt.nv)).1
  · exact (dt.parked_ixSpineStOfB _ _ _ _ mV ⟨rfl, rfl⟩ (Fin.last dt.nv)).2
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [show dt.regBound (A := A) (R' := R')
      (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) =
        2 ^ Nat.card (dt.RegIx (A := A) (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF))) from rfl] at hb
    omega
  · have h1 : wideRank (wmRegSeg botE) <
        dt.regBound (A := A) (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) :=
      dt.wideRank_regLaid_cell_lt hlin hR.le hupinp ⟨botE, hbotm⟩
    have h2 : wideRank xw < wideRank (wmRegSeg botE) :=
      (wideRank_lt_iff hlin _ _).mpr
        ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hxy, ne_of_wmIncr hxy⟩)
    have h3 : wideRank (logicalTop (R := R')
        (P := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) (K := dt.KIx)
        (V := Fin dt.dd → A)) < wideRank ((dt.regLaid hlin hR.le).cell gbot) :=
      (wideRank_lt_iff hlin _ _).mpr
        (dt.work_regLaid hbotm hleast hbotarg (fun z hz => hz) gbot)
    have h4 : wideRank ((dt.regLaid hlin hR.le).cell gbot) <
        dt.regBound (A := A) (R' := R')
          (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) :=
      dt.wideRank_regLaid_cell_lt hlin hR.le hupinp gbot
    have h0 : wideRank (fun _ : Univ A (R')
        (NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd => False) = 0 :=
      wideRank_bot hlin
    obtain ⟨P, hP⟩ : ∃ P, 2 ^ ((k + 1) * m) = P := ⟨_, rfl⟩
    rw [hP] at hopenle ⊢
    obtain ⟨Bd, hBd⟩ : ∃ Bd, dt.regBound (A := A)
        (R' := R')
        (P' := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)) = Bd := ⟨_, rfl⟩
    rw [hBd] at hopenle h1 h4
    omega

end Yes

end PfpData

end Pfp

end DescriptiveComplexity
