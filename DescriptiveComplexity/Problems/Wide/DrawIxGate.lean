/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxExp
import DescriptiveComplexity.Problems.Wide.DrawInstGate

/-!
# The gates at an arbitrary file

A gate asks of one block of the working address that it encode a point: the
witness chain reads every tag's witness cell, the branch dispatches on the
one-hot decoding, and the branch's element loop evaluates the tag's domain
sentence at the decoded assignment. Every read goes to the cell of an encoded
tuple in the gated block, so this is
`DescriptiveComplexity.Problems.Wide.DrawInstGate` read at a coarse file exactly
as `DescriptiveComplexity.Problems.Wide.DrawIxExp` reads the expansion atoms:
the cells become the registers the layout names
(`DescriptiveComplexity.Draw.DrawData.ixEncG_iff`), the marks become marks on
registers, and the block value the gate reads is the one the address the marks
stand for holds (`DescriptiveComplexity.ixAddr`).

Only the declarations that mention the file are restated here; everything the
elementwise file says about the control alone is imported.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {I : Type} (F : LaidFile dt A R P I)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section GateInst

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (b : Fin dt.ko ⊕ Fin dt.ki)
variable (st : TapeSt dt A R P I) (t : dt.X.Tag)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (helt : ∀ (b' : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b' c) = dt.blkElt b' (pad zero c))
variable (hsepP : F.toLayout.NameSep zero dt.dd0Le) (hix : IsLinOrd F.le)

/-- **The register of one tag's witness read**: the one the layout names by the
tag's witness tuple in the gated block. -/
noncomputable def ixGateTagCell (c : Fin (Fintype.card dt.X.Tag)) : I :=
  F.toLayout.reg hhas b (dt.encCoord zero one
    (Sum.inl ((Fintype.equivFin dt.X.Tag).symm c)) (fun _ _ => zero)
    fun _ : Unit => zero)

variable (hnt : (dt.domPk t).n ≤ dt.eDim)

/-- **The register of the `r`-th domain leaf read at round `a`**: the one the
layout names by the member tuple the block atom spells. -/
noncomputable def ixGateECell (a : Lex (Fin dt.eDim → A))
    (r : Fin (dt.domNr t)) : I :=
  F.toLayout.reg hhas b (dt.encCoord zero one (Sum.inr (domLeafData t r).1)
    (fun _ => pad zero fun q => ofLex a (Fin.castLE hnt ((domLeafData t r).2 q)))
    fun _ : Unit => zero)

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
include helt in
/-- **The witness register holds the witness cell.** -/
theorem elt_ixGateTagCell (c : Fin (Fintype.card dt.X.Tag)) :
    elt (dt.ixGateTagCell F hhas one b c) = dt.gateTagCell zero one b c :=
  dt.elt_reg_encCoord hhas helt _ _ _ _

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.Structure A] in
include helt in
/-- **The domain-leaf register holds the leaf cell.** -/
theorem elt_ixGateECell (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.domNr t)) :
    elt (dt.ixGateECell F hhas one b t hnt a r) =
      dt.gateECell zero one b t hnt a r :=
  dt.elt_reg_encCoord hhas helt _ _ _ _

variable (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
variable (hrd : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}

variable (vAdr) in
/-- **The generated witness chain of a gate**, at the pack. -/
noncomputable def ixGateTagFam (f₀ : dt.CtlIx → A)
    (i : Fin (Fintype.card dt.X.Tag + 1)) : dt.CtlIx → A :=
  tagFam ((dt.gateArgs zero one b hc hn hrd).setTagFlag)
    (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
    (dt.ixGateTagCell F hhas one b) f₀ i


variable (vAdr) in
/-- **The generated family of branch `t`'s domain loop**, at the pack. -/
noncomputable def ixGateFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.domNr t + 1)) : dt.CtlIx → A :=
  elemFam ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
    ((dt.gateArgs zero one b hc hn hrd).initEl t)
    ((dt.gateArgs zero one b hc hn hrd).advEl t)
    (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
    (dt.ixGateECell F hhas one b t (hn t)) f₀ a j

variable {dt F hhas one b st t hnt hc hn hrd}


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The loop element is the round's wide tuple**, at every stage of a
gate's family. -/
theorem readLvE_ixGateFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.domNr t + 1)) :
    dt.readLvE (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j) =
      ofLex a := by
  classical
  have hchain : ∀ (b' : Lex (Fin dt.eDim → A)) (q : dt.CtlIx → A) (n : ℕ),
      dt.readLvE (chainSt
        (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) b' j'))
        (fun j' bb q' =>
          (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q n) = dt.readLvE q :=
    fun b' q n => readLvE_chainSt _ _
      (fun i bb f => readLvE_gate_setFlag i bb f _) q n
  have hiter : ∀ b' : Lex (Fin dt.eDim → A),
      dt.readLvE (elemIter
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
        ((dt.gateArgs zero one b hc hn hrd).initEl t)
        ((dt.gateArgs zero one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
        (dt.ixGateECell F hhas one b t (hn t)) f₀ b') = ofLex b' := by
    intro b'
    induction b' using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz, readLvE_gate_init,
        ofLex_eq_botTup_of_bot hz]
    | hstep w z hwz hnb ih =>
      have hz2 : elemIter
          ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
          ((dt.gateArgs zero one b hc hn hrd).initEl t)
          ((dt.gateArgs zero one b hc hn hrd).advEl t)
          (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
          (dt.ixGateECell F hhas one b t (hn t)) f₀ z =
        (dt.gateArgs zero one b hc hn hrd).advEl t
          (chainSt
            (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) w j'))
            (fun j' bb q' =>
              (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
                (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
            (elemIter ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
              ((dt.gateArgs zero one b hc hn hrd).initEl t)
              ((dt.gateArgs zero one b hc hn hrd).advEl t)
              (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
              (dt.ixGateECell F hhas one b t (hn t)) f₀ w) (dt.domNr t))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr) :=
        iterOrd_covers hwz hnb
      rw [hz2, readLvE_gate_adv, hchain, ih,
        ofLex_eq_tupNext_of_covers hwz hnb]
  rw [ixGateFam, elemFam, hchain]
  exact hiter a

/-! ### The witness chain: read-back and decode -/


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness flags read back**: after the chain, the flag of tag `t'`
holds the digit of `t'`'s witness cell in the gated block. -/
theorem ctlBit_ixGateTagFam_last (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (t' : dt.X.Tag) :
    dt.ctlBit one
        (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
          (Fin.last (Fintype.card dt.X.Tag))) (dt.gateTagC hc t') ↔
      st.mir (dt.ixGateTagCell F hhas one b (Fintype.equivFin dt.X.Tag t')) := by
  classical
  have hinj : ∀ c c' : Fin (Fintype.card dt.X.Tag),
      dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm c) =
        dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm c') → c = c' := by
    intro c c' h
    have h1 := dt.tgfC_injective h
    have h2 : (Fintype.equivFin dt.X.Tag) ((Fintype.equivFin dt.X.Tag).symm c)
        = (Fintype.equivFin dt.X.Tag) ((Fintype.equivFin dt.X.Tag).symm c') :=
      Fin.ext (by simpa using congrArg Fin.val h1)
    simpa using h2
  have hchain := dt.ctlBit_chain_setCtl (zero := zero) hzo
    (fun c => dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm c)) hinj
    (fun c => st.mir (dt.ixGateTagCell F hhas one b c)) f₀
    (Fintype.card dt.X.Tag) (Fintype.equivFin dt.X.Tag t')
    (Fintype.equivFin dt.X.Tag t').isLt
  have hslot : dt.gateTagC hc
      ((Fintype.equivFin dt.X.Tag).symm (Fintype.equivFin dt.X.Tag t')) =
      dt.gateTagC hc t' := by
    rw [Equiv.symm_apply_apply]
  rw [hslot] at hchain
  exact hchain


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **The witness flags after the chain read the block value**: the flag of
tag `t'` holds exactly when `t'`'s witness tuple belongs to the gated
block. -/
theorem ctlBit_ixGateTagFam_wit (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (t' : dt.X.Tag) :
    dt.ctlBit one
        (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
          (Fin.last (Fintype.card dt.X.Tag))) (dt.gateTagC hc t') ↔
      wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)
        (encTagTup dt.ly zero one t') := by
  rw [ctlBit_ixGateTagFam_last hzo f₀ t',
    ← ixAddr_elt hinj st.mir
      (dt.ixGateTagCell F hhas one b ((Fintype.equivFin dt.X.Tag) t')),
    dt.elt_ixGateTagCell F hhas one b helt ((Fintype.equivFin dt.X.Tag) t')]
  have hcell : dt.gateTagCell (R := R) (P := P) zero one b
      ((Fintype.equivFin dt.X.Tag) t') =
      dt.blkElt b (encTagTup dt.ly zero one t') := by
    rw [gateTagCell, Equiv.symm_apply_apply]
    rfl
  rw [hcell]
  exact Iff.rfl


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **The chain's decoding always dispatches**: at a block value with a
one-hot witness the flags decode its tag, and at any other the default
branch fires — the totality of the branch checkpoint on *every* block
value the sweep produces. -/
theorem ixDspTagsAre_gateFam (hzo : zero ≠ one) (f₀ : dt.CtlIx → A) :
    dt.DspTagsAre one hc
      (dt.dspTagOf zero one
        (wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)))
      (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
        (Fin.last (Fintype.card dt.X.Tag))) := by
  classical
  by_cases h : ∃ t₁ : dt.X.Tag, ∀ t' : dt.X.Tag,
      wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)
        (encTagTup dt.ly zero one t') ↔ t' = t₁
  · left
    rw [dspTagOf, dif_pos h]
    intro t'
    rw [ctlBit_ixGateTagFam_wit hinj helt hzo f₀ t']
    exact h.choose_spec t'
  · right
    refine ⟨by rw [dspTagOf, dif_neg h], fun t₁ hc1 => h ⟨t₁, fun t' => ?_⟩⟩
    rw [← ctlBit_ixGateTagFam_wit (b := b) (st := st) (vAdr := vAdr) hinj helt hzo f₀ t']
    exact hc1 t'

/-! ### The domain payload at a generated state, and the leaf guards -/


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The payload a domain leaf spells at a generated state** is the round's
tuple's. -/
theorem domPay_ixGateFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.domNr t + 1)) (r : Fin (dt.domNr t)) :
    dt.domPay (zero := zero) (t := t) (r := r) (hn := hn t)
      (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j) =
      pad zero fun q => ofLex a (Fin.castLE (hn t) ((domLeafData t r).2 q)) := by
  refine congrArg (pad zero) (funext fun q => ?_)
  exact congrFun (readLvE_ixGateFam f₀ a j) _


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A domain leaf read's guard holds at its cell.** -/
theorem ixDomMatch_gateFam (hzo : zero ≠ one) (hix : IsLinOrd F.le)
    (hsepP : F.toLayout.NameSep zero dt.dd0Le)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.domNr t + 1)) (r : Fin (dt.domNr t)) :
    dt.domMatch zero one b t r (hn t)
      (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j)
      (dt.ixBack F.toLayout zero one dt.dd0Le st
        (F.cell (dt.ixGateECell F hhas one b t (hn t) a r))) := by
  refine (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsepP hhas _ _ _ _ _).mpr ?_
  have hcoord : dt.encCoord zero one (Sum.inr (domLeafData t r).1)
      (dt.domPay (zero := zero) (t := t) (r := r) (hn := hn t))
      (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j) =
    dt.encCoord zero one (Sum.inr (domLeafData t r).1)
      (fun _ => pad zero fun q => ofLex a (Fin.castLE (hn t) ((domLeafData t r).2 q)))
      (fun _ : Unit => zero) := by
    funext c
    simp only [encCoord]
    rw [domPay_ixGateFam f₀ a j r]
  rw [ixGateECell, hcoord]


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A domain leaf read's guard identifies its cell.** -/
theorem ixDomMatch_gateFam_uniq (hzo : zero ≠ one) (hix : IsLinOrd F.le)
    (hsepP : F.toLayout.NameSep zero dt.dd0Le)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.domNr t + 1)) (r : Fin (dt.domNr t))
    {y : Univ A R P dt.KIx dt.dd → Prop}
    (hM : dt.domMatch zero one b t r (hn t)
      (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j)
      (dt.ixBack F.toLayout zero one dt.dd0Le st y)) :
    y = F.cell (dt.ixGateECell F hhas one b t (hn t) a r) := by
  by_cases hreg : ∃ u : I, y = F.cell u
  · obtain ⟨u, rfl⟩ := hreg
    have hu := (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsepP hhas _ _ _ _ u).mp hM
    have hcoord : dt.encCoord zero one (Sum.inr (domLeafData t r).1)
        (dt.domPay (zero := zero) (t := t) (r := r) (hn := hn t))
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j) =
      dt.encCoord zero one (Sum.inr (domLeafData t r).1)
        (fun _ => pad zero fun q => ofLex a (Fin.castLE (hn t) ((domLeafData t r).2 q)))
        (fun _ : Unit => zero) := by
      funext c
      simp only [encCoord]
      rw [domPay_ixGateFam f₀ a j r]
    rw [hu, ixGateECell, hcoord]
  · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
      (fun u hc' => hreg ⟨u, hc'⟩))

/-- **A gate's leaf at the file, over the wide valuation**: the tag's domain
sentence at the decoded assignment of the block value the marks' address
holds. -/
noncomputable def ixGateLeafP (dt : DrawData L) {I : Type}
    (b : Fin dt.ko ⊕ Fin dt.ki) (st : TapeSt dt A R P I) (t : dt.X.Tag)
    (hnt : (dt.domPk t).n ≤ dt.eDim) {elt : I → Univ A R P dt.KIx dt.dd}
    (zero one : A) (v : Fin dt.eDim → A) : Prop :=
  dt.domLeaf t
    (decRho dt.ly zero one
      (wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)))
    fun j => v (Fin.castLE hnt j)

/-! ### The gate's machine run -/

section GateRun

variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepR : F.toLayout.NameSep PR.zero dt.dd0Le) (hixR : IsLinOrd F.le)
variable {eltR : I → Univ A R P dt.KIx dt.dd}
variable (hinjR : Function.Injective eltR)
variable (heltR : ∀ (b' : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  eltR (F.toLayout.reg hhasP b' c) = dt.blkElt b' (pad PR.zero c))
variable {emb : TagPh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr → P}
variable {exitPh : P}
variable {rEmb : ∀ i : TagSite (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr,
  TagSh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : TagSite (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr)
    (ρ : TagSh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr i),
  PR.rules (rEmb i ρ) = tagRule PR.one Slot.wk Slot.reg emb
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackT)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).MatchT)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).setTagFlag)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).TagsAre)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackE)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).MatchE)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).setFlagE)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).initEl)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).advEl)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).exitSt)
    ((dt.gateArgs PR.zero PR.one b hc hn hrd).IsMaxEl)
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : I} (hbot : ∀ y, F.le gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable {t₀ : dt.SlotIx} {m₀ : I → Prop}
variable (hm₀ : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r t₀ =
  bitVal PR.zero PR.one (bitAtOf F.cell m₀ r))
variable (hwkt₀ : (Slot.wk : dt.SlotIx) ≠ t₀)
variable (hrgt₀ : (Slot.reg : dt.SlotIx) ≠ t₀)
variable (htag : dt.dspTagOf PR.zero PR.one
  (wmBlk (ixAddr eltR st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)) = t)
variable (f₀ : dt.CtlIx → A)


include hrules hR hlin hixR hsepR hbot hv hvi hwkSt hm₀ hwkt₀ hrgt₀ hinjR heltR htag in
/-- **The gate's machine run**: from the machinery's first phase at the
marker – the witness chain reading the block value, the dispatch onto the
decoded tag's branch (or the default tag's, where the witness is not
one-hot), and the branch's domain loop over the wide tuples – to the exit
phase one cell to the marker's right. -/
theorem ixGate_reachesIn (w : ℕ)
    (hcostT : ∀ c : Fin (Fintype.card dt.X.Tag),
      2 * (wideRank (F.cell (dt.ixGateTagCell F hhasP PR.one b c)) -
        wideRank v) + 2 ≤ w)
    (hcostE : ∀ (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.domNr t)),
      2 * (wideRank (F.cell (dt.ixGateECell F hhasP PR.one b t (hn t) a r)) -
        wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((w + 2) * Fintype.card dt.X.Tag + 2 +
        ((2 + (w + 2) * dt.domNr t) * (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1))
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell t₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.gateArgs PR.zero PR.one b hc hn hrd).exitSt t
            (dt.ixGateFam F hhasP PR.one b st t hc hn hrd v
              (dt.ixGateTagFam F hhasP PR.one b st hc hn hrd v f₀
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr t)))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hwk_ne_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hrg_ne_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hTA : dt.DspTagsAre PR.one hc t
      (dt.ixGateTagFam F hhasP PR.one b st hc hn hrd v f₀
        (Fin.last (Fintype.card dt.X.Tag))) := by
    rw [← htag]
    exact ixDspTagsAre_gateFam (b := b) (st := st) (vAdr := v) hinjR heltR hzo f₀
  refine tag_reachesIn_iter F.toIxFile hrules hR hlin hixR hbot hv hvi
    (fun r => by
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun r => rfl)
    (mT := fun _ => st.mir)
    (fun i r => rfl)
    (fun i => hwk_ne_mir)
    (fun i => hrg_ne_mir)
    hm₀ hwkt₀ hrgt₀
    (xT := dt.ixGateTagCell F hhasP PR.one b) (f₀ := f₀)
    ?_ ?_
    (τ := t)
    hTA
    (mE := fun _ => st.mir)
    (fun j r => rfl)
    (fun j => hwk_ne_mir)
    (fun j => hrg_ne_mir)
    (a₀ := toLex botTup) (aT := toLex topTup)
    (fun a => tup_isBot_iff.mpr (fun p x => botTup_le p x) a)
    (fun a => tup_isTop_iff.mpr (fun p x => le_topTup p x) a)
    (xE := dt.ixGateECell F hhasP PR.one b t (hn t))
    ?_ ?_ ?_ ?_ w hcostT hcostE
  · -- the witness guards hold at their cells
    intro i
    rw [passTracks_of_back
      (t := (dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackT i)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := st.mir) F.toIxFile (fun r => rfl) _]
    exact (dt.ixEncG_iff hzo (F.toIxFile.injective hixR) hsepR hhasP _ _ _ _ _).mpr rfl
  · -- the witness guards identify their cells
    intro i r hM
    rw [passTracks_of_back
      (t := (dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackT i)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := st.mir) F.toIxFile (fun r' => rfl) _] at hM
    by_cases hreg : ∃ u : I, r = F.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.ixEncG_iff hzo (F.toIxFile.injective hixR) hsepR hhasP _ _ _ _ u).mp hM
      rw [hu]
      rfl
    · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
        (fun u hc' => hreg ⟨u, hc'⟩))
  · -- the domain leaf guards hold at their cells
    intro a j
    rw [passTracks_of_back
      (t := (dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackE t j)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := st.mir) F.toIxFile (fun r => rfl) _]
    exact ixDomMatch_gateFam hzo hixR hsepR _ a j.castSucc j
  · -- the domain leaf guards identify their cells
    intro a j r hM
    rw [passTracks_of_back
      (t := (dt.gateArgs PR.zero PR.one b hc hn hrd).rdTrackE t j)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := st.mir) F.toIxFile (fun r' => rfl) _] at hM
    exact ixDomMatch_gateFam_uniq hzo hixR hsepR _ a j.castSucc j hM
  · -- exhausted at the top
    change IsMaxTup (dt.readLvE _)
    rw [show dt.readLvE (elemFam
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).setFlagE t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).initEl t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
        (dt.ixGateECell F hhasP PR.one b t (hn t))
        (tagFam (dt.gateArgs PR.zero PR.one b hc hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
          (dt.ixGateTagCell F hhasP PR.one b) f₀
          (Fin.last (Fintype.card dt.X.Tag)))
        (toLex topTup) (Fin.last (dt.domNr t))) =
      ofLex (toLex topTup) from readLvE_ixGateFam _ _ _]
    exact isMaxTup_topTup
  · -- not exhausted below the top
    intro a ha hcx
    have hc2 : IsMaxTup (dt.readLvE (elemFam
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).setFlagE t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).initEl t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
        (dt.ixGateECell F hhasP PR.one b t (hn t))
        (tagFam (dt.gateArgs PR.zero PR.one b hc hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
          (dt.ixGateTagCell F hhasP PR.one b) f₀
          (Fin.last (Fintype.card dt.X.Tag)))
        a (Fin.last (dt.domNr t)))) := hcx
    rw [show dt.readLvE (elemFam
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).setFlagE t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).initEl t)
        ((dt.gateArgs PR.zero PR.one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
        (dt.ixGateECell F hhasP PR.one b t (hn t))
        (tagFam (dt.gateArgs PR.zero PR.one b hc hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (fun _ => st.mir)
          (dt.ixGateTagCell F hhasP PR.one b) f₀
          (Fin.last (Fintype.card dt.X.Tag)))
        a (Fin.last (dt.domNr t))) =
      ofLex a from readLvE_ixGateFam _ _ _] at hc2
    exact absurd (tup_isTop_iff.mpr hc2 (toLex topTup)) (not_le_of_gt ha)

end GateRun

/-! ### The sub-fold: the sac invariant and the conjoining exit -/

section GateVerdict


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The domain leaf-read flags read back** at a round's end. -/
theorem ctlBit_rdf_ixGateFam (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.domNr t)) :
    dt.ctlBit one
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a
          (Fin.last (dt.domNr t)))
        (dt.rdfC (Fin.castLE (hrd t) r)) ↔
      st.mir (dt.ixGateECell F hhas one b t (hn t) a r) := by
  have hinj : ∀ r₁ r₂ : Fin (dt.domNr t),
      dt.rdfC (Fin.castLE (hrd t) r₁) = dt.rdfC (Fin.castLE (hrd t) r₂) →
        r₁ = r₂ := fun r₁ r₂ h =>
    Fin.castLE_injective _ (dt.rdfC_injective h)
  exact dt.ctlBit_chain_setCtl hzo
    (fun r' => dt.rdfC (Fin.castLE (hrd t) r')) hinj
    (fun r' => st.mir (dt.ixGateECell F hhas one b t (hn t) a r'))
    (elemIter ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
      ((dt.gateArgs zero one b hc hn hrd).initEl t)
      ((dt.gateArgs zero one b hc hn hrd).advEl t)
      (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
      (dt.ixGateECell F hhas one b t (hn t)) f₀ a)
    (dt.domNr t) r r.isLt


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **The leaf flag's value at a round's end is the gate's leaf**: the
domain sentence's matrix at the decoded assignment, read at the round's
tuple. -/
theorem domLeafVal_ixGateFam (hzo : zero ≠ one)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) :
    dt.domLeafVal one t (hn t) (hrd t)
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a
          (Fin.last (dt.domNr t))) ↔
      dt.ixGateLeafP (elt := elt) b st t (hn t) zero one (ofLex a) := by
  have hval := dt.domLeafVal_iff t (hn t) (hrd t)
    (decRho dt.ly zero one
      (wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)))
    (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a (Fin.last (dt.domNr t)))
    (fun r => by
      refine (ctlBit_rdf_ixGateFam hzo f₀ a r).trans ?_
      have hpay : (fun q => ofLex a
          (Fin.castLE (hn t) ((domLeafData t r).2 q))) =
          fun q => dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a
            (Fin.last (dt.domNr t))
            (dt.lvE (Fin.castLE (hn t) ((domLeafData t r).2 q))) :=
        funext fun q =>
          (congrFun (readLvE_ixGateFam f₀ a (Fin.last (dt.domNr t))) _).symm
      rw [ixGateECell, ← ixAddr_elt hinj st.mir
          (F.toLayout.reg hhas b (dt.encCoord zero one (Sum.inr (domLeafData t r).1)
            (fun _ => pad zero fun q => ofLex a
              (Fin.castLE (hn t) ((domLeafData t r).2 q))) fun _ : Unit => zero)),
        dt.elt_reg_encCoord hhas helt, hpay]
      exact Iff.rfl)
  refine hval.trans ?_
  rw [ixGateLeafP]
  refine iff_of_eq (congrArg _ (funext fun j => ?_))
  exact congrFun (readLvE_ixGateFam f₀ a (Fin.last (dt.domNr t))) _


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **A gate's accumulators fold the strict prefix**: at every round's
entry, the `sac` slots hold the contributions of the domain sentence's
prefix at the round's tuple. -/
theorem readSac_ixGateIter (hzo : zero ≠ one)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) (j : ℕ)
    (hj : j < dt.eDim) :
    dt.readSac one (elemIter
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
        ((dt.gateArgs zero one b hc hn hrd).initEl t)
        ((dt.gateArgs zero one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
        (dt.ixGateECell F hhas one b t (hn t)) f₀ a) j ↔
      accCVal (dt.domPk t).pol (dt.ixGateLeafP (elt := elt) b st t (hn t) zero one)
        (· ≤ · : A → A → Prop) j (ofLex a) := by
  classical
  induction a using order_induction generalizing j with
  | hmin z hz =>
    rw [elemIter, iterOrd_bot hz]
    have hread : dt.readSac one
        ((dt.gateArgs zero one b hc hn hrd).initEl t f₀
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) j ↔
        ((dt.domPk t).pol j = false) := by
      change dt.readSac one (dt.gateInit zero one t f₀) j ↔ _
      rw [gateInit, initSac]
      exact readSac_putSac hzo _ _ hj
    rw [hread, ofLex_eq_botTup_of_bot hz]
    exact (accCVal_bot (fun i x => botTup_le i x) j).symm
  | hstep w z hwz hnb ih =>
    have hnm : ¬IsMaxTup (ofLex w) := by
      intro hcx
      exact absurd (tup_isTop_iff.mpr hcx z) (not_le_of_gt hwz)
    obtain ⟨pc, hpc, hAt⟩ := tupSuccAt_tupCarry (t := ofLex w) hnm
    have hzw : ofLex z = tupNext (ofLex w) := ofLex_eq_tupNext_of_covers hwz hnb
    rw [← hzw] at hAt
    set Fc := elemFam ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
      ((dt.gateArgs zero one b hc hn hrd).initEl t)
      ((dt.gateArgs zero one b hc hn hrd).advEl t)
      (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
      (dt.ixGateECell F hhas one b t (hn t)) f₀ w
      (Fin.last (dt.domNr t)) with hF
    have hreadF : ∀ j' : ℕ, dt.readSac one Fc j' ↔
        dt.readSac one (elemIter
          ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
          ((dt.gateArgs zero one b hc hn hrd).initEl t)
          ((dt.gateArgs zero one b hc hn hrd).advEl t)
          (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
          (dt.ixGateECell F hhas one b t (hn t)) f₀ w) j' := by
      intro j'
      rw [hF]
      exact readSac_chainSt _ _
        (fun i bb f j'' => by
          change dt.readSac one (dt.setCtl zero one
            (dt.rdfC (Fin.castLE (hrd t) i)) (bb = true) f) j'' ↔ _
          have hne : ∀ j₃ : Fin dt.eDim,
              dt.sacC j₃ ≠ dt.rdfC (Fin.castLE (hrd t) i) :=
            fun j₃ h => nomatch h
          exact readSac_setCtl hne _ f j'') _ _ j'
    have hlvF : dt.readLvE Fc = ofLex w :=
      readLvE_ixGateFam f₀ w (Fin.last (dt.domNr t))
    have hstepEq : elemIter
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
        ((dt.gateArgs zero one b hc hn hrd).initEl t)
        ((dt.gateArgs zero one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
        (dt.ixGateECell F hhas one b t (hn t)) f₀ z =
        (dt.gateArgs zero one b hc hn hrd).advEl t Fc
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr) := by
      rw [elemIter, iterOrd_covers hwz hnb]
      rfl
    rw [hstepEq]
    have hadv : ∀ j' : ℕ, j' < dt.eDim →
        (dt.readSac one
          ((dt.gateArgs zero one b hc hn hrd).advEl t Fc
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) j' ↔
        dt.readSac one
          (dt.carrySac zero one (dt.domPk t).pol (tupCarry (dt.readLvE Fc))
            (dt.setSubLeaf zero one
              (dt.domLeafVal one t (hn t) (hrd t) Fc) Fc)) j') := by
      intro j' hj'
      change dt.readSac one (dt.gateAdv zero one t (hn t) (hrd t) Fc) j' ↔ _
      rw [gateAdv]
      exact readSac_advLvE _ j'
    rw [hadv j hj, hlvF]
    refine accCVal_step (le := (· ≤ · : A → A → Prop)) (v := ofLex w)
      ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
        fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
      (hc := hpc ▸ pc.isLt) ?_ ?_ ?_ ?_
      (acc := dt.readSac one (dt.setSubLeaf zero one
        (dt.domLeafVal one t (hn t) (hrd t) Fc) Fc))
      (leaf := dt.ctlBit one (dt.setSubLeaf zero one
        (dt.domLeafVal one t (hn t) (hrd t) Fc) Fc) dt.subLeafC)
      ?_ ?_ ?_ j hj
    · intro i hi
      have hlt : (i : ℕ) < (pc : ℕ) := by omega
      exact hAt.1 i (Fin.lt_def.mpr hlt)
    · intro i hi x
      have hlt : (pc : ℕ) < (i : ℕ) := by omega
      exact (hAt.2.2 i (Fin.lt_def.mpr hlt)).1 x
    · intro i hi x
      have hlt : (pc : ℕ) < (i : ℕ) := by omega
      exact (hAt.2.2 i (Fin.lt_def.mpr hlt)).2 x
    · intro x
      constructor
      · rintro ⟨hle, hnle⟩
        by_contra hbw
        have hwb : ofLex w ⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ < x :=
          lt_of_not_ge (by
            intro hcx
            exact hbw (by
              have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim)
                  = pc := Fin.ext hpc.symm
              rw [hpcc] at hcx ⊢
              exact hcx))
        have hblt : x < ofLex z ⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ :=
          lt_of_le_not_ge hle hnle
        have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim) = pc :=
          Fin.ext hpc.symm
        rw [hpcc] at hwb hblt
        exact hAt.2.1.2 x ⟨hwb, hblt⟩
      · intro hle
        have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim) = pc :=
          Fin.ext hpc.symm
        rw [hpcc]
        rw [hpcc] at hle
        have hblt : x < ofLex z pc := lt_of_le_of_lt hle hAt.2.1.1
        exact ⟨le_of_lt hblt, not_le_of_gt hblt⟩
    · intro i hi
      rw [readSac_setSubLeaf, hreadF i]
      exact ih i hi
    · rw [ctlBit_setSubLeaf hzo]
      exact domLeafVal_ixGateFam hinj helt hzo f₀ w
    · intro i hi
      exact readSac_carrySac hzo (dt.domPk t).pol (tupCarry (ofLex w))
        (dt.setSubLeaf zero one
          (dt.domLeafVal one t (hn t) (hrd t) Fc) Fc) (j := i) hi

/-! ### The gates' flag rides, and the conjoining exit -/


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness flags survive a branch's domain loop**: neither the leaf
reads nor the fold write them, so the conjoining exit still reads the
chain's decoding. -/
theorem ctlBit_tgf_ixGateFam (t₂ : dt.X.Tag) (f₀ : dt.CtlIx → A)
    (a : Lex (Fin dt.eDim → A)) (j : Fin (dt.domNr t + 1)) :
    dt.ctlBit one
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr f₀ a j)
        (dt.gateTagC hc t₂) ↔
      dt.ctlBit one f₀ (dt.gateTagC hc t₂) := by
  classical
  have hupdE : ∀ (i : Fin (dt.domNr t)) (bb : Bool) (f : dt.CtlIx → A),
      dt.ctlBit one
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t i bb f
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) (dt.gateTagC hc t₂) ↔
      dt.ctlBit one f (dt.gateTagC hc t₂) := by
    intro i bb f
    change dt.ctlBit one (dt.setCtl zero one
      (dt.rdfC (Fin.castLE (hrd t) i)) (bb = true) f) _ ↔ _
    have hne : dt.gateTagC hc t₂ ≠ dt.rdfC (Fin.castLE (hrd t) i) :=
      fun h => nomatch h
    exact ctlBit_setCtl_of_ne hne _ _
  have hchain : ∀ (b' : Lex (Fin dt.eDim → A)) (q : dt.CtlIx → A) (n : ℕ),
      dt.ctlBit one (chainSt
        (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) b' j'))
        (fun j' bb q' =>
          (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q n) (dt.gateTagC hc t₂) ↔
      dt.ctlBit one q (dt.gateTagC hc t₂) :=
    fun b' q n => ctlBit_chainSt_of _ _ _
      (fun i bb f => hupdE i bb f) q n
  have hiter : ∀ b' : Lex (Fin dt.eDim → A),
      dt.ctlBit one (elemIter
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
        ((dt.gateArgs zero one b hc hn hrd).initEl t)
        ((dt.gateArgs zero one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
        (dt.ixGateECell F hhas one b t (hn t)) f₀ b') (dt.gateTagC hc t₂) ↔
      dt.ctlBit one f₀ (dt.gateTagC hc t₂) := by
    intro b'
    induction b' using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz]
      exact ctlBit_tgf_gate_init t₂ _ _
    | hstep w z hwz hnb ih =>
      have hz2 := iterOrd_covers
        (init := ((dt.gateArgs zero one b hc hn hrd).initEl t f₀
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)))
        (step := fun a' q => (dt.gateArgs zero one b hc hn hrd).advEl t
          (chainSt
            (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) a' j'))
            (fun j' bb q' =>
              (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
                (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q (dt.domNr t))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
        hwz hnb
      rw [elemIter] at ih ⊢
      rw [hz2, ctlBit_tgf_gate_adv t₂, hchain]
      exact ih
  rw [ixGateFam, elemFam, hchain]
  exact hiter a


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The gates' flag survives one gate's machinery**: neither the witness
chain nor the branch's domain loop writes it. -/
theorem ctlBit_gateFlagC_ixGateFam (f₀ : dt.CtlIx → A)
    (a : Lex (Fin dt.eDim → A)) (j : Fin (dt.domNr t + 1)) :
    dt.ctlBit one
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag))) a j) dt.gateFlagC ↔
      dt.ctlBit one f₀ dt.gateFlagC := by
  classical
  have hupdE : ∀ (i : Fin (dt.domNr t)) (bb : Bool) (f : dt.CtlIx → A),
      dt.ctlBit one
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t i bb f
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) dt.gateFlagC ↔
      dt.ctlBit one f dt.gateFlagC := by
    intro i bb f
    change dt.ctlBit one (dt.setCtl zero one
      (dt.rdfC (Fin.castLE (hrd t) i)) (bb = true) f) _ ↔ _
    have hne : dt.gateFlagC ≠ dt.rdfC (Fin.castLE (hrd t) i) :=
      fun h => nomatch h
    exact ctlBit_setCtl_of_ne hne _ _
  have hchain : ∀ (b' : Lex (Fin dt.eDim → A)) (q : dt.CtlIx → A) (n : ℕ),
      dt.ctlBit one (chainSt
        (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) b' j'))
        (fun j' bb q' =>
          (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q n) dt.gateFlagC ↔
      dt.ctlBit one q dt.gateFlagC :=
    fun b' q n => ctlBit_chainSt_of _ _ _
      (fun i bb f => hupdE i bb f) q n
  have hiter : ∀ b' : Lex (Fin dt.eDim → A),
      dt.ctlBit one (elemIter
        ((dt.gateArgs zero one b hc hn hrd).setFlagE t)
        ((dt.gateArgs zero one b hc hn hrd).initEl t)
        ((dt.gateArgs zero one b hc hn hrd).advEl t)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (fun _ => st.mir)
        (dt.ixGateECell F hhas one b t (hn t))
        (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
          (Fin.last (Fintype.card dt.X.Tag))) b') dt.gateFlagC ↔
      dt.ctlBit one (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
        (Fin.last (Fintype.card dt.X.Tag))) dt.gateFlagC := by
    intro b'
    induction b' using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz]
      exact ctlBit_gateFlagC_gate_init _ _
    | hstep w z hwz hnb ih =>
      have hz2 := iterOrd_covers
        (init := ((dt.gateArgs zero one b hc hn hrd).initEl t
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag)))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)))
        (step := fun a' q => (dt.gateArgs zero one b hc hn hrd).advEl t
          (chainSt
            (fun j' => st.mir (dt.ixGateECell F hhas one b t (hn t) a' j'))
            (fun j' bb q' =>
              (dt.gateArgs zero one b hc hn hrd).setFlagE t j' bb q'
                (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q (dt.domNr t))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
        hwz hnb
      rw [elemIter] at ih ⊢
      rw [hz2, ctlBit_gateFlagC_gate_adv, hchain]
      exact ih
  have htag : dt.ctlBit one (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
      (Fin.last (Fintype.card dt.X.Tag))) dt.gateFlagC ↔
      dt.ctlBit one f₀ dt.gateFlagC := by
    rw [ixGateTagFam, tagFam]
    refine ctlBit_chainSt_of _ _ _ (fun i bb f => ?_) f₀ _
    change dt.ctlBit one (dt.setCtl zero one
      (dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm i)) (bb = true) f)
      _ ↔ _
    have hne : dt.gateFlagC ≠
        dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm i) :=
      fun h => nomatch h
    exact ctlBit_setCtl_of_ne hne _ _
  rw [ixGateFam, elemFam, hchain, hiter a]
  exact htag


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **The verdict the conjoining exit carries**: the gates' flag holds after
one gate exactly when it held before – every earlier block passed – **and**
the block value's witness is one-hot at the dispatched tag – so the default
branch always clears – **and** the fold of this block's domain sentence
over the whole wide enumeration holds, i.e. the tag's domain condition at
the decoded assignment. -/
theorem ctlBit_gateFlagC_ixGate_exit (hzo : zero ≠ one) (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.gateArgs zero one b hc hn hrd).exitSt t
          (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
            (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr t)))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) dt.gateFlagC ↔
      (dt.ctlBit one f₀ dt.gateFlagC ∧
        (∀ t' : dt.X.Tag,
          wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)
            (encTagTup dt.ly zero one t') ↔ t' = t) ∧
        foldFrom (dt.domPk t).pol (dt.ixGateLeafP (elt := elt) b st t (hn t) zero one)
          (· ≤ · : A → A → Prop) 0 topTup) := by
  classical
  change dt.ctlBit one (dt.gateExit zero one t hc (hn t) (hrd t)
    (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
      (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
        (Fin.last (Fintype.card dt.X.Tag)))
      (toLex topTup) (Fin.last (dt.domNr t)))) dt.gateFlagC ↔ _
  rw [gateExit, ctlBit_setCtl_self hzo]
  refine and_congr (ctlBit_gateFlagC_ixGateFam f₀ (toLex topTup)
    (Fin.last (dt.domNr t))) (and_congr ?_ ?_)
  · -- the one-hotness conjunct reads the block value off the surviving
    -- witness flags
    constructor
    · intro hg t'
      rw [← ctlBit_ixGateTagFam_wit (b := b) (st := st)
          (hc := hc) (hn := hn) (hrd := hrd) (vAdr := vAdr) hinj helt hzo f₀ t',
        ← ctlBit_tgf_ixGateFam (b := b) (st := st) (t := t)
          (hc := hc) (hn := hn) (hrd := hrd) (vAdr := vAdr) t'
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr t))]
      exact hg t'
    · intro hone t'
      rw [ctlBit_tgf_ixGateFam (b := b) (st := st) (t := t)
          (hc := hc) (hn := hn) (hrd := hrd) (vAdr := vAdr) t'
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr t)),
        ctlBit_ixGateTagFam_wit (b := b) (st := st)
          (hc := hc) (hn := hn) (hrd := hrd) (vAdr := vAdr) hinj helt hzo f₀ t']
      exact hone t'
  have hacc : ∀ j : ℕ, j < dt.eDim →
      (dt.readSac one (dt.setSubLeaf zero one
        (dt.domLeafVal one t (hn t) (hrd t)
          (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
            (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr t))))
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr t)))) j ↔
      accCVal (dt.domPk t).pol (dt.ixGateLeafP (elt := elt) b st t (hn t) zero one)
        (· ≤ · : A → A → Prop) j (ofLex (toLex topTup))) := by
    intro j hj
    rw [readSac_setSubLeaf]
    refine Iff.trans ?_ (readSac_ixGateIter (F := F) (hhas := hhas) (b := b)
      (hc := hc) (hrd := hrd) (vAdr := vAdr) hinj helt hzo
      (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
        (Fin.last (Fintype.card dt.X.Tag))) (toLex topTup) j hj)
    rw [ixGateFam, elemFam]
    refine readSac_chainSt _ _ (fun i bb f j'' => ?_) _ _ j
    change dt.readSac one (dt.setCtl zero one
      (dt.rdfC (Fin.castLE (hrd t) i)) (bb = true) f) j'' ↔ _
    have hne : ∀ j₃ : Fin dt.eDim,
        dt.sacC j₃ ≠ dt.rdfC (Fin.castLE (hrd t) i) := fun j₃ h => nomatch h
    exact readSac_setCtl hne _ f j''
  have hleaf : dt.ctlBit one (dt.setSubLeaf zero one
      (dt.domLeafVal one t (hn t) (hrd t)
        (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
          (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr t))))
      (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
        (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
          (Fin.last (Fintype.card dt.X.Tag)))
        (toLex topTup) (Fin.last (dt.domNr t)))) dt.subLeafC ↔
      dt.ixGateLeafP (elt := elt) b st t (hn t) zero one (ofLex (toLex topTup)) := by
    rw [ctlBit_setSubLeaf hzo]
    exact domLeafVal_ixGateFam hinj helt hzo _ (toLex topTup)
  exact sacVerdict_iff_foldFrom hacc hleaf


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
include hinj helt in
/-- **The gate's verdict is the gate**: after one gate the flag holds
exactly when it held before – every earlier block passed – and the block
value's witness is one-hot at the dispatched tag and the decoded assignment
satisfies that tag's domain sentence. -/
theorem ctlBit_gateFlagC_ixGate_domHolds (hzo : zero ≠ one)
    (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.gateArgs zero one b hc hn hrd).exitSt t
          (dt.ixGateFam F hhas one b st t hc hn hrd vAdr
            (dt.ixGateTagFam F hhas one b st hc hn hrd vAdr f₀
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr t)))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) dt.gateFlagC ↔
      (dt.ctlBit one f₀ dt.gateFlagC ∧
        (∀ t' : dt.X.Tag,
          wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)
            (encTagTup dt.ly zero one t') ↔ t' = t) ∧
        ExpExpansion.DomHolds (X := dt.X)
          (t, decRho dt.ly zero one
            (wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)))) := by
  refine (ctlBit_gateFlagC_ixGate_exit hinj helt hzo f₀).trans
    (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine (foldFrom_top (j₀ := 0)
    ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
      fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
    (fun i _ a => le_topTup i a) (Nat.le_refl 0)).trans ?_
  exact (dt.domHolds_iff_altQuantFrom_domLeaf_pad t
    (decRho dt.ly zero one
      (wmBlk (ixAddr elt st.mir) (DrawTag.arg (toLex b) : DrawTag R P dt.KIx)))
    (hn t) topTup).symm

end GateVerdict

end GateInst

end DrawData

end Draw

end DescriptiveComplexity
