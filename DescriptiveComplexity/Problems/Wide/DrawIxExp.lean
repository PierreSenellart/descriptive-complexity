/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstExp
import DescriptiveComplexity.Problems.Wide.IxAddr

/-!
# The expansion atoms at an arbitrary file

An expansion atom reads a witness cell per position and tag, dispatches on the
decoded tags, and runs the branch's wide element loop, one leaf trip per block
atom. Every one of those trips goes to the cell of an **encoded tuple**
(`DescriptiveComplexity.Draw.encTup`) in an argument block. At the elementwise
file that cell is an element of the universe
(`DescriptiveComplexity.Draw.Data.expTagCell`/`expECell`); at a coarser one it
is a **register**, the one the layout names by the tuple's coordinates
(`DescriptiveComplexity.Draw.Data.ixEncG_iff`), and the encoding's canonical
padding is what makes the two the same cell
(`DescriptiveComplexity.Draw.Data.elt_reg_encCoord`).

This file is that reading: the named registers, the generated families over
them, the guards' arrival and uniqueness, and the atom's run
(`DescriptiveComplexity.Draw.Data.ixExp_run`). As in
`DescriptiveComplexity.Draw.Data.ixStageAtom_reachesIn` the file is carried by
one **coherence** hypothesis – the element a register holds the bit of is the
element its name spells – and everything the semantics says of an elementwise
run then says of this one.
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
variable {I : Type} (F : LaidFile dt A R P I)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

/-! ### The registers an expansion atom's trips go to -/

section Cells

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)

/-- **The register of the `i`-th witness read**: the one the layout names by
the tag's witness tuple in the copy's block. -/
noncomputable def ixExpTagCell (i : Fin (k * Fintype.card dt.X.Tag)) : I :=
  F.toLayout.reg hhas (dt.lvBlk vi (ts (dt.wIx i).1))
    (dt.encCoord zero one (Sum.inl (dt.wIx i).2) (fun _ _ => zero) fun _ : Unit => zero)

variable (hnτ : (dt.relPk e τ).n ≤ dt.eDim)

/-- **The register of the `r`-th leaf read at round `a`**: the one the layout
names by the member tuple the block atom spells. -/
noncomputable def ixExpECell (a : Lex (Fin dt.eDim → A))
    (r : Fin (dt.relNr e τ)) : I :=
  F.toLayout.reg hhas (dt.lvBlk vi (ts (relLeafData e τ r).1.1))
    (dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
      (fun _ => dt.expPayTup zero e τ hnτ a r) fun _ : Unit => zero)

variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))

include helt

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
/-- **The witness register holds the witness cell**: its address is the cell an
elementwise atom reads. -/
theorem elt_ixExpTagCell (i : Fin (k * Fintype.card dt.X.Tag)) :
    elt (dt.ixExpTagCell F hhas one vi ts i) = dt.expTagCell zero one vi ts i :=
  dt.elt_reg_encCoord hhas helt _ _ _ _

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A]
  [L.Structure A] in
/-- **The leaf register holds the leaf cell.** -/
theorem elt_ixExpECell (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.relNr e τ)) :
    elt (dt.ixExpECell F hhas one vi ts e τ (hnτ := hnτ) a r) =
      dt.expECell zero one vi ts e τ hnτ a r :=
  dt.elt_reg_encCoord hhas helt _ _ _ _

end Cells

/-! ### The generated families, over the file's registers -/

section Fams

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I) (τ : Fin k → dt.X.Tag)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable (vAdr : Univ A R P dt.KIx dt.dd → Prop)

/-- **The register behind the `i`-th witness read**, at the file: the copy's
level's register set. -/
noncomputable def ixExpTagSet (i : Fin (k * Fintype.card dt.X.Tag)) : I → Prop :=
  dt.lvSet st vi (ts (dt.wIx i).1)

/-- **The register behind the `r`-th leaf read of branch `τ`**, at the file. -/
noncomputable def ixExpESet (r : Fin (dt.relNr e τ)) : I → Prop :=
  dt.lvSet st vi (ts (relLeafData e τ r).1.1)

/-- **The generated family of branch `τ`'s element loop**, at the file. -/
noncomputable def ixExpFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) : dt.CtlIx → A :=
  elemFam ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
    ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
    ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
    (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
    (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ a j

/-- **The generated witness chain of an expansion atom**, at the file. -/
noncomputable def ixExpTagFam (f₀ : dt.CtlIx → A)
    (i : Fin (k * Fintype.card dt.X.Tag + 1)) : dt.CtlIx → A :=
  tagFam ((dt.expArgs zero one vi ts e av hk hn hrd).setTagFlag)
    (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpTagSet vi ts st)
    (dt.ixExpTagCell F hhas one vi ts) f₀ i

variable {dt F hhas one vi ts e av st τ hk hn hrd vAdr}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The loop element is the round's wide tuple**, at every stage of the
family: the same reading as at the elementwise file, the reads now going to the
registers the layout names. -/
theorem readLvE_ixExpFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) :
    dt.readLvE (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
      ofLex a := by
  classical
  have hchain : ∀ (b : Lex (Fin dt.eDim → A)) (q : dt.CtlIx → A) (n : ℕ),
      dt.readLvE (chainSt
        (fun j' => dt.ixExpESet vi ts e st τ j'
          (dt.ixExpECell F hhas one vi ts e τ (hn τ) b j'))
        (fun j' bb q' =>
          (dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ j' bb q'
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) q n) = dt.readLvE q :=
    fun b q n => readLvE_chainSt _ _
      (fun i bb f => readLvE_exp_setFlag i bb f _) q n
  have hiter : ∀ b : Lex (Fin dt.eDim → A),
      dt.readLvE (elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
        (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ b) = ofLex b := by
    intro b
    induction b using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz, readLvE_exp_init,
        ofLex_eq_botTup_of_bot hz]
    | hstep w z hwz hnb ih =>
      have hz2 : elemIter
          ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
          (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr
          (dt.ixExpESet vi ts e st τ)
          (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ z =
        (dt.expArgs zero one vi ts e av hk hn hrd).advEl τ
          (chainSt
            (fun j' => dt.ixExpESet vi ts e st τ j'
              (dt.ixExpECell F hhas one vi ts e τ (hn τ) w j'))
            (fun j' bb q' =>
              (dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ j' bb q'
                (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
            (elemIter ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
              ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
              ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
              (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr
              (dt.ixExpESet vi ts e st τ)
              (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ w) (dt.relNr e τ))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr) :=
        iterOrd_covers hwz hnb
      rw [hz2, readLvE_exp_adv, hchain, ih,
        ofLex_eq_tupNext_of_covers hwz hnb]
  rw [ixExpFam, elemFam, hchain]
  exact hiter a

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An expansion atom's element loop is blind to the two scratch
registers**, at an arbitrary file: it reads the levels' register sets – the
mirror and VAL – and its background at the working cell alone. -/
theorem ixExpFam_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st') (hreg : ¬∃ u : I, vAdr = F.cell u)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) :
    dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j =
      dt.ixExpFam F hhas one vi ts e av st' τ hk hn hrd vAdr f₀ a j := by
  have hset : dt.ixExpESet vi ts e st τ = dt.ixExpESet vi ts e st' τ := by
    funext r
    simp only [ixExpESet, lvSet, h.2.1, h.2.2.1]
  rw [ixExpFam, ixExpFam, hset]
  exact elemFam_congr_rest (h.ixBack hreg) _ _ _ _

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness chain is blind to the two scratch registers too.** -/
theorem ixExpTagFam_congr_scratch {st' : TapeSt dt A R P I}
    (h : dt.ScratchEq st st') (hreg : ¬∃ u : I, vAdr = F.cell u)
    (f₀ : dt.CtlIx → A) (i : Fin (k * Fintype.card dt.X.Tag + 1)) :
    dt.ixExpTagFam F hhas one vi ts e av st hk hn hrd vAdr f₀ i =
      dt.ixExpTagFam F hhas one vi ts e av st' hk hn hrd vAdr f₀ i := by
  have hset : dt.ixExpTagSet vi ts st = dt.ixExpTagSet vi ts st' := by
    funext i'
    simp only [ixExpTagSet, lvSet, h.2.1, h.2.2.1]
  rw [ixExpTagFam, ixExpTagFam, hset]
  exact tagFam_congr_rest (h.ixBack hreg) _ _ _

end Fams

/-! ### The witness chain's read-back and the branch dispatch -/

section Chain

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable (vAdr : Univ A R P dt.KIx dt.dd → Prop)

variable {dt F hhas one vi ts e av st hk hn hrd vAdr}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness flags read back**: after the chain, the flag of position `ℓ`
and tag `t` holds the digit of the register the witness cell of `(ℓ, t)` is. -/
theorem ctlBit_ixExpTagFam_last (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (ℓ : Fin k) (t : dt.X.Tag) :
    dt.ctlBit one
      (dt.ixExpTagFam F hhas one vi ts e av st hk hn hrd vAdr f₀
        (Fin.last (k * Fintype.card dt.X.Tag))) (dt.tagIx hk ℓ t) ↔
      dt.ixExpTagSet vi ts st (dt.tagIxOf ℓ t)
        (dt.ixExpTagCell F hhas one vi ts (dt.tagIxOf ℓ t)) := by
  classical
  have hinj : ∀ i i' : Fin (k * Fintype.card dt.X.Tag),
      dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 =
        dt.tagIx hk (dt.wIx i').1 (dt.wIx i').2 → i = i' := by
    intro i i' h
    obtain ⟨h1, h2⟩ := tagIx_injective hk h
    exact dt.wIx_injective (Prod.ext h1 h2)
  have hchain := dt.ctlBit_chain_setCtl (zero := zero) hzo
    (fun i => dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) hinj
    (fun i => dt.ixExpTagSet vi ts st i (dt.ixExpTagCell F hhas one vi ts i)) f₀
    (k * Fintype.card dt.X.Tag) (dt.tagIxOf ℓ t) (dt.tagIxOf ℓ t).isLt
  have hslot : dt.tagIx hk (dt.wIx (dt.tagIxOf ℓ t)).1
      (dt.wIx (dt.tagIxOf ℓ t)).2 = dt.tagIx hk ℓ t := by
    rw [dt.wIx_tagIxOf]
  rw [hslot] at hchain
  exact hchain

variable {elt : I → Univ A R P dt.KIx dt.dd}

omit [Fintype dt.SlotIx] in
/-- **The chain decodes the argument points' tags**, at the file: if the
addresses the levels' registers stand for hold the encodings of the points, the
flags are one-hot at the points' tag tuple, which is the branch dispatch's
guard. -/
theorem tagsAre_ixExpTagFam (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hinj : Function.Injective elt)
    (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    (dt.expArgs zero one vi ts e av hk hn hrd).TagsAre
      (fun ℓ => (pts ℓ).1.1)
      (dt.ixExpTagFam F hhas one vi ts e av st hk hn hrd vAdr f₀
        (Fin.last (k * Fintype.card dt.X.Tag))) := by
  intro ℓ t
  rw [ctlBit_ixExpTagFam_last hzo f₀ ℓ t]
  have hcell : dt.ixExpTagSet vi ts st (dt.tagIxOf ℓ t)
      (dt.ixExpTagCell F hhas one vi ts (dt.tagIxOf ℓ t)) ↔ (pts ℓ).1.1 = t := by
    rw [ixExpTagSet, dt.wIx_tagIxOf]
    rw [← ixAddr_elt hinj (dt.lvSet st vi (ts ℓ))
      (dt.ixExpTagCell F hhas one vi ts (dt.tagIxOf ℓ t))]
    rw [dt.elt_ixExpTagCell F hhas one vi ts helt (dt.tagIxOf ℓ t), expTagCell,
      dt.wIx_tagIxOf]
    exact (regBit_wmSeg hlin _ _).symm.trans
      (dt.blk_encTagTup_iff hzo hlin (hENC ℓ) t)
  rw [hcell]
  exact eq_comm

end Chain

/-! ### The leaf guards, at the generated states -/

section Leaves

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I) (τ : Fin k → dt.X.Tag)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable (vAdr : Univ A R P dt.KIx dt.dd → Prop)

variable {dt F hhas one vi ts e av st τ hk hn hrd vAdr}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The payload a leaf read spells at a generated state** is the round's
tuple's, so the guard's computed coordinates name the round's register. -/
theorem expPay_ixExpFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ)) :
    dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn τ)
      (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
      dt.expPayTup zero e τ (hn τ) a r := by
  refine congrArg (pad zero) (funext fun q => ?_)
  exact congrFun (readLvE_ixExpFam f₀ a j) _

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A leaf read's guard holds at its register**: the computed coordinates are
the round's payload, so the trip stops at the register the layout names by the
member tuple. -/
theorem ixExpMatch_ixExpFam (hzo : zero ≠ one) (hix : IsLinOrd F.le)
    (hsep : F.toLayout.NameSep zero dt.dd0Le)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ)) :
    dt.expMatch zero one vi ts e τ r (hn τ)
      (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j)
      (dt.ixBack F.toLayout zero one dt.dd0Le st
        (F.cell (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r))) := by
  refine (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsep hhas _ _ _ _ _).mpr ?_
  have hcoord : dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
      (dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn τ))
      (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
    dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
      (fun _ => dt.expPayTup zero e τ (hn τ) a r) (fun _ : Unit => zero) := by
    funext c
    simp only [encCoord]
    rw [expPay_ixExpFam f₀ a j r]
  rw [ixExpECell, hcoord]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A leaf read's guard identifies its register.** -/
theorem ixExpMatch_ixExpFam_uniq (hzo : zero ≠ one) (hix : IsLinOrd F.le)
    (hsep : F.toLayout.NameSep zero dt.dd0Le)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ))
    {y : Univ A R P dt.KIx dt.dd → Prop}
    (hM : dt.expMatch zero one vi ts e τ r (hn τ)
      (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j)
      (dt.ixBack F.toLayout zero one dt.dd0Le st y)) :
    y = F.cell (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r) := by
  by_cases hreg : ∃ u : I, y = F.cell u
  · obtain ⟨u, rfl⟩ := hreg
    have hu := (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsep hhas _ _ _ _ u).mp hM
    have hcoord : dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
        (dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn τ))
        (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
      dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
        (fun _ => dt.expPayTup zero e τ (hn τ) a r) (fun _ : Unit => zero) := by
      funext c
      simp only [encCoord]
      rw [expPay_ixExpFam f₀ a j r]
    rw [hu, ixExpECell, hcoord]
  · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
      (fun u hc => hreg ⟨u, hc⟩))

variable {elt : I → Univ A R P dt.KIx dt.dd}

omit [Fintype dt.SlotIx] [Nonempty A] in
/-- **What a leaf trip's digit means**, at the file: at a round's register, the
bit is the block atom's value at the points the addresses encode, read at the
valuation the round's tuple spells. -/
theorem ixExpESet_ixExpECell_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hinj : Function.Injective elt)
    (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.relNr e τ))
    {f : dt.CtlIx → A} (hf : dt.readLvE f = ofLex a) :
    dt.ixExpESet vi ts e st τ r
        (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r) ↔
      BlkAtom.holds (L := L) (B := dt.X.B.replicate k)
        (dt.X.B.replicateAssign fun ℓ => (pts ℓ).1.2)
        (fun j => f (dt.lvE (Fin.castLE (hn τ) j)))
        (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2) := by
  have hpay : dt.expPay (zero := zero) (e := e) (τ := τ) (r := r)
      (hn := hn τ) f = dt.expPayTup zero e τ (hn τ) a r :=
    congrArg (pad zero) (funext fun q => congrFun hf _)
  have h := dt.regBit_expMatch (zero := zero) hzo hlin ts e τ r (hn τ) pts
    (m := ixAddr elt (dt.ixExpESet vi ts e st τ r))
    (hENC (relLeafData e τ r).1.1) f
  rw [hpay] at h
  rw [← ixAddr_elt hinj (dt.ixExpESet vi ts e st τ r)
    (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r),
    dt.elt_ixExpECell F hhas one vi ts e τ (hn τ) helt a r, expECell]
  exact (regBit_wmSeg hlin _ _).symm.trans h

end Leaves

/-! ### The expansion atom's machine run -/

section ExpRun

variable (hhasP : F.toLayout.HasName PR.zero)
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable {emb : TagPh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
  (dt.relNr e) → P}
variable {exitPh : P}
variable {rEmb : ∀ i : TagSite (k * Fintype.card dt.X.Tag)
    (Fin k → dt.X.Tag) (dt.relNr e),
  TagSh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag) (dt.relNr e) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : TagSite (k * Fintype.card dt.X.Tag)
      (Fin k → dt.X.Tag) (dt.relNr e))
    (ρ : TagSh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
      (dt.relNr e) i),
  PR.rules (rEmb i ρ) = tagRule PR.one Slot.wk Slot.reg emb
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).MatchT)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).TagsAre)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).MatchE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt)
    ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).IsMaxEl)
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
variable (pts : Fin k → dt.X.Map A)
variable (hENC : ∀ ℓ : Fin k,
  wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
    (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
    encMap dt.ly PR.zero PR.one (pts ℓ))
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hix hsepP hbot hv hvi hwkSt hm₀ hwkt₀ hrgt₀ hinj helt hENC in
/-- **The expansion atom's machine run at an arbitrary file, on a clock**: from
the machinery's first phase at the marker – the witness chain decoding the
argument points' tags, the dispatch onto their branch, and that branch's wide
element loop, one leaf trip per block atom – to the exit phase one cell to the
marker's right. Every trip goes to a register the layout names, and the cost is
the chain's reads and the branch's whole loop. -/
theorem ixExp_reachesIn (w : ℕ)
    (hcostT : ∀ i : Fin (k * Fintype.card dt.X.Tag),
      2 * (wideRank (F.cell (dt.ixExpTagCell F hhasP PR.one vi ts i)) -
        wideRank v) + 2 ≤ w)
    (hcostE : ∀ (a : Lex (Fin dt.eDim → A))
        (r : Fin (dt.relNr e (fun ℓ => (pts ℓ).1.1))),
      2 * (wideRank (F.cell (dt.ixExpECell F hhasP PR.one vi ts e
        (fun ℓ => (pts ℓ).1.1) (hn (fun ℓ => (pts ℓ).1.1)) a r)) - wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      ((w + 2) * (k * Fintype.card dt.X.Tag) + 2 +
        ((2 + (w + 2) * dt.relNr e (fun ℓ => (pts ℓ).1.1)) *
          (Nat.card (Lex (Fin dt.eDim → A)) + 1) + 1))
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell t₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt
            (fun ℓ => (pts ℓ).1.1)
            (dt.ixExpFam F hhasP PR.one vi ts e av st (fun ℓ => (pts ℓ).1.1)
              hk hn hrd v
              (dt.ixExpTagFam F hhasP PR.one vi ts e av st hk hn hrd v f₀
                (Fin.last (k * Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  refine tag_reachesIn_iter F.toIxFile hrules hR hlin hix hbot hv hvi
    (fun r => by
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun r => rfl)
    (mT := dt.ixExpTagSet vi ts st)
    (fun i r => dt.back_lvTrack F PR.zero PR.one st vi (ts (dt.wIx i).1) r)
    (fun i => dt.wk_ne_lvTrack vi (ts (dt.wIx i).1))
    (fun i => dt.reg_ne_lvTrack vi (ts (dt.wIx i).1))
    hm₀ hwkt₀ hrgt₀
    (xT := dt.ixExpTagCell F hhasP PR.one vi ts) (f₀ := f₀)
    ?_ ?_
    (τ := fun ℓ => (pts ℓ).1.1)
    (tagsAre_ixExpTagFam hzo hlin hinj helt pts hENC f₀)
    (mE := dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1))
    (fun j r => dt.back_lvTrack F PR.zero PR.one st vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r)
    (fun j => dt.wk_ne_lvTrack vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1))
    (fun j => dt.reg_ne_lvTrack vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1))
    (a₀ := toLex botTup) (aT := toLex topTup)
    (fun a => tup_isBot_iff.mpr (fun p b => botTup_le p b) a)
    (fun a => tup_isTop_iff.mpr (fun p b => le_topTup p b) a)
    (xE := dt.ixExpECell F hhasP PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
      (hn (fun ℓ => (pts ℓ).1.1)))
    ?_ ?_ ?_ ?_ w hcostT hcostE
  · -- the witness guards hold at their cells
    intro i
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT i)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := dt.ixExpTagSet vi ts st i)
      F.toIxFile (fun r => dt.back_lvTrack F PR.zero PR.one st vi (ts (dt.wIx i).1) r) _]
    exact (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ _ _ _ _).mpr rfl
  · -- the witness guards identify their cells
    intro i r hM
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT i)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := dt.ixExpTagSet vi ts st i)
      F.toIxFile (fun r' => dt.back_lvTrack F PR.zero PR.one st vi (ts (dt.wIx i).1) r') _]
      at hM
    by_cases hreg : ∃ u : I, r = F.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.ixEncG_iff hzo (F.toIxFile.injective hix) hsepP hhasP _ _ _ _ u).mp hM
      rw [hu]
      rfl
    · exact absurd hM (dt.ixNot_nameGF_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the leaf guards hold at their cells
    intro a j
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE
        (fun ℓ => (pts ℓ).1.1) j)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1) j)
      F.toIxFile (fun r => dt.back_lvTrack F PR.zero PR.one st vi
        (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r) _]
    exact ixExpMatch_ixExpFam hzo hix hsepP _ a j.castSucc j
  · -- the leaf guards identify their cells
    intro a j r hM
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE
        (fun ℓ => (pts ℓ).1.1) j)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
      (m := dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1) j)
      F.toIxFile (fun r' => dt.back_lvTrack F PR.zero PR.one st vi
        (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r') _] at hM
    exact ixExpMatch_ixExpFam_uniq hzo hix hsepP _ a j.castSucc j hM
  · -- exhausted at the top
    change dt.IsMaxLvE _
    change IsMaxTup (dt.readLvE _)
    rw [show dt.readLvE (elemFam
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl
          (fun ℓ => (pts ℓ).1.1))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v
        (dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.ixExpECell F hhasP PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (dt.ixExpTagSet vi ts st)
          (dt.ixExpTagCell F hhasP PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        (toLex topTup)
        (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1)))) =
      ofLex (toLex topTup) from readLvE_ixExpFam _ _ _]
    exact isMaxTup_topTup
  · -- not exhausted below the top
    intro a ha hc
    have hc2 : IsMaxTup (dt.readLvE (elemFam
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl
          (fun ℓ => (pts ℓ).1.1))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v
        (dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.ixExpECell F hhasP PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (dt.ixExpTagSet vi ts st)
          (dt.ixExpTagCell F hhasP PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        a (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))) := hc
    rw [show dt.readLvE (elemFam
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl
          (fun ℓ => (pts ℓ).1.1))
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v
        (dt.ixExpESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.ixExpECell F hhasP PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) v (dt.ixExpTagSet vi ts st)
          (dt.ixExpTagCell F hhasP PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        a (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1)))) =
      ofLex a from readLvE_ixExpFam _ _ _] at hc2
    exact absurd (tup_isTop_iff.mpr hc2 (toLex topTup)) (not_le_of_gt ha)


end ExpRun

/-! ### The sub-fold: the sac invariant and the exit verdict -/

section ExpVerdict

variable {zero : A} (hhas : F.toLayout.HasName zero) (one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P I) (τ : Fin k → dt.X.Tag)
variable (hnτ : (dt.relPk e τ).n ≤ dt.eDim)
variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))

/-- **The branch's leaf, over the wide valuation**: the defining sentence's
matrix at the points' assignments, its levels read off the first `n`
coordinates of the wide tuple. -/
noncomputable def ixExpLeafP (pts : Fin k → dt.X.Map A)
    (v : Fin dt.eDim → A) : Prop :=
  dt.expLeaf e τ (fun ℓ => (pts ℓ).1.2) fun j => v (Fin.castLE hnτ j)



omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The leaf-read flags read back**: at a round's end, the flag of the
`r`-th block atom holds the digit of the round's cell. -/
theorem ctlBit_rdf_ixExpFam (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.relNr e τ)) :
    dt.ctlBit one
        (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a
          (Fin.last (dt.relNr e τ)))
        (dt.rdfC (Fin.castLE (hrd τ) r)) ↔
      dt.ixExpESet vi ts e st τ r
        (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r) := by
  have hinj : ∀ r₁ r₂ : Fin (dt.relNr e τ),
      dt.rdfC (Fin.castLE (hrd τ) r₁) = dt.rdfC (Fin.castLE (hrd τ) r₂) →
        r₁ = r₂ := fun r₁ r₂ h =>
    Fin.castLE_injective _ (dt.rdfC_injective h)
  exact dt.ctlBit_chain_setCtl hzo
    (fun r' => dt.rdfC (Fin.castLE (hrd τ) r')) hinj
    (fun r' => dt.ixExpESet vi ts e st τ r'
      (dt.ixExpECell F hhas one vi ts e τ (hn τ) a r'))
    (elemIter ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
      (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
      (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ a)
    (dt.relNr e τ) r r.isLt

omit [Fintype dt.SlotIx] in
include hinj helt in
/-- **The leaf flag's value at a round's end is the branch's leaf**: with
the flags holding the block atoms' bits and the loop element the round's
tuple, the Boolean function the control computes is the leaf predicate at
that tuple. -/
theorem expLeafVal_ixExpFam (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) :
    dt.expLeafVal one e τ (hn τ) (hrd τ)
        (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a
          (Fin.last (dt.relNr e τ))) ↔
      dt.ixExpLeafP e τ (hn τ) pts (ofLex a) := by
  have hval := dt.expLeafVal_iff (one := one) e τ (hn τ) (hrd τ)
    (fun ℓ => (pts ℓ).1.2)
    (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ a
      (Fin.last (dt.relNr e τ)))
    (fun r => (ctlBit_rdf_ixExpFam (dt := dt) (F := F) (hhas := hhas) (one := one)
        (vi := vi) (ts := ts) (e := e) (av := av) (st := st) (τ := τ) (hk := hk)
        (hn := hn) (hrd := hrd) (hzo := hzo) (f₀ := f₀) (a := a) (r := r)).trans
      (ixExpESet_ixExpECell_iff (F := F) (hhas := hhas) (hinj := hinj) (helt := helt)
          (hzo := hzo) (hlin := hlin) (pts := pts) (hENC := hENC) (a := a) (r := r)
        (readLvE_ixExpFam f₀ a (Fin.last (dt.relNr e τ)))))
  refine hval.trans ?_
  rw [ixExpLeafP]
  refine iff_of_eq (congrArg _ (funext fun j => ?_))
  exact congrFun (readLvE_ixExpFam f₀ a (Fin.last (dt.relNr e τ))) _

include hinj helt in
omit [Fintype dt.SlotIx] in
/-- **The sub-fold's accumulators fold the strict prefix**: at every round's
entry, the `sac` slots hold the completed-subtree contributions of the
branch's prefix at the round's tuple. -/
theorem readSac_ixExpIter (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) (j : ℕ)
    (hj : j < dt.eDim) :
    dt.readSac one (elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
        (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ a) j ↔
      accCVal (dt.relPk e τ).pol (dt.ixExpLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) j (ofLex a) := by
  classical
  induction a using order_induction generalizing j with
  | hmin z hz =>
    rw [elemIter, iterOrd_bot hz]
    have hread : dt.readSac one
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ f₀
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) j ↔
        ((dt.relPk e τ).pol j = false) := by
      change dt.readSac one (dt.expInit zero one e τ f₀) j ↔ _
      rw [expInit, initSac]
      exact readSac_putSac hzo _ _ hj
    rw [hread, ofLex_eq_botTup_of_bot hz]
    exact (accCVal_bot (fun i b => botTup_le i b) j).symm
  | hstep w z hwz hnb ih =>
    -- the step's carry, off the covered tuple
    have hnm : ¬IsMaxTup (ofLex w) := by
      intro hc
      exact absurd (tup_isTop_iff.mpr hc z) (not_le_of_gt hwz)
    obtain ⟨pc, hpc, hAt⟩ := tupSuccAt_tupCarry (t := ofLex w) hnm
    have hzw : ofLex z = tupNext (ofLex w) := ofLex_eq_tupNext_of_covers hwz hnb
    rw [← hzw] at hAt
    -- the post-chain state of round `w`, and its readings
    set Fc := elemFam ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
      (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
      (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ w
      (Fin.last (dt.relNr e τ)) with hF
    have hreadF : ∀ j' : ℕ, dt.readSac one Fc j' ↔
        dt.readSac one (elemIter
          ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
          (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
          (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ w) j' := by
      intro j'
      rw [hF]
      exact readSac_chainSt _ _
        (fun i bb f j'' => readSac_exp_setFlag i bb f _ j'') _ _ j'
    have hlvF : dt.readLvE Fc = ofLex w :=
      readLvE_ixExpFam f₀ w (Fin.last (dt.relNr e τ))
    -- one round of the machine's fold
    have hstepEq : elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.ixBack F.toLayout zero one dt.dd0Le st) vAdr (dt.ixExpESet vi ts e st τ)
        (dt.ixExpECell F hhas one vi ts e τ (hn τ)) f₀ z =
        (dt.expArgs zero one vi ts e av hk hn hrd).advEl τ Fc
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr) := by
      rw [elemIter, iterOrd_covers hwz hnb]
      rfl
    rw [hstepEq]
    -- the advance, unfolded to the carry write
    have hadv : ∀ j' : ℕ, j' < dt.eDim →
        (dt.readSac one
          ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ Fc
            (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr)) j' ↔
        dt.readSac one
          (dt.carrySac zero one (dt.relPk e τ).pol (tupCarry (dt.readLvE Fc))
            (dt.setSubLeaf zero one
              (dt.expLeafVal one e τ (hn τ) (hrd τ) Fc) Fc)) j') := by
      intro j' hj'
      change dt.readSac one (dt.expAdv zero one e τ (hn τ) (hrd τ) Fc) j' ↔ _
      rw [expAdv]
      exact readSac_advLvE _ j'
    -- close by the vector's step rule
    rw [hadv j hj, hlvF]
    refine accCVal_step (le := (· ≤ · : A → A → Prop)) (v := ofLex w)
      ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
        fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
      (hc := hpc ▸ pc.isLt) ?_ ?_ ?_ ?_
      (acc := dt.readSac one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ) Fc) Fc))
      (leaf := dt.ctlBit one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ) Fc) Fc) dt.subLeafC)
      ?_ ?_ ?_ j hj
    · -- coordinates below the carry agree
      intro i hi
      have hlt : (i : ℕ) < (pc : ℕ) := by omega
      exact hAt.1 i (Fin.lt_def.mpr hlt)
    · -- coordinates above the carry are maximal before the step
      intro i hi b
      have hlt : (pc : ℕ) < (i : ℕ) := by omega
      exact (hAt.2.2 i (Fin.lt_def.mpr hlt)).1 b
    · -- and minimal after it
      intro i hi b
      have hlt : (pc : ℕ) < (i : ℕ) := by omega
      exact (hAt.2.2 i (Fin.lt_def.mpr hlt)).2 b
    · -- the carry coordinate steps
      intro b
      constructor
      · rintro ⟨hle, hnle⟩
        by_contra hbw
        have hwb : ofLex w ⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ < b :=
          lt_of_not_ge (by
            intro hc
            exact hbw (by
              have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim)
                  = pc := Fin.ext hpc.symm
              rw [hpcc] at hc ⊢
              exact hc))
        have hblt : b < ofLex z ⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ :=
          lt_of_le_not_ge hle hnle
        have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim) = pc :=
          Fin.ext hpc.symm
        rw [hpcc] at hwb hblt
        exact hAt.2.1.2 b ⟨hwb, hblt⟩
      · intro hle
        have hpcc : (⟨tupCarry (ofLex w), hpc ▸ pc.isLt⟩ : Fin dt.eDim) = pc :=
          Fin.ext hpc.symm
        rw [hpcc]
        rw [hpcc] at hle
        have hblt : b < ofLex z pc := lt_of_le_of_lt hle hAt.2.1.1
        exact ⟨le_of_lt hblt, not_le_of_gt hblt⟩
    · -- the old accumulators are the contributions at the old tuple
      intro i hi
      rw [readSac_setSubLeaf, hreadF i]
      exact ih i hi
    · -- the old leaf flag is the leaf at the old tuple
      rw [ctlBit_setSubLeaf hzo]
      exact expLeafVal_ixExpFam (dt := dt) (F := F) (hhas := hhas) (one := one) (vi := vi)
        (ts := ts) (e := e) (av := av) (st := st) (τ := τ) (hk := hk) (hn := hn)
        (hrd := hrd) (hinj := hinj) (helt := helt) (hzo := hzo) (hlin := hlin)
        (pts := pts) (hENC := hENC) (f₀ := f₀) (a := w)
    · -- the new readings are the carry write's
      intro i hi
      exact readSac_carrySac hzo (dt.relPk e τ).pol (tupCarry (ofLex w))
        (dt.setSubLeaf zero one
          (dt.expLeafVal one e τ (hn τ) (hrd τ) Fc) Fc) (j := i) hi

include hinj helt in
omit [Fintype dt.SlotIx] in
/-- **The verdict the exit control carries**: the atom's slot holds the fold
of the branch's whole prefix at the points' assignments – the value
`DescriptiveComplexity.Draw.Data.expLeaf`'s prefix takes over every wide
tuple, which `DescriptiveComplexity.Problems.Wide.DrawExp` reads as the
expansion atom's truth. -/
theorem ctlBit_avC_ixExp_exit (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.expArgs zero one vi ts e av hk hn hrd).exitSt τ
          (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀
            (toLex topTup) (Fin.last (dt.relNr e τ)))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
        (dt.avC av) ↔
      foldFrom (dt.relPk e τ).pol (dt.ixExpLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) 0 topTup := by
  classical
  change dt.ctlBit one (dt.expExit zero one e τ (hn τ) (hrd τ) av
    (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀ (toLex topTup)
      (Fin.last (dt.relNr e τ)))) (dt.avC av) ↔ _
  rw [expExit, ctlBit_setCtl_self hzo]
  have hacc : ∀ j : ℕ, j < dt.eDim →
      (dt.readSac one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ)
          (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀
            (toLex topTup) (Fin.last (dt.relNr e τ))))
        (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀
          (toLex topTup) (Fin.last (dt.relNr e τ)))) j ↔
      accCVal (dt.relPk e τ).pol (dt.ixExpLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) j (ofLex (toLex topTup))) := by
    intro j hj
    rw [readSac_setSubLeaf]
    refine Iff.trans ?_ (readSac_ixExpIter (dt := dt) (F := F) (hhas := hhas)
      (one := one) (vi := vi) (ts := ts) (e := e) (av := av) (st := st) (τ := τ)
      (hk := hk) (hn := hn) (hrd := hrd) (vAdr := vAdr) (hinj := hinj)
      (helt := helt) (hzo := hzo) (hlin := hlin) (pts := pts) (hENC := hENC)
      (f₀ := f₀) (a := toLex topTup) j hj)
    rw [ixExpFam, elemFam]
    exact readSac_chainSt _ _
      (fun i bb f j'' => readSac_exp_setFlag i bb f _ j'') _ _ j
  have hleaf : dt.ctlBit one (dt.setSubLeaf zero one
      (dt.expLeafVal one e τ (hn τ) (hrd τ)
        (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀
          (toLex topTup) (Fin.last (dt.relNr e τ))))
      (dt.ixExpFam F hhas one vi ts e av st τ hk hn hrd vAdr f₀
        (toLex topTup) (Fin.last (dt.relNr e τ)))) dt.subLeafC ↔
      dt.ixExpLeafP e τ (hn τ) pts (ofLex (toLex topTup)) := by
    rw [ctlBit_setSubLeaf hzo]
    exact expLeafVal_ixExpFam (dt := dt) (F := F) (hhas := hhas) (one := one) (vi := vi)
      (ts := ts) (e := e) (av := av) (st := st) (τ := τ) (hk := hk) (hn := hn)
      (hrd := hrd) (hinj := hinj) (helt := helt) (hzo := hzo) (hlin := hlin)
      (pts := pts) (hENC := hENC) (f₀ := f₀) (a := toLex topTup)
  exact sacVerdict_iff_foldFrom hacc hleaf

include hinj helt in
omit [Fintype dt.SlotIx] in
/-- **The expansion atom's verdict is its truth**: at the argument points
the registers encode, the bit the exit control files in the atom's slot is
`RelMap` of the expansion – the machine has evaluated the defining
sentence. -/
theorem ctlBit_avC_ixExp_relMap (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (ixAddr elt (dt.lvSet st vi (ts ℓ)))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.expArgs zero one vi ts e av hk hn hrd).exitSt
          (fun ℓ => (pts ℓ).1.1)
          (dt.ixExpFam F hhas one vi ts e av st (fun ℓ => (pts ℓ).1.1) hk hn hrd
            vAdr f₀ (toLex topTup)
            (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
          (dt.ixBack F.toLayout zero one dt.dd0Le st vAdr))
        (dt.avC av) ↔
      RelMap (M := dt.X.Map A) e pts := by
  refine (ctlBit_avC_ixExp_exit (dt := dt) (F := F) (hhas := hhas) (one := one)
    (vi := vi) (ts := ts) (e := e) (av := av) (st := st)
    (τ := fun ℓ => (pts ℓ).1.1) (hk := hk) (hn := hn) (hrd := hrd) (vAdr := vAdr)
    (hinj := hinj) (helt := helt) (hzo := hzo) (hlin := hlin) (pts := pts)
    (hENC := hENC) (f₀ := f₀)).trans ?_
  refine (foldFrom_top (j₀ := 0)
    ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
      fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
    (fun i _ a => le_topTup i a) (Nat.le_refl 0)).trans ?_
  exact (dt.relMap_iff_altQuantFrom_expLeaf_pad e pts
    (hn (fun ℓ => (pts ℓ).1.1)) topTup).symm

end ExpVerdict



end Data

end Draw

end DescriptiveComplexity
