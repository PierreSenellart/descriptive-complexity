/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstStage

/-!
# The expansion atoms, instantiated: the tag-branched wide loop

The third semantic instantiation: an expansion atom's machinery at the pack
`DescriptiveComplexity.Draw.Data.expArgs`. The witness chain reads each
argument point's tag off its witness cell, the branch dispatches on the
one-hot decoding, and the branch's element loop enumerates the **wide**
tuples – the whole prefix of the defining sentence – one leaf-read trip per
block atom, the sub-fold riding in the `sac` slots.

This file builds the generated families and their invariants:

* `DescriptiveComplexity.Draw.Data.expTagCell`/`expECell` – the cells the
  trips go to: the tag-witness tuples and the member tuples of the copies'
  points, at the payload the round's wide tuple spells;
* `DescriptiveComplexity.Draw.Data.readLvE_expFam` – the loop element is
  the round's wide tuple at every stage of the family;
* the chain read-backs: the witness flags decode the points' tags, the
  leaf-read flags hold the block atoms' bits.
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
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree, and that is the bridge every statement
-- about the elementwise layout crosses.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

/-! ### The wide loop element through the machinery's operations -/

section Riding

variable {dt}
variable {zero one : A}

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The wide loop element rides along a control-bit store off it. -/
theorem readLvE_setCtl {q : dt.CtlIx} (hq : ∀ j : Fin dt.eDim, dt.lvE j ≠ q)
    (b : Prop) (f : dt.CtlIx → A) :
    dt.readLvE (dt.setCtl zero one q b f) = dt.readLvE f := by
  funext j
  rw [readLvE, readLvE, setCtl_of_ne (hq j)]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The wide loop element rides along a sub-fold accumulator write. -/
theorem readLvE_putSac (f : dt.CtlIx → A) (b : Fin dt.eDim → Prop) :
    dt.readLvE (dt.putSac zero one f b) = dt.readLvE f := by
  funext j
  rw [readLvE, readLvE, putSac_of_lvE]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The wide loop element after an advance is the next tuple. -/
theorem readLvE_advLvE (f : dt.CtlIx → A) :
    dt.readLvE (dt.advLvE f) = tupNext (dt.readLvE f) :=
  readLvE_putLvE f _

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A within-round chain preserving the loop element preserves it end to
end** – the generic riding lemma every stored-read chain uses. -/
theorem readLvE_chainSt {nr : ℕ} (bit : Fin nr → Prop)
    (upd : Fin nr → Bool → (dt.CtlIx → A) → dt.CtlIx → A)
    (hupd : ∀ (i : Fin nr) (b : Bool) (f : dt.CtlIx → A),
      dt.readLvE (upd i b f) = dt.readLvE f)
    (base : dt.CtlIx → A) (n : ℕ) :
    dt.readLvE (chainSt bit upd base n) = dt.readLvE base := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < nr
    · by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb, hupd, ih]
      · rw [chainSt_succ_neg h hb, hupd, ih]
    · have hskip : chainSt bit upd base (n + 1) = chainSt bit upd base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip, ih]

end Riding

/-! ### The cells and registers of an expansion atom -/

section ExpInst

variable (zero one : A)
variable (vi : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf vi))
variable (e : dt.X.E.Relations k) (av : Fin dt.natMax)
variable (st : TapeStD dt A R P) (τ : Fin k → dt.X.Tag)

/-- **The register behind the `i`-th witness read**: the copy's level's
register. -/
noncomputable def expTagSet (i : Fin (k * Fintype.card dt.X.Tag)) :
    Univ A R P dt.KIx dt.dd → Prop :=
  dt.lvSet st vi (ts (dt.wIx i).1)

/-- **The cell of the `i`-th witness read**: the tag's witness tuple in the
copy's block. -/
noncomputable def expTagCell (i : Fin (k * Fintype.card dt.X.Tag)) :
    Univ A R P dt.KIx dt.dd :=
  dt.blkElt (dt.lvBlk vi (ts (dt.wIx i).1))
    (encTup dt.ly zero one (Sum.inl (dt.wIx i).2) fun _ => zero)

/-- **The register behind the `r`-th leaf read of branch `τ`**. -/
noncomputable def expESet (r : Fin (dt.relNr e τ)) :
    Univ A R P dt.KIx dt.dd → Prop :=
  dt.lvSet st vi (ts (relLeafData e τ r).1.1)

variable (hnτ : (dt.relPk e τ).n ≤ dt.eDim)

/-- **The payload the `r`-th leaf spells at round `a`**: the block atom's
levels read out of the round's wide tuple. -/
noncomputable def expPayTup (a : Lex (Fin dt.eDim → A))
    (r : Fin (dt.relNr e τ)) : Fin (blockArityBound dt.X.B) → A :=
  pad zero fun q => ofLex a (Fin.castLE hnτ ((relLeafData e τ r).2 q))

/-- **The cell of the `r`-th leaf read at round `a`**: the member tuple the
block atom names, in the copy's block. -/
noncomputable def expECell (a : Lex (Fin dt.eDim → A))
    (r : Fin (dt.relNr e τ)) : Univ A R P dt.KIx dt.dd :=
  dt.blkElt (dt.lvBlk vi (ts (relLeafData e τ r).1.1))
    (encTup dt.ly zero one (Sum.inr (relLeafData e τ r).1.2)
      (dt.expPayTup zero e τ hnτ a r))

variable (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hn : ∀ τ' : Fin k → dt.X.Tag, (dt.relPk e τ').n ≤ dt.eDim)
variable (hrd : ∀ τ' : Fin k → dt.X.Tag, dt.relNr e τ' ≤ dt.nfDim)
variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}

variable (vAdr) in
/-- **The generated family of branch `τ`'s element loop**, at the pack. -/
noncomputable def expFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) : dt.CtlIx → A :=
  elemFam ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
    ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
    ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
    (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
    (dt.expECell zero one vi ts e τ (hn τ)) f₀ a j

variable {dt zero one vi ts e av st τ hnτ hk hn hrd}

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- A leaf-read store preserves the wide loop element. -/
theorem readLvE_exp_setFlag (r : Fin (dt.relNr e τ)) (bb : Bool)
    (q : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.readLvE ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ r bb q g) =
      dt.readLvE q := by
  change dt.readLvE (dt.setCtl zero one (dt.rdfC (Fin.castLE (hrd τ) r))
    (bb = true) q) = _
  have hne : ∀ j : Fin dt.eDim,
      dt.lvE j ≠ dt.rdfC (Fin.castLE (hrd τ) r) := fun j h => nomatch h
  exact readLvE_setCtl hne _ q

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- The branch's loop starts at the least wide tuple. -/
theorem readLvE_exp_init (q : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.readLvE ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ q g) =
      botTup := by
  change dt.readLvE (dt.expInit zero one e τ q) = _
  rw [expInit, initSac, readLvE_putSac, readLvE_initLvE]

omit [Fintype dt.SlotIx] in
/-- A round's fold-and-advance steps the wide tuple. -/
theorem readLvE_exp_adv (q : dt.CtlIx → A) (g : dt.SlotIx → A) :
    dt.readLvE ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ q g) =
      tupNext (dt.readLvE q) := by
  change dt.readLvE (dt.expAdv zero one e τ (hn τ) (hrd τ) q) = _
  have hne : ∀ j : Fin dt.eDim, dt.lvE j ≠ dt.subLeafC := fun j h => nomatch h
  rw [expAdv, readLvE_advLvE, carrySac, readLvE_putSac, setSubLeaf,
    readLvE_setCtl hne]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The loop element is the round's wide tuple**, at every stage of the
family. -/
theorem readLvE_expFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) :
    dt.readLvE (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
      ofLex a := by
  classical
  have hchain : ∀ (b : Lex (Fin dt.eDim → A)) (q : dt.CtlIx → A) (n : ℕ),
      dt.readLvE (chainSt
        (fun j' => dt.expESet vi ts e st τ j'
          (dt.expECell zero one vi ts e τ (hn τ) b j'))
        (fun j' bb q' =>
          (dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ j' bb q'
            (dt.back RF.cell zero one dt.dd0Le st vAdr)) q n) = dt.readLvE q :=
    fun b q n => readLvE_chainSt _ _
      (fun i bb f => readLvE_exp_setFlag i bb f _) q n
  have hiter : ∀ b : Lex (Fin dt.eDim → A),
      dt.readLvE (elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
        (dt.expECell zero one vi ts e τ (hn τ)) f₀ b) = ofLex b := by
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
          (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
          (dt.expECell zero one vi ts e τ (hn τ)) f₀ z =
        (dt.expArgs zero one vi ts e av hk hn hrd).advEl τ
          (chainSt
            (fun j' => dt.expESet vi ts e st τ j'
              (dt.expECell zero one vi ts e τ (hn τ) w j'))
            (fun j' bb q' =>
              (dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ j' bb q'
                (dt.back RF.cell zero one dt.dd0Le st vAdr))
            (elemIter ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
              ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
              ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
              (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
              (dt.expECell zero one vi ts e τ (hn τ)) f₀ w) (dt.relNr e τ))
          (dt.back RF.cell zero one dt.dd0Le st vAdr) :=
        iterOrd_covers hwz hnb
      rw [hz2, readLvE_exp_adv, hchain, ih,
        ofLex_eq_tupNext_of_covers hwz hnb]
  rw [expFam, elemFam, hchain]
  exact hiter a

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An expansion atom's element loop is blind to the two scratch
registers**: it reads the levels' register sets – the mirror and VAL – and
its background at the working cell alone. -/
theorem expFam_congr_scratch {st' : TapeStD dt A R P}
    (h : dt.ScratchEq st st')
    (hreg : ¬∃ u : Univ A R P dt.KIx dt.dd, vAdr = RF.cell u)
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) :
    dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a j =
      dt.expFam RF zero one vi ts e av st' τ hk hn hrd vAdr f₀ a j := by
  have hset : dt.expESet vi ts e st τ = dt.expESet vi ts e st' τ := by
    funext r
    simp only [expESet, lvSet, h.2.1, h.2.2.1]
  rw [expFam, expFam, hset]
  exact elemFam_congr_rest (h.back hreg) _ _ _ _

/-! ### The witness chain: its family, read-backs and decode -/

variable (zero one vi ts e av st hk hn hrd vAdr) in
/-- **The generated witness chain of an expansion atom**, at the pack. -/
noncomputable def expTagFam (f₀ : dt.CtlIx → A)
    (i : Fin (k * Fintype.card dt.X.Tag + 1)) : dt.CtlIx → A :=
  tagFam ((dt.expArgs zero one vi ts e av hk hn hrd).setTagFlag)
    (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expTagSet vi ts st)
    (dt.expTagCell zero one vi ts) f₀ i

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness chain is blind to the two scratch registers too.** -/
theorem expTagFam_congr_scratch {st' : TapeStD dt A R P}
    (h : dt.ScratchEq st st')
    (hreg : ¬∃ u : Univ A R P dt.KIx dt.dd, vAdr = RF.cell u)
    (f₀ : dt.CtlIx → A) (i : Fin (k * Fintype.card dt.X.Tag + 1)) :
    dt.expTagFam RF zero one vi ts e av st hk hn hrd vAdr f₀ i =
      dt.expTagFam RF zero one vi ts e av st' hk hn hrd vAdr f₀ i := by
  have hset : dt.expTagSet vi ts st = dt.expTagSet vi ts st' := by
    funext i'
    simp only [expTagSet, lvSet, h.2.1, h.2.2.1]
  rw [expTagFam, expTagFam, hset]
  exact tagFam_congr_rest (h.back hreg) _ _ _

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The witness numbering is injective. -/
theorem wIx_injective {i i' : Fin (k * Fintype.card dt.X.Tag)}
    (h : dt.wIx i = dt.wIx i') : i = i' := by
  have h1 : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i').1 :=
    (Prod.ext_iff.mp h).1
  have h2 : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm i').2 :=
    (Fintype.equivFin dt.X.Tag).symm.injective (Prod.ext_iff.mp h).2
  exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

/-- **The index of one witness read**, by position and tag. -/
noncomputable def tagIxOf (ℓ : Fin k) (t : dt.X.Tag) :
    Fin (k * Fintype.card dt.X.Tag) :=
  finProdFinEquiv (ℓ, (Fintype.equivFin dt.X.Tag) t)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The numbering decodes the index. -/
theorem wIx_tagIxOf (ℓ : Fin k) (t : dt.X.Tag) :
    dt.wIx (dt.tagIxOf ℓ t) = (ℓ, t) := by
  rw [wIx, tagIxOf, Equiv.symm_apply_apply]
  exact Prod.ext rfl ((Fintype.equivFin dt.X.Tag).symm_apply_apply t)

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The witness flags read back**: after the chain, the flag of position
`ℓ` and tag `t` holds the digit of the witness cell of `(ℓ, t)`. -/
theorem ctlBit_expTagFam_last (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (ℓ : Fin k) (t : dt.X.Tag) :
    dt.ctlBit one
      (dt.expTagFam RF zero one vi ts e av st hk hn hrd vAdr f₀
        (Fin.last (k * Fintype.card dt.X.Tag))) (dt.tagIx hk ℓ t) ↔
      dt.expTagSet vi ts st (dt.tagIxOf ℓ t)
        (dt.expTagCell zero one vi ts (dt.tagIxOf ℓ t)) := by
  classical
  have hinj : ∀ i i' : Fin (k * Fintype.card dt.X.Tag),
      dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 =
        dt.tagIx hk (dt.wIx i').1 (dt.wIx i').2 → i = i' := by
    intro i i' h
    obtain ⟨h1, h2⟩ := tagIx_injective hk h
    exact dt.wIx_injective (Prod.ext h1 h2)
  have hchain := dt.ctlBit_chain_setCtl (zero := zero) hzo
    (fun i => dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) hinj
    (fun i => dt.expTagSet vi ts st i (dt.expTagCell zero one vi ts i)) f₀
    (k * Fintype.card dt.X.Tag) (dt.tagIxOf ℓ t) (dt.tagIxOf ℓ t).isLt
  have hslot : dt.tagIx hk (dt.wIx (dt.tagIxOf ℓ t)).1
      (dt.wIx (dt.tagIxOf ℓ t)).2 = dt.tagIx hk ℓ t := by
    rw [dt.wIx_tagIxOf]
  rw [hslot] at hchain
  exact hchain

omit [Fintype dt.SlotIx] in
/-- **The chain decodes the argument points' tags**: if the levels'
registers hold the encodings of the points, the flags are one-hot at the
points' tag tuple, which is the branch dispatch's guard. -/
theorem tagsAre_expTagFam (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    (dt.expArgs zero one vi ts e av hk hn hrd).TagsAre
      (fun ℓ => (pts ℓ).1.1)
      (dt.expTagFam RF zero one vi ts e av st hk hn hrd vAdr f₀
        (Fin.last (k * Fintype.card dt.X.Tag))) := by
  intro ℓ t
  rw [dt.ctlBit_expTagFam_last RF hzo f₀ ℓ t]
  have hcell : dt.expTagSet vi ts st (dt.tagIxOf ℓ t)
      (dt.expTagCell zero one vi ts (dt.tagIxOf ℓ t)) ↔ (pts ℓ).1.1 = t := by
    rw [expTagSet, expTagCell, dt.wIx_tagIxOf]
    exact (regBit_wmSeg hlin _ _).symm.trans
      (dt.blk_encTagTup_iff hzo hlin (hENC ℓ) t)
  rw [hcell]
  exact eq_comm

/-! ### The payload at a generated state, and the leaf cells -/

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The payload a leaf read spells at a generated state** is the round's
tuple's: the guard's computed coordinates are the cell of
`DescriptiveComplexity.Draw.Data.expECell`. -/
theorem expPay_expFam (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ)) :
    dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn τ)
      (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a j) =
      dt.expPayTup zero e τ (hn τ) a r := by
  refine congrArg (pad zero) (funext fun q => ?_)
  exact congrFun (readLvE_expFam RF f₀ a j) _

/-! ### The leaf guards, at the generated states -/

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A leaf read's guard holds at its cell**: the computed coordinates are
the round's payload, so the trip stops at the member tuple's cell. -/
theorem expMatch_expFam (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ)) :
    dt.expMatch zero one vi ts e τ r (hn τ)
      (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a j)
      (dt.back RF.cell zero one dt.dd0Le st
        (RF.cell (dt.expECell zero one vi ts e τ (hn τ) a r))) := by
  refine (dt.encG_iff hzo (RF.injective hlin) _ _ _ _ _).mpr ?_
  rw [expECell, dt.expPay_expFam RF f₀ a j r]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A leaf read's guard identifies its cell.** -/
theorem expMatch_expFam_uniq (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A))
    (j : Fin (dt.relNr e τ + 1)) (r : Fin (dt.relNr e τ))
    {y : Univ A R P dt.KIx dt.dd → Prop}
    (hM : dt.expMatch zero one vi ts e τ r (hn τ)
      (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a j)
      (dt.back RF.cell zero one dt.dd0Le st y)) :
    y = RF.cell (dt.expECell zero one vi ts e τ (hn τ) a r) := by
  by_cases hreg : ∃ u : Univ A R P dt.KIx dt.dd, y = RF.cell u
  · obtain ⟨u, rfl⟩ := hreg
    have hu := (dt.encG_iff hzo (RF.injective hlin) _ _ _ _ u).mp hM
    rw [hu, expECell, dt.expPay_expFam RF f₀ a j r]
  · exact absurd hM (dt.not_nameGF_of_not_reg hzo
      (fun u hc => hreg ⟨u, hc⟩))

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P] [Nonempty A] in
/-- **What a leaf trip's digit means**: at a round's cell, the register's
bit is the block atom's value at the points the registers encode, read at
the valuation the round's tuple spells. This is the `hav` input of
`DescriptiveComplexity.Draw.Data.expLeafVal_iff`, hence of the exit
verdict. -/
theorem expESet_expECell_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.relNr e τ))
    {f : dt.CtlIx → A} (hf : dt.readLvE f = ofLex a) :
    dt.expESet vi ts e st τ r
        (dt.expECell zero one vi ts e τ (hn τ) a r) ↔
      BlkAtom.holds (L := L) (B := dt.X.B.replicate k)
        (dt.X.B.replicateAssign fun ℓ => (pts ℓ).1.2)
        (fun j => f (dt.lvE (Fin.castLE (hn τ) j)))
        (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2) := by
  have hpay : dt.expPay (zero := zero) (e := e) (τ := τ) (r := r)
      (hn := hn τ) f = dt.expPayTup zero e τ (hn τ) a r :=
    congrArg (pad zero) (funext fun q => congrFun hf _)
  have h := dt.regBit_expMatch (zero := zero) hzo hlin ts e τ r (hn τ) pts
    (m := dt.expESet vi ts e st τ r)
    (hENC (relLeafData e τ r).1.1) f
  rw [hpay] at h
  exact (regBit_wmSeg hlin _ _).symm.trans h

/-! ### The expansion atom's machine run -/

section ExpRun

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
variable {gbot : Univ A R P dt.KIx dt.dd} (hbot : ∀ y, WMLe gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable {t₀ : dt.SlotIx} {m₀ : Univ A R P dt.KIx dt.dd → Prop}
variable (hm₀ : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le st r t₀ =
  bitVal PR.zero PR.one (bitAtOf RF.cell m₀ r))
variable (hwkt₀ : (Slot.wk : dt.SlotIx) ≠ t₀)
variable (hrgt₀ : (Slot.reg : dt.SlotIx) ≠ t₀)
variable (pts : Fin k → dt.X.Map A)
variable (hENC : ∀ ℓ : Fin k,
  wmBlk (dt.lvSet st vi (ts ℓ))
    (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
    encMap dt.ly PR.zero PR.one (pts ℓ))
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hord hbot hv hvi hwkSt hm₀ hwkt₀ hrgt₀ hENC in
/-- **The expansion atom's machine run**: from the machinery's first phase
at the marker – the witness chain decoding the argument points' tags, the
dispatch onto their branch, and that branch's wide element loop, one leaf
trip per block atom – to the exit phase one cell to the marker's right. -/
theorem exp_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ (dt.back RF.cell PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).exitSt
            (fun ℓ => (pts ℓ).1.1)
            (dt.expFam RF PR.zero PR.one vi ts e av st (fun ℓ => (pts ℓ).1.1)
              hk hn hrd v
              (dt.expTagFam RF PR.zero PR.one vi ts e av st hk hn hrd v f₀
                (Fin.last (k * Fintype.card dt.X.Tag)))
              (toLex topTup)
              (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ (dt.back RF.cell PR.zero PR.one dt.dd0Le st) m₀)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  refine tag_run_iter RF.toIx hrules hR hlin hlin hbot hv hvi
    (fun r => by
      rw [show dt.back RF.cell PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun r => rfl)
    (mT := dt.expTagSet vi ts st)
    (fun i r => dt.back_lvTrackD RF hord PR.zero PR.one st vi (ts (dt.wIx i).1) r)
    (fun i => dt.wk_ne_lvTrack vi (ts (dt.wIx i).1))
    (fun i => dt.reg_ne_lvTrack vi (ts (dt.wIx i).1))
    hm₀ hwkt₀ hrgt₀
    (xT := dt.expTagCell PR.zero PR.one vi ts) (f₀ := f₀)
    ?_ ?_
    (τ := fun ℓ => (pts ℓ).1.1)
    (dt.tagsAre_expTagFam RF hzo hlin pts hENC f₀)
    (mE := dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1))
    (fun j r => dt.back_lvTrackD RF hord PR.zero PR.one st vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r)
    (fun j => dt.wk_ne_lvTrack vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1))
    (fun j => dt.reg_ne_lvTrack vi
      (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1))
    (a₀ := toLex botTup) (aT := toLex topTup)
    (fun a => tup_isBot_iff.mpr (fun p b => botTup_le p b) a)
    (fun a => tup_isTop_iff.mpr (fun p b => le_topTup p b) a)
    (xE := dt.expECell PR.zero PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
      (hn (fun ℓ => (pts ℓ).1.1)))
    ?_ ?_ ?_ ?_
  · -- the witness guards hold at their cells
    intro i
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT i)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      (m := dt.expTagSet vi ts st i)
      RF.toIx (fun r => dt.back_lvTrackD RF hord PR.zero PR.one st vi (ts (dt.wIx i).1) r) _]
    exact (dt.encG_iff hzo (RF.injective hlin) _ _ _ _ _).mpr rfl
  · -- the witness guards identify their cells
    intro i r hM
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackT i)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      (m := dt.expTagSet vi ts st i)
      RF.toIx (fun r' => dt.back_lvTrackD RF hord PR.zero PR.one st vi (ts (dt.wIx i).1) r') _]
      at hM
    by_cases hreg : ∃ u : Univ A R P dt.KIx dt.dd, r = RF.cell u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.encG_iff hzo (RF.injective hlin) _ _ _ _ u).mp hM
      rw [hu]
      rfl
    · exact absurd hM (dt.not_nameGF_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the leaf guards hold at their cells
    intro a j
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE
        (fun ℓ => (pts ℓ).1.1) j)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      (m := dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1) j)
      RF.toIx (fun r => dt.back_lvTrackD RF hord PR.zero PR.one st vi
        (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r) _]
    exact dt.expMatch_expFam RF hzo hlin _ a j.castSucc j
  · -- the leaf guards identify their cells
    intro a j r hM
    rw [passTracks_of_back
      (t := (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).rdTrackE
        (fun ℓ => (pts ℓ).1.1) j)
      (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st)
      (m := dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1) j)
      RF.toIx (fun r' => dt.back_lvTrackD RF hord PR.zero PR.one st vi
        (ts (relLeafData e (fun ℓ => (pts ℓ).1.1) j).1.1) r') _] at hM
    exact dt.expMatch_expFam_uniq RF hzo hlin _ a j.castSucc j hM
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
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v
        (dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.expECell PR.zero PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v (dt.expTagSet vi ts st)
          (dt.expTagCell PR.zero PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        (toLex topTup)
        (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1)))) =
      ofLex (toLex topTup) from readLvE_expFam RF _ _ _]
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
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v
        (dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.expECell PR.zero PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v (dt.expTagSet vi ts st)
          (dt.expTagCell PR.zero PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        a (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))) := hc
    rw [show dt.readLvE (elemFam
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setFlagE
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).initEl
          (fun ℓ => (pts ℓ).1.1))
        ((dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).advEl
          (fun ℓ => (pts ℓ).1.1))
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v
        (dt.expESet vi ts e st (fun ℓ => (pts ℓ).1.1))
        (dt.expECell PR.zero PR.one vi ts e (fun ℓ => (pts ℓ).1.1)
          (hn (fun ℓ => (pts ℓ).1.1)))
        (tagFam (dt.expArgs PR.zero PR.one vi ts e av hk hn hrd).setTagFlag
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) v (dt.expTagSet vi ts st)
          (dt.expTagCell PR.zero PR.one vi ts) f₀
          (Fin.last (k * Fintype.card dt.X.Tag)))
        a (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1)))) =
      ofLex a from readLvE_expFam RF _ _ _] at hc2
    exact absurd (tup_isTop_iff.mpr hc2 (toLex topTup)) (not_le_of_gt ha)

end ExpRun

/-! ### The sub-fold: the sac invariant and the exit verdict -/

section ExpVerdict

variable (dt e τ hnτ) in
/-- **The branch's leaf, over the wide valuation**: the defining sentence's
matrix at the points' assignments, its levels read off the first `n`
coordinates of the wide tuple. -/
noncomputable def expLeafP (pts : Fin k → dt.X.Map A)
    (v : Fin dt.eDim → A) : Prop :=
  dt.expLeaf e τ (fun ℓ => (pts ℓ).1.2) fun j => v (Fin.castLE hnτ j)

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A sub-fold accumulator rides along a control-bit store off it. -/
theorem readSac_setCtl {zero one : A} {q : dt.CtlIx}
    (hq : ∀ j : Fin dt.eDim, dt.sacC j ≠ q) (b : Prop) (f : dt.CtlIx → A)
    (j : ℕ) :
    dt.readSac one (dt.setCtl zero one q b f) j ↔ dt.readSac one f j := by
  refine exists_congr fun h => ?_
  rw [setCtl_of_ne (hq ⟨j, h⟩)]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A sub-fold accumulator rides along a wide-tuple advance. -/
theorem readSac_advLvE {one : A} (f : dt.CtlIx → A) (j : ℕ) :
    dt.readSac one (dt.advLvE f) j ↔ dt.readSac one f j := by
  refine exists_congr fun h => ?_
  have hne : ∀ j' : Fin dt.eDim, dt.sacC ⟨j, h⟩ ≠ dt.lvE j' :=
    fun j' hc => nomatch hc
  rw [advLvE, putLvE_of_not_lv hne]

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A within-round chain preserving the accumulators preserves them end to
end.** -/
theorem readSac_chainSt {one : A} {nr : ℕ} (bit : Fin nr → Prop)
    (upd : Fin nr → Bool → (dt.CtlIx → A) → dt.CtlIx → A)
    (hupd : ∀ (i : Fin nr) (b : Bool) (f : dt.CtlIx → A) (j : ℕ),
      dt.readSac one (upd i b f) j ↔ dt.readSac one f j)
    (base : dt.CtlIx → A) (n : ℕ) (j : ℕ) :
    dt.readSac one (chainSt bit upd base n) j ↔ dt.readSac one base j := by
  classical
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    by_cases h : n < nr
    · by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb, hupd, ih]
      · rw [chainSt_succ_neg h hb, hupd, ih]
    · have hskip : chainSt bit upd base (n + 1) = chainSt bit upd base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip, ih]

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] in
/-- A leaf-read store preserves the accumulators. -/
theorem readSac_exp_setFlag (r : Fin (dt.relNr e τ)) (bb : Bool)
    (q : dt.CtlIx → A) (g : dt.SlotIx → A) (j : ℕ) :
    dt.readSac one
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ r bb q g) j ↔
      dt.readSac one q j := by
  change dt.readSac one (dt.setCtl zero one (dt.rdfC (Fin.castLE (hrd τ) r))
    (bb = true) q) j ↔ _
  have hne : ∀ j' : Fin dt.eDim,
      dt.sacC j' ≠ dt.rdfC (Fin.castLE (hrd τ) r) := fun j' h => nomatch h
  exact readSac_setCtl hne _ q j

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The leaf-read flags read back**: at a round's end, the flag of the
`r`-th block atom holds the digit of the round's cell. -/
theorem ctlBit_rdf_expFam (hzo : zero ≠ one) (f₀ : dt.CtlIx → A)
    (a : Lex (Fin dt.eDim → A)) (r : Fin (dt.relNr e τ)) :
    dt.ctlBit one
        (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a
          (Fin.last (dt.relNr e τ)))
        (dt.rdfC (Fin.castLE (hrd τ) r)) ↔
      dt.expESet vi ts e st τ r
        (dt.expECell zero one vi ts e τ (hn τ) a r) := by
  have hinj : ∀ r₁ r₂ : Fin (dt.relNr e τ),
      dt.rdfC (Fin.castLE (hrd τ) r₁) = dt.rdfC (Fin.castLE (hrd τ) r₂) →
        r₁ = r₂ := fun r₁ r₂ h =>
    Fin.castLE_injective _ (dt.rdfC_injective h)
  exact dt.ctlBit_chain_setCtl hzo
    (fun r' => dt.rdfC (Fin.castLE (hrd τ) r')) hinj
    (fun r' => dt.expESet vi ts e st τ r'
      (dt.expECell zero one vi ts e τ (hn τ) a r'))
    (elemIter ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
      (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
      (dt.expECell zero one vi ts e τ (hn τ)) f₀ a)
    (dt.relNr e τ) r r.isLt

omit [Fintype dt.SlotIx] in
/-- **The leaf flag's value at a round's end is the branch's leaf**: with
the flags holding the block atoms' bits and the loop element the round's
tuple, the Boolean function the control computes is the leaf predicate at
that tuple. -/
theorem expLeafVal_expFam (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) :
    dt.expLeafVal one e τ (hn τ) (hrd τ)
        (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a
          (Fin.last (dt.relNr e τ))) ↔
      dt.expLeafP e τ (hn τ) pts (ofLex a) := by
  have hval := dt.expLeafVal_iff one e τ (hn τ) (hrd τ)
    (fun ℓ => (pts ℓ).1.2)
    (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ a
      (Fin.last (dt.relNr e τ)))
    (fun r => (dt.ctlBit_rdf_expFam RF hzo f₀ a r).trans
      (dt.expESet_expECell_iff hzo hlin pts hENC a r
        (readLvE_expFam RF f₀ a (Fin.last (dt.relNr e τ)))))
  refine hval.trans ?_
  rw [expLeafP]
  refine iff_of_eq (congrArg _ (funext fun j => ?_))
  exact congrFun (readLvE_expFam RF f₀ a (Fin.last (dt.relNr e τ))) _

omit [Fintype dt.SlotIx] in
/-- **The sub-fold's accumulators fold the strict prefix**: at every round's
entry, the `sac` slots hold the completed-subtree contributions of the
branch's prefix at the round's tuple. -/
theorem readSac_expIter (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) (a : Lex (Fin dt.eDim → A)) (j : ℕ)
    (hj : j < dt.eDim) :
    dt.readSac one (elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
        (dt.expECell zero one vi ts e τ (hn τ)) f₀ a) j ↔
      accCVal (dt.relPk e τ).pol (dt.expLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) j (ofLex a) := by
  classical
  induction a using order_induction generalizing j with
  | hmin z hz =>
    rw [elemIter, iterOrd_bot hz]
    have hread : dt.readSac one
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ f₀
          (dt.back RF.cell zero one dt.dd0Le st vAdr)) j ↔
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
    set F := elemFam ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
      ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
      (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
      (dt.expECell zero one vi ts e τ (hn τ)) f₀ w
      (Fin.last (dt.relNr e τ)) with hF
    have hreadF : ∀ j' : ℕ, dt.readSac one F j' ↔
        dt.readSac one (elemIter
          ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
          ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
          (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
          (dt.expECell zero one vi ts e τ (hn τ)) f₀ w) j' := by
      intro j'
      rw [hF]
      exact readSac_chainSt _ _
        (fun i bb f j'' => readSac_exp_setFlag i bb f _ j'') _ _ j'
    have hlvF : dt.readLvE F = ofLex w :=
      readLvE_expFam RF f₀ w (Fin.last (dt.relNr e τ))
    -- one round of the machine's fold
    have hstepEq : elemIter
        ((dt.expArgs zero one vi ts e av hk hn hrd).setFlagE τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).initEl τ)
        ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ)
        (dt.back RF.cell zero one dt.dd0Le st) vAdr (dt.expESet vi ts e st τ)
        (dt.expECell zero one vi ts e τ (hn τ)) f₀ z =
        (dt.expArgs zero one vi ts e av hk hn hrd).advEl τ F
          (dt.back RF.cell zero one dt.dd0Le st vAdr) := by
      rw [elemIter, iterOrd_covers hwz hnb]
      rfl
    rw [hstepEq]
    -- the advance, unfolded to the carry write
    have hadv : ∀ j' : ℕ, j' < dt.eDim →
        (dt.readSac one
          ((dt.expArgs zero one vi ts e av hk hn hrd).advEl τ F
            (dt.back RF.cell zero one dt.dd0Le st vAdr)) j' ↔
        dt.readSac one
          (dt.carrySac zero one (dt.relPk e τ).pol (tupCarry (dt.readLvE F))
            (dt.setSubLeaf zero one
              (dt.expLeafVal one e τ (hn τ) (hrd τ) F) F)) j') := by
      intro j' hj'
      change dt.readSac one (dt.expAdv zero one e τ (hn τ) (hrd τ) F) j' ↔ _
      rw [expAdv]
      exact readSac_advLvE _ j'
    -- close by the vector's step rule
    rw [hadv j hj, hlvF]
    refine accCVal_step (le := (· ≤ · : A → A → Prop)) (v := ofLex w)
      ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
        fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
      (hc := hpc ▸ pc.isLt) ?_ ?_ ?_ ?_
      (acc := dt.readSac one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ) F) F))
      (leaf := dt.ctlBit one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ) F) F) dt.subLeafC)
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
      exact expLeafVal_expFam RF hzo hlin pts hENC f₀ w
    · -- the new readings are the carry write's
      intro i hi
      exact readSac_carrySac hzo (dt.relPk e τ).pol (tupCarry (ofLex w))
        (dt.setSubLeaf zero one
          (dt.expLeafVal one e τ (hn τ) (hrd τ) F) F) (j := i) hi

omit [Fintype dt.SlotIx] in
/-- **The verdict the exit control carries**: the atom's slot holds the fold
of the branch's whole prefix at the points' assignments – the value
`DescriptiveComplexity.Draw.Data.expLeaf`'s prefix takes over every wide
tuple, which `DescriptiveComplexity.Problems.Wide.DrawExp` reads as the
expansion atom's truth. -/
theorem ctlBit_avC_exp_exit (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.expArgs zero one vi ts e av hk hn hrd).exitSt τ
          (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀
            (toLex topTup) (Fin.last (dt.relNr e τ)))
          (dt.back RF.cell zero one dt.dd0Le st vAdr))
        (dt.avC av) ↔
      foldFrom (dt.relPk e τ).pol (dt.expLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) 0 topTup := by
  classical
  change dt.ctlBit one (dt.expExit zero one e τ (hn τ) (hrd τ) av
    (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀ (toLex topTup)
      (Fin.last (dt.relNr e τ)))) (dt.avC av) ↔ _
  rw [expExit, ctlBit_setCtl_self hzo]
  have hacc : ∀ j : ℕ, j < dt.eDim →
      (dt.readSac one (dt.setSubLeaf zero one
        (dt.expLeafVal one e τ (hn τ) (hrd τ)
          (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀
            (toLex topTup) (Fin.last (dt.relNr e τ))))
        (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀
          (toLex topTup) (Fin.last (dt.relNr e τ)))) j ↔
      accCVal (dt.relPk e τ).pol (dt.expLeafP e τ (hn τ) pts)
        (· ≤ · : A → A → Prop) j (ofLex (toLex topTup))) := by
    intro j hj
    rw [readSac_setSubLeaf]
    refine Iff.trans ?_ (dt.readSac_expIter (av := av) (hk := hk)
      (hrd := hrd) (vAdr := vAdr) RF hzo hlin pts hENC f₀ (toLex topTup) j hj)
    rw [expFam, elemFam]
    exact readSac_chainSt _ _
      (fun i bb f j'' => readSac_exp_setFlag i bb f _ j'') _ _ j
  have hleaf : dt.ctlBit one (dt.setSubLeaf zero one
      (dt.expLeafVal one e τ (hn τ) (hrd τ)
        (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀
          (toLex topTup) (Fin.last (dt.relNr e τ))))
      (dt.expFam RF zero one vi ts e av st τ hk hn hrd vAdr f₀
        (toLex topTup) (Fin.last (dt.relNr e τ)))) dt.subLeafC ↔
      dt.expLeafP e τ (hn τ) pts (ofLex (toLex topTup)) := by
    rw [ctlBit_setSubLeaf hzo]
    exact expLeafVal_expFam RF hzo hlin pts hENC f₀ (toLex topTup)
  exact sacVerdict_iff_foldFrom hacc hleaf

omit [Fintype dt.SlotIx] in
/-- **The expansion atom's verdict is its truth**: at the argument points
the registers encode, the bit the exit control files in the atom's slot is
`RelMap` of the expansion – the machine has evaluated the defining
sentence. -/
theorem ctlBit_avC_exp_relMap (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (pts : Fin k → dt.X.Map A)
    (hENC : ∀ ℓ : Fin k,
      wmBlk (dt.lvSet st vi (ts ℓ))
        (Tag.arg (toLex (dt.lvBlk vi (ts ℓ))) : Tag R P dt.KIx) =
        encMap dt.ly zero one (pts ℓ))
    (f₀ : dt.CtlIx → A) :
    dt.ctlBit one
        ((dt.expArgs zero one vi ts e av hk hn hrd).exitSt
          (fun ℓ => (pts ℓ).1.1)
          (dt.expFam RF zero one vi ts e av st (fun ℓ => (pts ℓ).1.1) hk hn hrd
            vAdr f₀ (toLex topTup)
            (Fin.last (dt.relNr e (fun ℓ => (pts ℓ).1.1))))
          (dt.back RF.cell zero one dt.dd0Le st vAdr))
        (dt.avC av) ↔
      RelMap (M := dt.X.Map A) e pts := by
  refine (dt.ctlBit_avC_exp_exit (τ := fun ℓ => (pts ℓ).1.1) RF hzo hlin pts
    hENC f₀).trans ?_
  refine (foldFrom_top (j₀ := 0)
    ⟨fun x => le_refl x, fun x y z hxy hyz => le_trans hxy hyz,
      fun x y hxy hyx => le_antisymm hxy hyx, fun x y => le_total x y⟩
    (fun i _ a => le_topTup i a) (Nat.le_refl 0)).trans ?_
  exact (dt.relMap_iff_altQuantFrom_expLeaf_pad e pts
    (hn (fun ℓ => (pts ℓ).1.1)) topTup).symm

end ExpVerdict

end ExpInst

end Data

end Draw

end DescriptiveComplexity
