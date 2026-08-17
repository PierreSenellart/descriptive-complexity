/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpDefCtl

/-!
# The folds are definable

What the program's control holds between rounds is a **fold**: one accumulator
per level of a quantifier prefix, closed by a leaf flag. Reading it back is
`DescriptiveComplexity.Pfp.chainFrom`, a recursion down the levels, and writing
it at a carry is `DescriptiveComplexity.Pfp.PfpData.putVec` of a family whose
entries branch on the carry.

Both are definable, and for the same reason: the recursion is over a *fixed*
number of levels, so recursing the same way builds the pattern function. The
atoms are `DescriptiveComplexity.Pfp.PfpData.uGDefinable_readVec` and
`uGDefinable_ctlBit`; everything else is the connectives.

The matrix's own value at the atoms' verdicts
(`DescriptiveComplexity.Pfp.qfValue`) is the same shape one level down – a
recursion over the syntax rather than over the levels – so it is here too.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : PfpData L} [Fintype dt.SlotIx]

/-! ### The chain -/

/-- **A fold, read back, is definable**: the recursion down the levels is
finite, so recursing the same way builds the formula. The leaf it closes with
is the caller's – a flag of the control, or a bit it is about to store. -/
theorem uGDefinable_chainFrom {m : ℕ} (accs : Fin m → dt.CtlIx)
    {leaf : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hleaf : UGDefinable leaf) (pol : ℕ → Bool) (n : ℕ) :
    ∀ j : ℕ, UGDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) g =>
        chainFrom pol (dt.readVec e.one accs f) (leaf e f g) n j := by
  have key : ∀ k j : ℕ, n - j ≤ k → UGDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) g =>
        chainFrom pol (dt.readVec e.one accs f) (leaf e f g) n j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      exact hleaf.congr fun _ _ _ => iff_of_eq (chainFrom_of_le (by omega))
    | succ k ih =>
      intro j hj
      by_cases hlt : j < n
      · have h1 := (uGDefinable_readVec (dt := dt) accs j).or (ih (j + 1) (by omega))
        have h2 := (uGDefinable_readVec (dt := dt) accs j).and (ih (j + 1) (by omega))
        exact (UGDefinable.ite (p := pol j = true) h1 h2).congr fun _ _ _ =>
          iff_of_eq (chainFrom_succ hlt)
      · exact hleaf.congr fun _ _ _ =>
          iff_of_eq (chainFrom_of_le (not_lt.mp hlt))
  exact fun j => key (n - j) j le_rfl

/-- **The inner fold's verdict is definable.** -/
theorem uGDefinable_accVerdict (pol : ℕ → Bool) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.accVerdict e.one pol f :=
  (uGDefinable_chainFrom dt.accC (uGDefinable_ctlBit dt.leafC) pol dt.ki 0).congr
    fun _ _ _ => Iff.rfl

/-- **A sub-fold's verdict is definable.** -/
theorem uGDefinable_sacVerdict (pol : ℕ → Bool) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.sacVerdict e.one pol f :=
  (uGDefinable_chainFrom dt.sacC (uGDefinable_ctlBit dt.subLeafC) pol dt.eDim 0).congr
    fun _ _ _ => Iff.rfl

/-! ### The write at a carry -/

/-- **A fold at a tuple successor is definable**: below the carry each level
keeps its bit, the carry absorbs the chain below it, and the levels above it
reset – three branches decided when the formula is built. -/
theorem uStDefinable_carryVec {m : ℕ} {accs : Fin m → dt.CtlIx}
    (hinj : Function.Injective accs) (leafSlot : dt.CtlIx) (pol : ℕ → Bool)
    (n c : ℕ) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.putVec e.zero e.one accs f fun j =>
        if (j : ℕ) < c then dt.readVec e.one accs f (j : ℕ)
          else if (j : ℕ) = c then
            (if pol c = true then
                dt.readVec e.one accs f c ∨
                  chainFrom pol (dt.readVec e.one accs f)
                    (dt.ctlBit e.one f leafSlot) n (c + 1)
              else
                dt.readVec e.one accs f c ∧
                  chainFrom pol (dt.readVec e.one accs f)
                    (dt.ctlBit e.one f leafSlot) n (c + 1))
          else (pol (j : ℕ) = false) :=
  uStDefinable_putVec hinj fun j =>
    UGDefinable.ite (p := (j : ℕ) < c) (uGDefinable_readVec accs (j : ℕ))
      (UGDefinable.ite (p := (j : ℕ) = c)
        (UGDefinable.ite (p := pol c = true)
          ((uGDefinable_readVec accs c).or
            (uGDefinable_chainFrom accs (uGDefinable_ctlBit leafSlot) pol n (c + 1)))
          ((uGDefinable_readVec accs c).and
            (uGDefinable_chainFrom accs (uGDefinable_ctlBit leafSlot) pol n (c + 1))))
        (uGDefinable_const (pol (j : ℕ) = false)))

/-- **The inner fold at a carry.** -/
theorem uStDefinable_carryAcc (pol : ℕ → Bool) (c : ℕ) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.carryAcc e.zero e.one pol c f :=
  (uStDefinable_carryVec dt.accC_injective dt.leafC pol dt.ki c).congr
    fun _ _ _ _ => rfl

/-- **A sub-fold at a carry.** -/
theorem uStDefinable_carrySac (pol : ℕ → Bool) (c : ℕ) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.carrySac e.zero e.one pol c f :=
  (uStDefinable_carryVec dt.sacC_injective dt.subLeafC pol dt.eDim c).congr
    fun _ _ _ _ => rfl

/-- **A sub-fold at its first tuple.** -/
theorem uStDefinable_initSac (pol : ℕ → Bool) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.initSac e.zero e.one pol f :=
  uStDefinable_putVec dt.sacC_injective fun j =>
    uGDefinable_const (pol (j : ℕ) = false)

/-- **Storing a sub-fold's leaf.** -/
theorem uStDefinable_setSubLeaf
    {b : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.setSubLeaf e.zero e.one (b e f g) f :=
  uStDefinable_setCtl dt.subLeafC hb

/-! ### The atoms a leaf is evaluated from -/

/-- **A block atom's value at the control is definable.** Three of its four
shapes are what a guard may now ask: two control slots are equal, one is at
most another, and a relation of the **source vocabulary** holds of a tuple of
them – the last two being exactly what an equality pattern cannot say. The
fourth, a relation variable of the block, is a read leaf and never evaluated
here. -/
theorem uGDefinable_blkAtomHolds {B : SOBlock} {n : ℕ} (v : Fin n → dt.CtlIx)
    (κ : BlkAtom L B n) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      BlkAtom.holds (L := L) (B := B) (fun _ _ => False) (fun j => f (v j)) κ := by
  match κ with
  | .eqA j₁ j₂ =>
    exact (uGDefinable_ctlEq (L := L) (W := dt.SlotIx) (v j₁) (v j₂)).congr
      fun _ _ _ => Iff.rfl
  | .ordA j₁ j₂ =>
    exact (uGDefinable_ctlLe (L := L) (W := dt.SlotIx) (v j₁) (v j₂)).congr
      fun _ _ _ => Iff.rfl
  | .baseA r ts =>
    exact (uGDefinable_ctlRel (W := dt.SlotIx) r fun j => v (ts j)).congr
      fun _ _ _ => Iff.rfl
  | .blkA i ts =>
    exact (uGDefinable_false (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun _ _ _ => Iff.rfl

/-! ### The matrix at its atoms' verdicts -/

/-- **A quantifier-free formula's value at a definable reading of its atoms is
definable**: a recursion over the syntax, the atoms being the caller's. -/
theorem uGDefinable_qfValue {L' : Language.{0, 0}} {α : Type} :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n)
      (val : ∀ e : Env L,
        (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → L'.BoundedFormula α n → Prop),
      (∀ a : L'.BoundedFormula α n, UGDefinable fun e f g => val e f g a) →
      UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
        fun e f g => qfValue φ (val e f g) := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => uGDefinable_false
  | equal t₁ t₂ => exact fun _ hval => hval _
  | rel r ts => exact fun _ hval => hval _
  | imp φ ψ ih₁ ih₂ =>
    exact fun val hval => (ih₁ val hval).imp (ih₂ val hval)
  | all φ _ => exact fun _ _ => uGDefinable_false

/-- **The matrix's value at the atoms' verdicts is definable**: each atom's
verdict is one of finitely many control flags. -/
theorem uGDefinable_postLeaf (v : dt.VarIx) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.postLeaf e.one v f :=
  uGDefinable_qfValue (dt.matOf v) _ fun a =>
    uGDefinable_exists fun k : Fin (dt.natOf v) =>
      (uGDefinable_const ((dt.atomsOf v).get k = a)).and
        (uGDefinable_ctlBit (dt.avC (Fin.castLE (dt.natOf_le_natMax v) k)))

end PfpData

end Pfp

end DescriptiveComplexity
