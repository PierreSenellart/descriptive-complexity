/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawCtl
import DescriptiveComplexity.Problems.Wide.DrawAcc

/-!
# The fold, in the control's slots

`DescriptiveComplexity.Problems.Wide.DrawAcc` says what the machine must
carry across the inner loop – one **contribution** per level plus the last
leaf – and how a round rewrites it. This file puts that in the program's own
slots, which is what the `dstSt` parameters of
`DescriptiveComplexity.Draw.Data.varRule` are:

* `initSt` is `DescriptiveComplexity.Draw.Data.initAcc` – every
  accumulator the polarity's unit, which is what an empty register's fold is
  (`accCVal_bot`);
* `postFold` is `DescriptiveComplexity.Draw.Data.setLeaf` at `postLeaf` –
  the matrix's Boolean value at the atoms' verdicts, in the leaf flag;
* `storeCarry b` is `DescriptiveComplexity.Draw.Data.carryAcc` – untouched
  below the carry, absorbing the chain at it, reset above (`accCVal_step`);
* `accBit` is `DescriptiveComplexity.Draw.Data.accVerdict` – the chain from
  level `0`, which is the whole prefix once the register is exhausted.

Every one of them is a function of the pointer alone, and each comes with
the equation the run needs: what the *next* pointer's slots read back. The
fold's own correctness is `DrawAcc`'s; nothing here repeats it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A : Type}

/-! ### The accumulator vector -/

variable (zero one : A)

/-- **A vector of control slots, read**: one bit per index. Past the family
it is `False`; a fold never looks there. -/
def readVec {m : ℕ} (accs : Fin m → dt.CtlIx) (f : dt.CtlIx → A) (j : ℕ) : Prop :=
  ∃ h : j < m, f (accs ⟨j, h⟩) = one

open Classical in
/-- **A vector of control slots, written.** -/
noncomputable def putVec {m : ℕ} (accs : Fin m → dt.CtlIx) (f : dt.CtlIx → A)
    (b : Fin m → Prop) : dt.CtlIx → A :=
  fun q => if h : ∃ j : Fin m, q = accs j then bitVal zero one (b h.choose) else f q

variable {dt zero one}

theorem putVec_of_not_mem {m : ℕ} {accs : Fin m → dt.CtlIx} {f : dt.CtlIx → A}
    {b : Fin m → Prop} {q : dt.CtlIx} (h : ∀ j : Fin m, q ≠ accs j) :
    dt.putVec zero one accs f b q = f q := by
  classical
  rw [putVec, dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj

/-- **A vector reads back**, index by index. -/
theorem readVec_putVec (hzo : zero ≠ one) {m : ℕ} {accs : Fin m → dt.CtlIx}
    (hinj : Function.Injective accs) (f : dt.CtlIx → A) (b : Fin m → Prop)
    {j : ℕ} (hj : j < m) :
    dt.readVec one accs (dt.putVec zero one accs f b) j ↔ b ⟨j, hj⟩ := by
  classical
  constructor
  · rintro ⟨h, hv⟩
    have hex : ∃ j' : Fin m, accs ⟨j, h⟩ = accs j' := ⟨⟨j, h⟩, rfl⟩
    rw [putVec, dif_pos hex] at hv
    have hb := (bitVal_iff hzo).mp hv
    rwa [hinj hex.choose_spec.symm] at hb
  · intro hb
    refine ⟨hj, ?_⟩
    have hex : ∃ j' : Fin m, accs ⟨j, hj⟩ = accs j' := ⟨⟨j, hj⟩, rfl⟩
    rw [putVec, dif_pos hex]
    refine (bitVal_iff hzo).mpr ?_
    rw [← hinj hex.choose_spec]
    exact hb

variable (dt zero one)

/-- **The inner fold's accumulator vector**, one bit per level. -/
def readAcc (f : dt.CtlIx → A) (j : ℕ) : Prop := dt.readVec one dt.accC f j

/-- **The inner fold's accumulator vector, written.** -/
noncomputable def putAcc (f : dt.CtlIx → A) (b : Fin dt.naDim → Prop) :
    dt.CtlIx → A :=
  dt.putVec zero one dt.accC f b

/-- **A sub-fold's accumulator vector**: the element loops of the atom
subroutines keep theirs in the `sac` slots, one per level of the defining
sentence's own prefix. -/
def readSac (f : dt.CtlIx → A) (j : ℕ) : Prop := dt.readVec one dt.sacC f j

/-- **A sub-fold's accumulator vector, written.** -/
noncomputable def putSac (f : dt.CtlIx → A) (b : Fin dt.eDim → Prop) :
    dt.CtlIx → A :=
  dt.putVec zero one dt.sacC f b

theorem sacC_injective : Function.Injective dt.sacC := by
  intro j j' h
  injection h

variable {dt zero one}

theorem putAcc_of_not_acc {f : dt.CtlIx → A} {b : Fin dt.naDim → Prop}
    {q : dt.CtlIx} (h : ∀ j : Fin dt.naDim, q ≠ dt.accC j) :
    dt.putAcc zero one f b q = f q :=
  putVec_of_not_mem h

theorem putSac_of_not_sac {f : dt.CtlIx → A} {b : Fin dt.eDim → Prop}
    {q : dt.CtlIx} (h : ∀ j : Fin dt.eDim, q ≠ dt.sacC j) :
    dt.putSac zero one f b q = f q :=
  putVec_of_not_mem h

/-- The inner fold's vector reads back, level by level. -/
theorem readAcc_putAcc (hzo : zero ≠ one) (f : dt.CtlIx → A)
    (b : Fin dt.naDim → Prop) {j : ℕ} (hj : j < dt.naDim) :
    dt.readAcc one (dt.putAcc zero one f b) j ↔ b ⟨j, hj⟩ :=
  readVec_putVec hzo dt.accC_injective f b hj

/-- A sub-fold's vector reads back, level by level. -/
theorem readSac_putSac (hzo : zero ≠ one) (f : dt.CtlIx → A)
    (b : Fin dt.eDim → Prop) {j : ℕ} (hj : j < dt.eDim) :
    dt.readSac one (dt.putSac zero one f b) j ↔ b ⟨j, hj⟩ :=
  readVec_putVec hzo dt.sacC_injective f b hj

/-! ### The leaf flag -/

variable (dt zero one)

/-- **The leaf flag**: the value of the matrix at the valuation the loop has
just evaluated – the bit every carry absorbs. -/
noncomputable def leafC : dt.CtlIx := dt.scratchC 0

/-- **The matrix's Boolean value at the atoms' verdicts**: what the machine
knows once every atom subroutine has filed its bit. -/
noncomputable def postLeaf (v : dt.VarIx) (f : dt.CtlIx → A) : Prop :=
  qfValue (dt.matOf v) fun a =>
    ∃ k : Fin (dt.natOf v), (dt.atomsOf v).get k = a ∧
      dt.ctlBit one f (dt.avC (Fin.castLE (dt.natOf_le_natMax v) k))

/-- **Storing the leaf.** -/
noncomputable def setLeaf (b : Prop) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one dt.leafC b f

variable {dt zero one}

theorem accC_ne_leafC (j : Fin dt.naDim) : dt.accC j ≠ dt.leafC := fun h => nomatch h

theorem leafC_ne_accC (j : Fin dt.naDim) : dt.leafC ≠ dt.accC j := fun h => nomatch h

@[simp]
theorem ctlBit_setLeaf (hzo : zero ≠ one) (b : Prop) (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.setLeaf zero one b f) dt.leafC ↔ b :=
  ctlBit_setCtl_self hzo _ _ _

theorem setLeaf_of_ne {q : dt.CtlIx} (hne : q ≠ dt.leafC) (b : Prop)
    (f : dt.CtlIx → A) : dt.setLeaf zero one b f q = f q :=
  setCtl_of_ne hne _ _

/-- The accumulators ride along a write of the leaf flag. -/
theorem readAcc_setLeaf (b : Prop) (f : dt.CtlIx → A) (j : ℕ) :
    dt.readAcc one (dt.setLeaf zero one b f) j ↔ dt.readAcc one f j := by
  refine exists_congr fun h => ?_
  rw [setLeaf_of_ne (accC_ne_leafC (dt := dt) ⟨j, h⟩)]

/-! ### The three updates -/

variable (dt zero one)

/-- **The folds at the empty valuation**: every accumulator the polarity's
unit. -/
noncomputable def initAcc (pol : ℕ → Bool) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putAcc zero one f fun j => pol (j : ℕ) = false

/-- **The verdict the accumulators spell**: the chain from level `0`, closed
by the leaf flag – the value of the whole prefix once the register is
exhausted. -/
noncomputable def accVerdict (pol : ℕ → Bool) (f : dt.CtlIx → A) : Prop :=
  chainFrom pol (dt.readAcc one f) (dt.ctlBit one f dt.leafC) dt.ki 0

/-- **The folds at an increment's carry block**: the levels before the carry
keep their bit, the carry level absorbs the chain below it, the levels after
it reset. -/
noncomputable def carryAcc (pol : ℕ → Bool) (c : ℕ) (f : dt.CtlIx → A) :
    dt.CtlIx → A :=
  dt.putAcc zero one f fun j =>
    if (j : ℕ) < c then dt.readAcc one f (j : ℕ)
      else if (j : ℕ) = c then
        (if pol c = true then
            dt.readAcc one f c ∨
              chainFrom pol (dt.readAcc one f) (dt.ctlBit one f dt.leafC) dt.ki (c + 1)
          else
            dt.readAcc one f c ∧
              chainFrom pol (dt.readAcc one f) (dt.ctlBit one f dt.leafC) dt.ki (c + 1))
      else (pol (j : ℕ) = false)

variable {dt zero one}

/-- **What the initialized vector reads**: the polarity's unit at every
level, which is `DescriptiveComplexity.Draw.accCVal_bot`'s value. -/
theorem readAcc_initAcc (hzo : zero ≠ one) (pol : ℕ → Bool) (f : dt.CtlIx → A)
    {j : ℕ} (hj : j < dt.naDim) :
    dt.readAcc one (dt.initAcc zero one pol f) j ↔ (pol j = false) :=
  readAcc_putAcc hzo f _ hj

/-- **What the vector reads after a carry**: exactly the shape
`DescriptiveComplexity.Draw.accCVal_step` asks for. -/
theorem readAcc_carryAcc (hzo : zero ≠ one) (pol : ℕ → Bool) (c : ℕ)
    (f : dt.CtlIx → A) {j : ℕ} (hj : j < dt.naDim) :
    dt.readAcc one (dt.carryAcc zero one pol c f) j ↔
      (if j < c then dt.readAcc one f j
        else if j = c then
          (if pol c = true then
              dt.readAcc one f c ∨
                chainFrom pol (dt.readAcc one f) (dt.ctlBit one f dt.leafC) dt.ki (c + 1)
            else
              dt.readAcc one f c ∧
                chainFrom pol (dt.readAcc one f) (dt.ctlBit one f dt.leafC) dt.ki (c + 1))
        else (pol j = false)) :=
  readAcc_putAcc hzo f _ hj

/-! ### The same for a sub-fold

An element loop of an atom subroutine folds its own prefix – the defining
sentence's – over the `sac` slots, with its own leaf flag. The three updates
are the same three; only the family and the width change. -/

variable (dt zero one)

/-- **The sub-fold's leaf flag**: the value of a defining sentence's matrix at
the tuple the element loop has just read. -/
noncomputable def subLeafC : dt.CtlIx := dt.scratchC 4

/-- **Storing a sub-fold's leaf.** -/
noncomputable def setSubLeaf (b : Prop) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one dt.subLeafC b f

/-- **A sub-fold at its first tuple.** -/
noncomputable def initSac (pol : ℕ → Bool) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putSac zero one f fun j => pol (j : ℕ) = false

/-- **What a sub-fold concludes**: the chain from level `0`, closed by its
leaf flag. -/
noncomputable def sacVerdict (pol : ℕ → Bool) (f : dt.CtlIx → A) : Prop :=
  chainFrom pol (dt.readSac one f) (dt.ctlBit one f dt.subLeafC) dt.eDim 0

/-- **A sub-fold at a tuple successor**, the carry coordinate given. -/
noncomputable def carrySac (pol : ℕ → Bool) (c : ℕ) (f : dt.CtlIx → A) :
    dt.CtlIx → A :=
  dt.putSac zero one f fun j =>
    if (j : ℕ) < c then dt.readSac one f (j : ℕ)
      else if (j : ℕ) = c then
        (if pol c = true then
            dt.readSac one f c ∨
              chainFrom pol (dt.readSac one f) (dt.ctlBit one f dt.subLeafC)
                dt.eDim (c + 1)
          else
            dt.readSac one f c ∧
              chainFrom pol (dt.readSac one f) (dt.ctlBit one f dt.subLeafC)
                dt.eDim (c + 1))
      else (pol (j : ℕ) = false)

variable {dt zero one}

theorem sacC_ne_subLeafC (j : Fin dt.eDim) : dt.sacC j ≠ dt.subLeafC :=
  fun h => nomatch h

theorem subLeafC_ne_sacC (j : Fin dt.eDim) : dt.subLeafC ≠ dt.sacC j :=
  fun h => nomatch h

@[simp]
theorem ctlBit_setSubLeaf (hzo : zero ≠ one) (b : Prop) (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.setSubLeaf zero one b f) dt.subLeafC ↔ b :=
  ctlBit_setCtl_self hzo _ _ _

/-- A sub-fold's accumulators ride along a write of its leaf flag. -/
theorem readSac_setSubLeaf (b : Prop) (f : dt.CtlIx → A) (j : ℕ) :
    dt.readSac one (dt.setSubLeaf zero one b f) j ↔ dt.readSac one f j := by
  refine exists_congr fun h => ?_
  rw [setSubLeaf, setCtl_of_ne (sacC_ne_subLeafC (dt := dt) ⟨j, h⟩)]

/-- The loop's wide tuple rides along a write of a sub-fold's
accumulators. -/
theorem putSac_of_lvE (f : dt.CtlIx → A) (b : Fin dt.eDim → Prop) (j : Fin dt.eDim) :
    dt.putSac zero one f b (dt.lvE j) = f (dt.lvE j) :=
  putSac_of_not_sac fun _ => fun h => nomatch h

theorem readSac_carrySac (hzo : zero ≠ one) (pol : ℕ → Bool) (c : ℕ)
    (f : dt.CtlIx → A) {j : ℕ} (hj : j < dt.eDim) :
    dt.readSac one (dt.carrySac zero one pol c f) j ↔
      (if j < c then dt.readSac one f j
        else if j = c then
          (if pol c = true then
              dt.readSac one f c ∨
                chainFrom pol (dt.readSac one f) (dt.ctlBit one f dt.subLeafC)
                  dt.eDim (c + 1)
            else
              dt.readSac one f c ∧
                chainFrom pol (dt.readSac one f) (dt.ctlBit one f dt.subLeafC)
                  dt.eDim (c + 1))
        else (pol j = false)) :=
  readSac_putSac hzo f _ hj

/-- **A sub-fold's verdict is its fold**, by the same chain. -/
theorem sacVerdict_iff_foldFrom {α : Type} {le : α → α → Prop}
    {P : (Fin dt.eDim → α) → Prop} {pol : ℕ → Bool} {v : Fin dt.eDim → α}
    {f : dt.CtlIx → A}
    (hacc : ∀ j : ℕ, j < dt.eDim → (dt.readSac one f j ↔ accCVal pol P le j v))
    (hleaf : dt.ctlBit one f dt.subLeafC ↔ P v) :
    dt.sacVerdict one pol f ↔ foldFrom pol P le 0 v :=
  chainFrom_iff_foldFrom hacc hleaf 0

/-! ### What the two readings are worth -/

/-- **The verdict is the fold**: if the accumulators hold the contributions
and the leaf flag the matrix at the current valuation, the chain from level
`0` is the fold's value there – so the exit checkpoint's guard reads the
sweep's answer off the control. -/
theorem accVerdict_iff_foldFrom {α : Type} {le : α → α → Prop}
    {P : (Fin dt.ki → α) → Prop} {pol : ℕ → Bool} {v : Fin dt.ki → α}
    {f : dt.CtlIx → A}
    (hacc : ∀ j : ℕ, j < dt.ki → (dt.readAcc one f j ↔ accCVal pol P le j v))
    (hleaf : dt.ctlBit one f dt.leafC ↔ P v) :
    dt.accVerdict one pol f ↔ foldFrom pol P le 0 v :=
  chainFrom_iff_foldFrom hacc hleaf 0

section Leaf

variable [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable [LinearOrder (dt.X.Map A)]

omit [Finite A] [Nonempty A] in
/-- **The leaf flag's value is the matrix**: once every atom subroutine has
filed its verdict, the Boolean function the control computes is the matrix at
the atoms' readings – `DescriptiveComplexity.Draw.realize_iff_qfValue_holds`'s
right-hand side, which is what the machine's leaf must be. -/
theorem postLeaf_iff_qfValue {v : dt.VarIx} {f : dt.CtlIx → A}
    {σ : dt.d.B.Assignment (dt.X.Map A)} {w : Fin (dt.nOf v) → dt.X.Map A}
    (hav : ∀ k : Fin (dt.natOf v),
      dt.ctlBit one f (dt.avC (Fin.castLE (dt.natOf_le_natMax v) k)) ↔
        (dt.kindOf v k).holds σ w) :
    dt.postLeaf one v f ↔
      qfValue (dt.matOf v) fun a => (matAtom? a).elim False (MatAtom.holds σ w) := by
  refine qfValue_congr _ _ _ fun a ha => ?_
  obtain ⟨k, hk⟩ : ∃ k : Fin (dt.atomsOf v).length, (dt.atomsOf v).get k = a :=
    List.mem_iff_get.mp ha
  have hkind : matAtom? a = some (dt.kindOf v k) := hk ▸ dt.matAtom?_get v k
  rw [hkind]
  constructor
  · rintro ⟨k', hk', hbit⟩
    have hkind' : matAtom? a = some (dt.kindOf v k') := hk' ▸ dt.matAtom?_get v k'
    have hsame : dt.kindOf v k' = dt.kindOf v k :=
      Option.some.inj (hkind'.symm.trans hkind)
    exact hsame ▸ (hav k').mp hbit
  · intro hholds
    exact ⟨k, hk, (hav k).mpr hholds⟩

end Leaf

end Data

end Draw

end DescriptiveComplexity
