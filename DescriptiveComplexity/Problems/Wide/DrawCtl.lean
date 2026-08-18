/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawData

/-!
# The control's dictionary: which slot plays which role

The program's states carry a pointer `f : dt.CtlIx → A`, and every semantic
parameter of the machinery – the coordinates a name guard compares against,
the accumulators the folds update, the flags a verdict is stored in – is a
*designation* of some of its slots. This file fixes them, once, with the
casts through the budgets that `DescriptiveComplexity.Draw.DrawData.eDim` and
friends were computed for:

| role | slots |
|---|---|
| the coordinates of the current loop element | `lvC` (the first `dd₀` of the `lv` family) |
| the inner fold's accumulators | `accC` |
| an element loop's sub-fold accumulators | `sacC` |
| the verdicts of the matrix's atoms | `avC` |
| the leaf reads of the current round | `rdfC` |
| the tag witnesses | `tgfC` |
| the gates' verdict, a copied bit, two scratch | `gateFlagC`, `bitFlagC`, `scratchC` |

and the two operations every parameter is built from: reading a slot as a
bit, and writing one (`DescriptiveComplexity.Draw.DrawData.ctlBit` and
`setCtl`), with their read-back equations. Nothing here is about the tape;
the machinery's `dstSt` parameters are functions of the pointer alone, and
this is their vocabulary.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A : Type}

/-! ### The designations -/

/-- **The coordinates of the loop element**: the first `dd₀` loop-variable
slots. A name guard compares a cell's name slots against these, so they are
the `coord` of every read and write trip. -/
noncomputable def lvC (j : Fin dt.dd0) : dt.CtlIx :=
  .lv (Fin.castLE dt.dd0_le_eDim j)

/-- **The inner fold's accumulators**: one per level of the quantifier
prefix, and one over. -/
noncomputable def accC (j : Fin dt.naDim) : dt.CtlIx := .acc j

/-- **A sub-fold's accumulators**: one per level of an element loop's own
prefix. -/
noncomputable def sacC (j : Fin dt.eDim) : dt.CtlIx := .sac j

/-- **The verdict of an atom of the matrix.** -/
noncomputable def avC (a : Fin dt.natMax) : dt.CtlIx := .av a

/-- **The verdict of a leaf read** of the current element-loop round. -/
noncomputable def rdfC (a : Fin dt.nfDim) : dt.CtlIx := .rdf a

/-- **A tag-witness flag.** -/
noncomputable def tgfC (a : Fin dt.ntgDim) : dt.CtlIx := .tgf a

/-- **The gates' verdict flag**: cleared by a failing block, read by the
verdict checkpoint. -/
noncomputable def gateFlagC : dt.CtlIx := .flag 0

/-- **The copied bit** of a tuple loop: written by the read trip's verdict
exit, read back by the write trip. -/
noncomputable def bitFlagC : dt.CtlIx := .flag 1

/-- The remaining scratch flags: the last leaf's value, the comparison
loops' accumulator and their two verdict bits, and two spare. -/
noncomputable def scratchC (k : Fin 6) : dt.CtlIx := .flag (k.addNat 2)

/-- **The ∃-levels' gate flag of a VAL round**: the conjunction, over the
existentially quantified levels of the variable's pack, of "this level's
inner block is an encoding". The last free scratch flag. -/
noncomputable def existGateC : dt.CtlIx := .flag 7

/-- **The ∀-levels' gate flag of a VAL round**: the same conjunction over
the universally quantified levels. Reuses the outer gates' flag, which is
dead once the verdict checkpoint has dispatched on it — nothing inside the
VAL loop reads it again. -/
noncomputable def allGateC : dt.CtlIx := .flag 0

theorem scratchC_injective : Function.Injective dt.scratchC := by
  intro k k' h
  have h' : k.addNat 2 = k'.addNat 2 := by injection h
  exact Fin.ext (by simpa using congrArg Fin.val h')

theorem gateFlagC_ne_scratchC (k : Fin 6) : dt.gateFlagC ≠ dt.scratchC k := by
  intro h
  have h' : (0 : Fin 8) = k.addNat 2 := by injection h
  exact absurd (congrArg Fin.val h') (by simp)

theorem bitFlagC_ne_scratchC (k : Fin 6) : dt.bitFlagC ≠ dt.scratchC k := by
  intro h
  have h' : (1 : Fin 8) = k.addNat 2 := by injection h
  exact absurd (congrArg Fin.val h') (by simp)

/-! ### Distinctness

The roles are disjoint families of the same inductive, so telling them apart
is a matter of constructors – except inside a family, where it is the index.
These are the facts an update needs: writing one slot leaves the others
alone. -/

theorem lvC_injective : Function.Injective dt.lvC := by
  intro j j' h
  have h' : Fin.castLE dt.dd0_le_eDim j = Fin.castLE dt.dd0_le_eDim j' := by
    injection h
  exact Fin.ext (by simpa using congrArg Fin.val h')

theorem accC_injective : Function.Injective dt.accC := by
  intro j j' h
  injection h

theorem avC_injective : Function.Injective dt.avC := by
  intro a a' h
  injection h

theorem rdfC_injective : Function.Injective dt.rdfC := by
  intro a a' h
  injection h

theorem tgfC_injective : Function.Injective dt.tgfC := by
  intro a a' h
  injection h

theorem lvC_ne_accC (j : Fin dt.dd0) (k : Fin dt.naDim) : dt.lvC j ≠ dt.accC k :=
  fun h => nomatch h

theorem lvC_ne_avC (j : Fin dt.dd0) (a : Fin dt.natMax) : dt.lvC j ≠ dt.avC a :=
  fun h => nomatch h

theorem lvC_ne_rdfC (j : Fin dt.dd0) (a : Fin dt.nfDim) : dt.lvC j ≠ dt.rdfC a :=
  fun h => nomatch h

theorem lvC_ne_gateFlagC (j : Fin dt.dd0) : dt.lvC j ≠ dt.gateFlagC :=
  fun h => nomatch h

theorem lvC_ne_bitFlagC (j : Fin dt.dd0) : dt.lvC j ≠ dt.bitFlagC :=
  fun h => nomatch h

theorem accC_ne_avC (k : Fin dt.naDim) (a : Fin dt.natMax) :
    dt.accC k ≠ dt.avC a := fun h => nomatch h

theorem accC_ne_gateFlagC (k : Fin dt.naDim) : dt.accC k ≠ dt.gateFlagC :=
  fun h => nomatch h

theorem avC_ne_rdfC (a : Fin dt.natMax) (a' : Fin dt.nfDim) :
    dt.avC a ≠ dt.rdfC a' := fun h => nomatch h

theorem avC_ne_gateFlagC (a : Fin dt.natMax) : dt.avC a ≠ dt.gateFlagC :=
  fun h => nomatch h

theorem rdfC_ne_gateFlagC (a : Fin dt.nfDim) : dt.rdfC a ≠ dt.gateFlagC :=
  fun h => nomatch h

theorem gateFlagC_ne_bitFlagC : dt.gateFlagC ≠ dt.bitFlagC := by
  intro h
  have h' : (0 : Fin 8) = 1 := by injection h
  exact absurd (congrArg Fin.val h') (by decide)

/-! ### Reading and writing one slot -/

variable (zero one : A)

/-- **A control slot, read as a bit.** -/
def ctlBit (f : dt.CtlIx → A) (q : dt.CtlIx) : Prop := f q = one

/-- **A control slot, written**: the pointer with one slot set to a bit. -/
noncomputable def setCtl (q : dt.CtlIx) (b : Prop) (f : dt.CtlIx → A) :
    dt.CtlIx → A :=
  Function.update f q (bitVal zero one b)

variable {dt zero one}

@[simp]
theorem ctlBit_setCtl_self (hzo : zero ≠ one) (q : dt.CtlIx) (b : Prop)
    (f : dt.CtlIx → A) : dt.ctlBit one (dt.setCtl zero one q b f) q ↔ b := by
  classical
  change Function.update f q (bitVal zero one b) q = one ↔ b
  rw [Function.update_self]
  exact bitVal_iff hzo

@[simp]
theorem ctlBit_setCtl_of_ne {q q' : dt.CtlIx} (hne : q' ≠ q) (b : Prop)
    (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.setCtl zero one q b f) q' ↔ dt.ctlBit one f q' := by
  classical
  change Function.update f q (bitVal zero one b) q' = one ↔ f q' = one
  rw [Function.update_of_ne hne]

/-- A write leaves the other slots' *values* alone, not only their bits. -/
theorem setCtl_of_ne {q q' : dt.CtlIx} (hne : q' ≠ q) (b : Prop)
    (f : dt.CtlIx → A) : dt.setCtl zero one q b f q' = f q' := by
  classical
  exact Function.update_of_ne hne _ _

/-- Two writes to distinct slots commute. -/
theorem setCtl_comm {q q' : dt.CtlIx} (hne : q ≠ q') (b b' : Prop)
    (f : dt.CtlIx → A) :
    dt.setCtl zero one q b (dt.setCtl zero one q' b' f) =
      dt.setCtl zero one q' b' (dt.setCtl zero one q b f) := by
  classical
  change Function.update (Function.update f q' _) q _ =
    Function.update (Function.update f q _) q' _
  exact Function.update_comm hne.symm _ _ f

end DrawData

/-! ### The tuple enumeration

An element loop runs over the tuples of source elements in the
lexicographic order, one coordinatewise successor per round
(`DescriptiveComplexity.TupSucc`, which
`DescriptiveComplexity.Draw.reflTransGen_of_tupLoop` indexes its rounds by).
The loop's three semantic parameters are the *functions* behind that
relation: where it starts, what it advances to, and when it is done. -/

section Tuple

variable {D : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The tuple is exhausted**: every coordinate is maximal, i.e. it is the
lexicographic top. -/
def IsMaxTup (t : Fin D → A) : Prop := ∀ (p : Fin D) (a : A), a ≤ t p

/-- **A non-exhausted tuple has a successor.** -/
theorem exists_tupSucc_of_not_isMaxTup {t : Fin D → A} (h : ¬IsMaxTup t) :
    ∃ w : Fin D → A, TupSucc t w := by
  classical
  obtain ⟨w, hw, hnb⟩ :=
    exists_gt_of_not_max (z := toLex t) (fun hc => h (tup_isTop_iff.mp hc))
  exact ⟨ofLex w, tupSucc_iff_covBy.mpr ⟨hw, fun c hc1 hc2 => hnb c ⟨hc1, hc2⟩⟩⟩

open Classical in
/-- **The next tuple**, the lexicographic successor – itself at the top,
where no round follows. -/
noncomputable def tupNext (t : Fin D → A) : Fin D → A :=
  if h : ∃ w : Fin D → A, TupSucc t w then h.choose else t

/-- Below the top, the next tuple is a successor. -/
theorem tupSucc_tupNext {t : Fin D → A} (h : ¬IsMaxTup t) :
    TupSucc t (tupNext t) := by
  classical
  have hex := exists_tupSucc_of_not_isMaxTup h
  rw [tupNext, dif_pos hex]
  exact hex.choose_spec

/-! ### The coordinate a round carries

A fold's update rule needs to know **which coordinate rolled over**, and the
loop's control does: it is the greatest non-maximal coordinate of the tuple,
which is the witness of `DescriptiveComplexity.TupSucc` – unique, so the
machine's `dstSt` may name it. -/

/-- The body of `DescriptiveComplexity.TupSucc` at a named coordinate. -/
def TupSuccAt (p : Fin D) (t t' : Fin D → A) : Prop :=
  (∀ j, j < p → t j = t' j) ∧
    (t p < t' p ∧ ∀ a : A, ¬(t p < a ∧ a < t' p)) ∧
    ∀ j, p < j → (∀ a : A, a ≤ t j) ∧ (∀ a : A, t' j ≤ a)

omit [Finite A] in
theorem tupSucc_iff_exists_at (t t' : Fin D → A) :
    TupSucc t t' ↔ ∃ p : Fin D, TupSuccAt p t t' := Iff.rfl

omit [Finite A] in
/-- **The carried coordinate is unique**: above it every coordinate is
already maximal, and it is not. -/
theorem tupSuccAt_unique {p p' : Fin D} {t t' : Fin D → A}
    (h : TupSuccAt p t t') (h' : TupSuccAt p' t t') : p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hlt
  · exact absurd ((h.2.2 p' hlt).1 (t' p')) (not_le_of_gt h'.2.1.1)
  · exact heq
  · exact absurd ((h'.2.2 p hlt).1 (t' p)) (not_le_of_gt h.2.1.1)

open Classical in
/-- **The coordinate a round carries**, read off the tuple – as a level
index, so that a fold's rules may use it directly; at the top, where no round
follows, it is past the last coordinate. -/
noncomputable def tupCarry (t : Fin D → A) : ℕ :=
  if h : ∃ p : Fin D, TupSuccAt p t (tupNext t) then ((h.choose : Fin D) : ℕ) else D

omit [Finite A] in
/-- **What the carried coordinate is**: the witness of the tuple's step,
which is unique. -/
theorem tupCarry_eq {t : Fin D → A} {p : Fin D}
    (hp : TupSuccAt p t (tupNext t)) : tupCarry t = (p : ℕ) := by
  classical
  have hex : ∃ p : Fin D, TupSuccAt p t (tupNext t) := ⟨p, hp⟩
  rw [tupCarry, dif_pos hex]
  exact congrArg Fin.val (tupSuccAt_unique hex.choose_spec hp)

/-- **Below the top the carried coordinate is a level**, and the round steps
there. -/
theorem tupSuccAt_tupCarry [Nonempty A] {t : Fin D → A} (h : ¬IsMaxTup t) :
    ∃ p : Fin D, (p : ℕ) = tupCarry t ∧ TupSuccAt p t (tupNext t) := by
  obtain ⟨p, hp⟩ : ∃ p : Fin D, TupSuccAt p t (tupNext t) := tupSucc_tupNext h
  exact ⟨p, (tupCarry_eq hp).symm, hp⟩

/-- **The first tuple**: every coordinate the least element. -/
noncomputable def botTup [Nonempty A] : Fin D → A :=
  letI := Fintype.ofFinite A
  fun _ => Finset.univ.min' Finset.univ_nonempty

theorem botTup_le [Nonempty A] (p : Fin D) (a : A) : (botTup : Fin D → A) p ≤ a :=
  letI := Fintype.ofFinite A
  Finset.min'_le _ a (Finset.mem_univ a)

end Tuple

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A : Type}

/-! ### The loop element, read and written

Two widths, one family of slots: an element loop of an expansion atom or a
domain gate enumerates the whole prefix of its defining sentence – up to
`eDim` coordinates – while a coordinate loop (a block copy, a comparison)
enumerates the `dd₀` coordinates a cell's name carries. The first `dd₀` slots
of the wide tuple are the narrow one (`lvC_eq_lvE`), so a leaf read of a wide
loop names its cell from the coordinates it computes and a leaf read of a
narrow one from the slots directly. -/

/-- **The loop element's coordinates**, read out of the control. -/
noncomputable def readLv (f : dt.CtlIx → A) : Fin dt.dd0 → A :=
  fun j => f (dt.lvC j)

open Classical in
/-- **The loop element's coordinates, written**: the pointer with the
loop-variable slots set to a tuple. -/
noncomputable def putLv (f : dt.CtlIx → A) (w : Fin dt.dd0 → A) : dt.CtlIx → A :=
  fun q => if h : ∃ j : Fin dt.dd0, q = dt.lvC j then w h.choose else f q

variable {dt}

theorem putLv_of_not_lv {f : dt.CtlIx → A} {w : Fin dt.dd0 → A} {q : dt.CtlIx}
    (h : ∀ j : Fin dt.dd0, q ≠ dt.lvC j) : dt.putLv f w q = f q := by
  classical
  rw [putLv, dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj

@[simp]
theorem readLv_putLv (f : dt.CtlIx → A) (w : Fin dt.dd0 → A) :
    dt.readLv (dt.putLv f w) = w := by
  classical
  funext j
  have hex : ∃ j' : Fin dt.dd0, dt.lvC j = dt.lvC j' := ⟨j, rfl⟩
  change (if h : ∃ j' : Fin dt.dd0, dt.lvC j = dt.lvC j' then w h.choose else _) = w j
  rw [dif_pos hex]
  exact congrArg w (dt.lvC_injective hex.choose_spec).symm

/-- The other slots ride along a write of the loop element. -/
theorem putLv_flag (f : dt.CtlIx → A) (w : Fin dt.dd0 → A) :
    dt.putLv f w dt.gateFlagC = f dt.gateFlagC :=
  putLv_of_not_lv fun _ => fun h => nomatch h

theorem putLv_acc (f : dt.CtlIx → A) (w : Fin dt.dd0 → A) (k : Fin dt.naDim) :
    dt.putLv f w (dt.accC k) = f (dt.accC k) :=
  putLv_of_not_lv fun _ => fun h => nomatch h

theorem putLv_av (f : dt.CtlIx → A) (w : Fin dt.dd0 → A) (a : Fin dt.natMax) :
    dt.putLv f w (dt.avC a) = f (dt.avC a) :=
  putLv_of_not_lv fun _ => fun h => nomatch h

variable (dt)

/-- **A loop variable of an element loop**, at the full width. -/
noncomputable def lvE (j : Fin dt.eDim) : dt.CtlIx := .lv j

theorem lvE_injective : Function.Injective dt.lvE := by
  intro j j' h
  injection h

theorem lvC_eq_lvE (j : Fin dt.dd0) :
    dt.lvC j = dt.lvE (Fin.castLE dt.dd0_le_eDim j) := rfl

/-- **The wide loop element**, read out of the control. -/
noncomputable def readLvE (f : dt.CtlIx → A) : Fin dt.eDim → A :=
  fun j => f (dt.lvE j)

open Classical in
/-- **The wide loop element, written.** -/
noncomputable def putLvE (f : dt.CtlIx → A) (w : Fin dt.eDim → A) : dt.CtlIx → A :=
  fun q => if h : ∃ j : Fin dt.eDim, q = dt.lvE j then w h.choose else f q

variable {dt}

theorem putLvE_of_not_lv {f : dt.CtlIx → A} {w : Fin dt.eDim → A} {q : dt.CtlIx}
    (h : ∀ j : Fin dt.eDim, q ≠ dt.lvE j) : dt.putLvE f w q = f q := by
  classical
  rw [putLvE, dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj

@[simp]
theorem readLvE_putLvE (f : dt.CtlIx → A) (w : Fin dt.eDim → A) :
    dt.readLvE (dt.putLvE f w) = w := by
  classical
  funext j
  have hex : ∃ j' : Fin dt.eDim, dt.lvE j = dt.lvE j' := ⟨j, rfl⟩
  change (if h : ∃ j' : Fin dt.eDim, dt.lvE j = dt.lvE j' then w h.choose else _) = w j
  rw [dif_pos hex]
  exact congrArg w (dt.lvE_injective hex.choose_spec).symm

/-- The narrow tuple is the first coordinates of the wide one. -/
theorem readLv_eq_readLvE (f : dt.CtlIx → A) (j : Fin dt.dd0) :
    dt.readLv f j = dt.readLvE f (Fin.castLE dt.dd0_le_eDim j) := rfl

/-- The accumulators, the verdicts and the flags ride along a write of the
wide loop element. -/
theorem putLvE_acc (f : dt.CtlIx → A) (w : Fin dt.eDim → A) (k : Fin dt.naDim) :
    dt.putLvE f w (dt.accC k) = f (dt.accC k) :=
  putLvE_of_not_lv fun _ => fun h => nomatch h

theorem putLvE_av (f : dt.CtlIx → A) (w : Fin dt.eDim → A) (a : Fin dt.natMax) :
    dt.putLvE f w (dt.avC a) = f (dt.avC a) :=
  putLvE_of_not_lv fun _ => fun h => nomatch h

theorem putLvE_flag (f : dt.CtlIx → A) (w : Fin dt.eDim → A) (k : Fin 8) :
    dt.putLvE f w (Ctl.flag k) = f (Ctl.flag k) :=
  putLvE_of_not_lv fun _ => fun h => nomatch h

variable (dt)

/-! ### The loop's three operations

`DescriptiveComplexity.Draw.tupNext` and friends, in the slots: where a loop
starts, what it advances to, and when it is done – the `initEl`/`advEl`/
`IsMaxEl` of every element loop, at either width. -/

variable [LinearOrder A] [Finite A] [Nonempty A]

/-- **The wide loop, started.** -/
noncomputable def initLvE (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putLvE f botTup

/-- **The wide loop, advanced.** -/
noncomputable def advLvE (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putLvE f (tupNext (dt.readLvE f))

/-- **The wide loop, exhausted.** -/
def IsMaxLvE (f : dt.CtlIx → A) : Prop := IsMaxTup (dt.readLvE f)

/-- **The narrow loop, started.** -/
noncomputable def initLvN (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putLv f botTup

/-- **The narrow loop, advanced.** -/
noncomputable def advLvN (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.putLv f (tupNext (dt.readLv f))

/-- **The narrow loop, exhausted.** -/
def IsMaxLvN (f : dt.CtlIx → A) : Prop := IsMaxTup (dt.readLv f)

variable {dt}

@[simp]
theorem readLvE_initLvE (f : dt.CtlIx → A) : dt.readLvE (dt.initLvE f) = botTup :=
  readLvE_putLvE f _

@[simp]
theorem readLv_initLvN (f : dt.CtlIx → A) : dt.readLv (dt.initLvN f) = botTup :=
  readLv_putLv f _

omit [Nonempty A] in
/-- **A round of the wide loop steps the tuple**, below the top. -/
theorem tupSucc_advLvE {f : dt.CtlIx → A} (h : ¬dt.IsMaxLvE f) :
    TupSucc (dt.readLvE f) (dt.readLvE (dt.advLvE f)) := by
  rw [advLvE, readLvE_putLvE]
  exact tupSucc_tupNext h

omit [Nonempty A] in
/-- **A round of the narrow loop steps the tuple**, below the top. -/
theorem tupSucc_advLvN {f : dt.CtlIx → A} (h : ¬dt.IsMaxLvN f) :
    TupSucc (dt.readLv f) (dt.readLv (dt.advLvN f)) := by
  rw [advLvN, readLv_putLv]
  exact tupSucc_tupNext h

end DrawData

end Draw

end DescriptiveComplexity
