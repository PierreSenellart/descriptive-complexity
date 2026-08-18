/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefName

/-!
# A gate's four folds

What a gate block's element loop carries between rounds is a *composite* write:
started, it clears the loop element and sets the sub-fold to its polarity's
unit; advanced, it stores the leaf, folds at the carry coordinate and steps the
loop element; and its exit conjoins the sub-fold's verdict into the block's
flag.

Each is two or three writes nested, and what makes them definable is not new
machinery but the **commutations**: the three registers a gate writes –
the loop element, the sub-fold's accumulators, and the sub-leaf flag – are
disjoint, so each write reads what it was given. With those, the pieces are the
ones already discharged.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L}

/-! ### The three registers are disjoint -/

section Frame

theorem lvE_ne_sacC (j : Fin dt.eDim) (j' : Fin dt.eDim) :
    dt.lvE j ≠ dt.sacC j' := fun h => nomatch h

theorem lvE_ne_subLeafC (j : Fin dt.eDim) : dt.lvE j ≠ dt.subLeafC :=
  fun h => nomatch h

variable {A : Type} {zero one : A}

/-- The loop element rides along a write of the sub-fold. -/
theorem readLvE_putSac (f : dt.CtlIx → A) (b : Fin dt.eDim → Prop) :
    dt.readLvE (dt.putSac zero one f b) = dt.readLvE f :=
  funext fun j => putVec_of_not_mem fun j' => lvE_ne_sacC j j'

/-- And along a write of the sub-leaf flag. -/
theorem readLvE_setSubLeaf (f : dt.CtlIx → A) (b : Prop) :
    dt.readLvE (dt.setSubLeaf zero one b f) = dt.readLvE f :=
  funext fun j => setCtl_of_ne (zero := zero) (one := one) (lvE_ne_subLeafC j) b f

/-- The loop element rides along a fold at a carry. -/
theorem readLvE_carrySac (pol : ℕ → Bool) (c : ℕ) (f : dt.CtlIx → A) :
    dt.readLvE (dt.carrySac zero one pol c f) = dt.readLvE f :=
  readLvE_putSac f _

/-- The sub-fold's accumulators ride along a write of the sub-leaf flag. -/
theorem readSac_setSubLeaf' (f : dt.CtlIx → A) (b : Prop) :
    dt.readSac one (dt.setSubLeaf zero one b f) = dt.readSac one f :=
  funext fun j => propext (readSac_setSubLeaf (zero := zero) b f j)

end Frame

/-! ### Composing a write with a write -/

section Comp

variable [Fintype dt.SlotIx]

open Classical in
/-- **A vector write over a definable base**: the named slots take the bits of
the family, and every other slot is whatever the base left there. -/
theorem uStDefinable_putVec_comp {m : ℕ} {accs : Fin m → dt.CtlIx}
    (hinj : Function.Injective accs)
    {b : ∀ e : Env L, Fin m → (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : ∀ j : Fin m, UGDefinable fun e f g => b e j f g)
    {F : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → dt.CtlIx → e.α}
    (hF : UStDefinable F) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.putVec e.zero e.one accs (F e f g) fun j => b e j f g := by
  intro q
  by_cases hq : ∃ j : Fin m, q = accs j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_bitVal (hb j)).congr fun e f g => ?_
    have hex : ∃ j' : Fin m, accs j = accs j' := ⟨j, rfl⟩
    change (if h : ∃ j' : Fin m, accs j = accs j' then
      bitVal e.zero e.one (b e h.choose f g) else F e f g (accs j)) = _
    rw [dif_pos hex, hinj hex.choose_spec.symm]
  · refine (hF q).congr fun _ _ _ => ?_
    exact putVec_of_not_mem fun j hc => hq ⟨j, hc⟩

open Classical in
/-- **A loop-element write over a definable base.** -/
theorem uStDefinable_putLvE_comp
    {w : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Fin dt.eDim → e.α}
    (hw : ∀ j : Fin dt.eDim, USlotDefinable fun e f g => w e f g j)
    {F : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → dt.CtlIx → e.α}
    (hF : UStDefinable F) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.putLvE (F e f g) (w e f g) := by
  intro q
  by_cases hq : ∃ j : Fin dt.eDim, q = dt.lvE j
  · obtain ⟨j, rfl⟩ := hq
    refine (hw j).congr fun e f g => ?_
    exact congrFun (dt.readLvE_putLvE (F e f g) (w e f g)) j
  · refine (hF q).congr fun _ _ _ => ?_
    exact putLvE_of_not_lv fun j hc => hq ⟨j, hc⟩

/-! ### The three shapes a fold has

A gate block and an expansion atom fold the same way – only the prefix and the
leaf differ – so the three shapes are stated at an arbitrary polarity and an
arbitrary definable leaf, and each machinery instantiates them. -/

section Folds

variable [L.IsRelational]

omit [L.IsRelational] in
/-- **A sub-fold's verdict at a stored leaf is definable**: the accumulators
ride along the store, and the leaf it closes with is what was stored. -/
theorem uGDefinable_sacVerdict_setSubLeaf (pol : ℕ → Bool)
    {b : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.sacVerdict e.one pol (dt.setSubLeaf e.zero e.one (b e f g) f) :=
  (uGDefinable_chainFrom dt.sacC hb pol dt.eDim 0).congr fun e f g => by
    rw [sacVerdict, readSac_setSubLeaf', propext (ctlBit_setSubLeaf e.hzo _ _)]
    exact Iff.rfl

omit [L.IsRelational] in
/-- **A loop started is definable**: the loop element cleared and the sub-fold
at its polarity's unit. -/
theorem uStDefinable_initSac_initLvE (pol : ℕ → Bool) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.initSac e.zero e.one pol (dt.initLvE f) :=
  uStDefinable_putVec_comp dt.sacC_injective
    (fun j => uGDefinable_const (pol (j : ℕ) = false)) uStDefinable_initLvE

omit [L.IsRelational] in
/-- **A conjoining exit is definable**: the leaf stored, and a flag written
from a question the caller supplies. -/
theorem uStDefinable_setCtl_setSubLeaf (q : dt.CtlIx)
    {b N : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) (hN : UGDefinable N) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.setCtl e.zero e.one q (N e f g) (dt.setSubLeaf e.zero e.one (b e f g) f) :=
  (uStDefinable_setSubLeaf hb).update q (uSlotDefinable_bitVal hN)

omit [L.IsRelational] in
/-- **A round, folded and advanced, is definable.** Three writes nested – the
leaf stored, the sub-fold folded at its carry, the loop element stepped – and
three commutations: the fold does not touch the loop element, the store touches
neither the accumulators nor it, so each write reads what it was given, and the
carry itself is a question about which coordinates are maximal. -/
theorem uStDefinable_advSac (pol : ℕ → Bool)
    {b : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.advLvE (dt.carrySac e.zero e.one pol (tupCarry (dt.readLvE f))
        (dt.setSubLeaf e.zero e.one (b e f g) f)) := by
  classical
  have hbody : ∀ (c₀ : Fin (dt.eDim + 1)) (j : Fin dt.eDim),
      UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
        (if (j : ℕ) < (c₀ : ℕ) then dt.readSac e.one f (j : ℕ)
          else if (j : ℕ) = (c₀ : ℕ) then
            (if pol (c₀ : ℕ) = true then
                dt.readSac e.one f (c₀ : ℕ) ∨
                  chainFrom pol (dt.readSac e.one f) (b e f g) dt.eDim ((c₀ : ℕ) + 1)
              else
                dt.readSac e.one f (c₀ : ℕ) ∧
                  chainFrom pol (dt.readSac e.one f) (b e f g) dt.eDim ((c₀ : ℕ) + 1))
          else (pol (j : ℕ) = false)) := by
    intro c₀ j
    exact UGDefinable.ite (p := (j : ℕ) < (c₀ : ℕ)) (uGDefinable_readSac (j : ℕ))
      (UGDefinable.ite (p := (j : ℕ) = (c₀ : ℕ))
        (UGDefinable.ite (p := pol (c₀ : ℕ) = true)
          ((uGDefinable_readSac (c₀ : ℕ)).or
            (uGDefinable_chainFrom dt.sacC hb pol dt.eDim ((c₀ : ℕ) + 1)))
          ((uGDefinable_readSac (c₀ : ℕ)).and
            (uGDefinable_chainFrom dt.sacC hb pol dt.eDim ((c₀ : ℕ) + 1))))
        (uGDefinable_const (pol (j : ℕ) = false)))
  have hb' : ∀ j : Fin dt.eDim,
      UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
        (if (j : ℕ) < tupCarry (dt.readLvE f) then dt.readSac e.one f (j : ℕ)
          else if (j : ℕ) = tupCarry (dt.readLvE f) then
            (if pol (tupCarry (dt.readLvE f)) = true then
                dt.readSac e.one f (tupCarry (dt.readLvE f)) ∨
                  chainFrom pol (dt.readSac e.one f) (b e f g) dt.eDim
                    (tupCarry (dt.readLvE f) + 1)
              else
                dt.readSac e.one f (tupCarry (dt.readLvE f)) ∧
                  chainFrom pol (dt.readSac e.one f) (b e f g) dt.eDim
                    (tupCarry (dt.readLvE f) + 1))
          else (pol (j : ℕ) = false)) := by
    intro j
    refine (uGDefinable_exists fun c₀ : Fin (dt.eDim + 1) =>
      (uGDefinable_tupCarry_eq (dt := dt) (c₀ : ℕ)).and (hbody c₀ j)).congr
      fun e f g => ?_
    constructor
    · intro hbdy
      exact ⟨⟨tupCarry (dt.readLvE f), Nat.lt_succ_of_le tupCarry_le⟩, rfl, hbdy⟩
    · rintro ⟨c₀, hc, hbdy⟩
      rwa [hc]
  have hbase : UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.carrySac e.zero e.one pol (tupCarry (dt.readLvE f))
        (dt.setSubLeaf e.zero e.one (b e f g) f) := by
    refine (uStDefinable_putVec_comp dt.sacC_injective hb'
      (uStDefinable_setSubLeaf hb)).congr fun e f g q => ?_
    rw [carrySac, readSac_setSubLeaf', propext (ctlBit_setSubLeaf e.hzo _ _)]
    rfl
  refine (uStDefinable_putLvE_comp (w := fun e (f : dt.CtlIx → e.α) _ =>
    tupNext (dt.readLvE f)) (fun j => uSlotDefinable_tupNext_lvE j) hbase).congr
    fun e f g q => ?_
  rw [advLvE, readLvE_carrySac, readLvE_setSubLeaf]

/-! ### A gate's four folds -/

omit [L.IsRelational] in
/-- **A gate's domain loop, started.** -/
theorem uStDefinable_gateInit (t : dt.X.Tag) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.gateInit e.zero e.one t f :=
  uStDefinable_initSac_initLvE (dt.domPk t).pol

/-- **A gate's domain round, folded and advanced.** -/
theorem uStDefinable_gateAdv (t : dt.X.Tag) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.gateAdv e.zero e.one t hn hrd f :=
  uStDefinable_advSac (dt.domPk t).pol (uGDefinable_domLeafVal t hn hrd)

/-- **A gate's conjoining exit**: the leaf stored, and the block's flag
conjoined with the decoding and the sub-fold's verdict. -/
theorem uStDefinable_gateExit (t : dt.X.Tag)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.gateExit e.zero e.one t hc hn hrd f :=
  uStDefinable_setCtl_setSubLeaf dt.gateFlagC (uGDefinable_domLeafVal t hn hrd)
    ((uGDefinable_ctlBit dt.gateFlagC).and
      ((uGDefinable_gateTagsAre hc t).and
        (uGDefinable_sacVerdict_setSubLeaf (dt.domPk t).pol
          (uGDefinable_domLeafVal t hn hrd))))

/-- **An inner gate's conjoining exit**, the same into the level's flag. -/
theorem uStDefinable_igateExit (flag : dt.CtlIx) (t : dt.X.Tag)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.igateExit e.zero e.one flag t hc hn hrd f :=
  uStDefinable_setCtl_setSubLeaf flag (uGDefinable_domLeafVal t hn hrd)
    ((uGDefinable_ctlBit flag).and
      ((uGDefinable_gateTagsAre hc t).and
        (uGDefinable_sacVerdict_setSubLeaf (dt.domPk t).pol
          (uGDefinable_domLeafVal t hn hrd))))

end Folds

end Comp

end Data

end Draw

end DescriptiveComplexity
