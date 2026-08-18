/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefAsm
import DescriptiveComplexity.Problems.Wide.DrawCtl

/-!
# The loop variables are definable: the one write that is not a copy

Everything the EXPSPACE program writes is a copy of one of its slots or one of
the two designated elements – *except* the loop advance. A loop element is a
tuple over the instance, and advancing it is
`DescriptiveComplexity.Draw.tupNext`, the lexicographic successor: the
coordinates below the one that rolls over keep their value, the one that rolls
over takes the **next** element of the order, and the ones above it reset.

Two things make that definable all the same.

* Which coordinate rolls over is decided by *which coordinates are maximal*,
  and that is in the equality pattern – so the case split is read off the
  pattern (`DescriptiveComplexity.Draw.uSlotDefinable_cases`).
* The value at the carry is `DescriptiveComplexity.ordSucc` of a single
  coordinate, which is exactly the source `DescriptiveComplexity.SlotVal.succ`
  names.

`DescriptiveComplexity.Draw.tupNext_apply_of_carry` is the coordinatewise
reading of `tupNext`, and the three statements after it are what a variable's
pack owes for its loop: the loop started, the loop advanced, and the loop
exhausted – at both widths.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### `tupNext`, coordinate by coordinate -/

section TupNext

variable {A : Type} [LinearOrder A] [Finite A] {D : ℕ} {zero one : A}

omit [Finite A] in
/-- **Being exhausted is holding the greatest element everywhere.** -/
theorem isMaxTup_iff_eq_top (ht : IsTop one) (t : Fin D → A) :
    IsMaxTup t ↔ ∀ p : Fin D, t p = one :=
  forall_congr' fun _ =>
    ⟨fun h => le_antisymm (ht _) (h one), fun h a => h ▸ ht a⟩

omit [Finite A] in
/-- **An exhausted tuple stands still.** -/
theorem tupNext_of_isMaxTup {t : Fin D → A} (h : IsMaxTup t) : tupNext t = t := by
  classical
  rw [tupNext, dif_neg]
  rintro ⟨w, p, hp⟩
  exact absurd (h p (w p)) (not_le.mpr hp.2.1.1)

omit [Finite A] in
/-- **The carry coordinate is unique**, being the greatest non-maximal one. -/
private theorem carry_unique {t : Fin D → A} {p p' : Fin D} (hp : ¬IsTop (t p))
    (hab : ∀ j : Fin D, p < j → IsTop (t j)) (hh : TupSuccAt p' t (tupNext t)) :
    p' = p := by
  have hp' : ¬IsTop (t p') := fun hc =>
    absurd (hc (tupNext t p')) (not_le.mpr hh.2.1.1)
  rcases lt_trichotomy p' p with hlt | heq | hlt
  · exact absurd (fun a => (hh.2.2 p hlt).1 a) hp
  · exact heq
  · exact absurd (hab p' hlt) hp'

omit [Finite A] in
/-- In a linear order, being a maximum is being *the* designated maximum. -/
private theorem isTop_iff' (ht : IsTop one) (a : A) : IsTop a ↔ a = one :=
  ⟨fun h => le_antisymm (ht a) (h one), fun h => h ▸ ht⟩

/-- **A tuple below the top steps at its carry coordinate.** -/
theorem tupSuccAt_of_carry {t : Fin D → A} {p : Fin D} (hp : ¬IsTop (t p))
    (hab : ∀ j : Fin D, p < j → IsTop (t j)) : TupSuccAt p t (tupNext t) := by
  have hnm : ¬IsMaxTup t := fun hc => hp fun a => hc p a
  obtain ⟨p', hh0⟩ : ∃ p' : Fin D, TupSuccAt p' t (tupNext t) := tupSucc_tupNext hnm
  exact carry_unique hp hab hh0 ▸ hh0

/-- **And the coordinate it carries is that one.** -/
theorem tupCarry_of_carry {t : Fin D → A} {p : Fin D} (hp : ¬IsTop (t p))
    (hab : ∀ j : Fin D, p < j → IsTop (t j)) : tupCarry t = (p : ℕ) :=
  tupCarry_eq (tupSuccAt_of_carry hp hab)

omit [Finite A] in
/-- **An exhausted tuple carries past its last coordinate.** -/
theorem tupCarry_of_isMaxTup {t : Fin D → A} (h : IsMaxTup t) : tupCarry t = D := by
  classical
  rw [tupCarry, dif_neg]
  rintro ⟨p, hp⟩
  exact absurd (h p (tupNext t p)) (not_le.mpr hp.2.1.1)

omit [Finite A] in
/-- **The carry never passes the last coordinate.** -/
theorem tupCarry_le {t : Fin D → A} : tupCarry t ≤ D := by
  classical
  rw [tupCarry]
  by_cases h : ∃ p : Fin D, TupSuccAt p t (tupNext t)
  · rw [dif_pos h]
    exact le_of_lt h.choose.isLt
  · rw [dif_neg h]

/-- **The next tuple, coordinate by coordinate**: below the carry a copy, at
the carry the next element, above it the least one. This is the reading the
interpretation writes down. -/
theorem tupNext_apply_of_carry (hb : IsBot zero)
    {t : Fin D → A} {p : Fin D} (hp : ¬IsTop (t p))
    (hab : ∀ j : Fin D, p < j → IsTop (t j)) (j : Fin D) :
    tupNext t j = if j < p then t j else if j = p then ordSucc (t j) else zero := by
  have hh : TupSuccAt p t (tupNext t) := tupSuccAt_of_carry hp hab
  rcases lt_trichotomy j p with hlt | heq | hlt
  · rw [if_pos hlt]
    exact (hh.1 j hlt).symm
  · subst heq
    rw [if_neg (lt_irrefl j), if_pos rfl]
    exact eq_ordSucc_of_covBy ⟨hh.2.1.1, fun c hc1 hc2 => hh.2.1.2 c ⟨hc1, hc2⟩⟩
  · rw [if_neg (not_lt.mpr hlt.le), if_neg (Fin.ne_of_gt hlt)]
    exact le_antisymm ((hh.2.2 j hlt).2 zero) (hb _)

omit [Finite A] in
/-- **A tuple that is not exhausted has a carry coordinate.** -/
theorem exists_carry (ht : IsTop one) {t : Fin D → A} (h : ¬IsMaxTup t) :
    ∃ p : Fin D, t p ≠ one ∧ ∀ j : Fin D, p < j → t j = one := by
  classical
  have hne : (Finset.univ.filter fun p : Fin D => t p ≠ one).Nonempty := by
    by_contra hc
    refine h ((isMaxTup_iff_eq_top ht t).mpr fun p => ?_)
    by_contra hp
    exact hc ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
  refine ⟨(Finset.univ.filter fun p : Fin D => t p ≠ one).max' hne, ?_, fun j hj => ?_⟩
  · exact (Finset.mem_filter.mp
      ((Finset.univ.filter fun p : Fin D => t p ≠ one).max'_mem hne)).2
  · by_contra hc
    exact absurd ((Finset.univ.filter fun p : Fin D => t p ≠ one).le_max'
      j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)) (not_le.mpr hj)

/-- **What the carry coordinate is**: the greatest coordinate below the top. -/
theorem tupCarry_eq_iff (ht : IsTop one) {t : Fin D → A} (p : Fin D) :
    tupCarry t = (p : ℕ) ↔ (t p ≠ one ∧ ∀ j : Fin D, p < j → t j = one) := by
  constructor
  · intro hc
    by_cases hm : IsMaxTup t
    · rw [tupCarry_of_isMaxTup hm] at hc
      have := p.isLt
      omega
    · obtain ⟨p', hp', hab'⟩ := exists_carry ht hm
      have h1 : tupCarry t = (p' : ℕ) :=
        tupCarry_of_carry (fun hcx => hp' ((isTop_iff' ht _).mp hcx))
          fun j hj => (isTop_iff' ht _).mpr (hab' j hj)
      obtain rfl : p = p' := Fin.ext (hc.symm.trans h1)
      exact ⟨hp', hab'⟩
  · rintro ⟨hp, hab⟩
    exact tupCarry_of_carry (fun hcx => hp ((isTop_iff' ht _).mp hcx))
      fun j hj => (isTop_iff' ht _).mpr (hab j hj)

/-- **And when there is none**: the tuple is exhausted. -/
theorem tupCarry_eq_card_iff (ht : IsTop one) {t : Fin D → A} :
    tupCarry t = D ↔ ∀ p : Fin D, t p = one := by
  constructor
  · intro hc
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp⟩ := hcon
    have hm : ¬IsMaxTup t := fun hx => hp ((isMaxTup_iff_eq_top ht t).mp hx p)
    obtain ⟨p', hp', hab'⟩ := exists_carry ht hm
    have h1 : tupCarry t = (p' : ℕ) :=
      tupCarry_of_carry (fun hcx => hp' ((isTop_iff' ht _).mp hcx))
        fun j hj => (isTop_iff' ht _).mpr (hab' j hj)
    have := p'.isLt
    omega
  · intro hall
    exact tupCarry_of_isMaxTup ((isMaxTup_iff_eq_top ht t).mpr hall)

/-- **The least tuple is the constant designated element.** -/
theorem botTup_eq [Nonempty A] (hb : IsBot zero) (p : Fin D) :
    (botTup : Fin D → A) p = zero :=
  le_antisymm (botTup_le p zero) (hb _)

end TupNext

/-! ### The three obligations of a loop element -/

namespace DrawData

variable {L : Language.{0, 0}} {dt : DrawData L} [Fintype dt.SlotIx]

/-- **A loop element's coordinate is definable after the advance**: the carry
is a question about the pattern, and the value at it is the next element. -/
theorem uSlotDefinable_tupNext_lvE (j : Fin dt.eDim) :
    USlotDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun _ f _ => tupNext (dt.readLvE f) j := by
  refine uSlotDefinable_cases
    (R := fun p : Fin dt.eDim => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      f (dt.lvE p) ≠ e.one ∧ ∀ j' : Fin dt.eDim, p < j' → f (dt.lvE j') = e.one)
    (U := fun p : Fin dt.eDim => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      if j < p then f (dt.lvE j) else if j = p then ordSucc (f (dt.lvE j)) else e.zero)
    (V' := fun _ f _ => f (dt.lvE j))
    (fun p => (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvE p)).not.and
      (uGDefinable_forall fun j' : Fin dt.eDim =>
        (uGDefinable_const (p < j')).imp
          (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvE j'))))
    (fun p => ((uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (dt.lvE j)).ite
      ((uSlotDefinable_ctlSucc (L := L) (W := dt.SlotIx) (dt.lvE j)).ite
        uSlotDefinable_zero)))
    (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (dt.lvE j)) ?_ ?_
  · rintro e f g p ⟨hp, hab⟩
    refine tupNext_apply_of_carry e.hbot (t := dt.readLvE f) (p := p) ?_ ?_ j
    · exact fun hc => hp (le_antisymm (e.htop _) (hc e.one))
    · intro j' hj'
      have hj1 : dt.readLvE f j' = e.one := hab j' hj'
      rw [hj1]
      exact e.htop
  · intro e f g hno
    have hmax : IsMaxTup (dt.readLvE f) := by
      by_contra hc
      obtain ⟨p, hp, hab⟩ := exists_carry e.htop hc
      exact hno p ⟨hp, hab⟩
    rw [tupNext_of_isMaxTup hmax]
    rfl

/-- **The wide loop, advanced, is definable.** -/
theorem uStDefinable_advLvE :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.advLvE f := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.eDim, q = dt.lvE j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_tupNext_lvE j).congr fun e f g => ?_
    exact congrFun (dt.readLvE_putLvE f (tupNext (dt.readLvE f))) j
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f g => ?_
    exact putLvE_of_not_lv fun j hc => hq ⟨j, hc⟩

/-- **The wide loop, started, is definable.** -/
theorem uStDefinable_initLvE :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.initLvE f := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.eDim, q = dt.lvE j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun e f _ => ?_
    exact (congrFun (dt.readLvE_putLvE f (botTup : Fin dt.eDim → e.α)) j).trans
      (botTup_eq e.hbot j)
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f g => ?_
    exact putLvE_of_not_lv fun j hc => hq ⟨j, hc⟩

/-- **The wide loop's exhaustion test is definable.** -/
theorem uGDefinable_isMaxLvE :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.IsMaxLvE f :=
  (uGDefinable_forall fun j : Fin dt.eDim =>
    uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvE j)).congr
    fun e f _ => (isMaxTup_iff_eq_top e.htop (dt.readLvE f)).trans Iff.rfl

/-- **Which coordinate carries is a definable question**: it is decided by
which coordinates are maximal, and that is what a slot atom says. -/
theorem uGDefinable_tupCarry_eq (c₀ : ℕ) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      tupCarry (dt.readLvE f) = c₀ := by
  by_cases hlt : c₀ < dt.eDim
  · refine ((uGDefinable_ctlOne (L := L) (W := dt.SlotIx)
      (dt.lvE ⟨c₀, hlt⟩)).not.and
      (uGDefinable_forall fun j : Fin dt.eDim =>
        (uGDefinable_const ((⟨c₀, hlt⟩ : Fin dt.eDim) < j)).imp
          (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvE j)))).congr
      fun e f _ => ?_
    exact tupCarry_eq_iff e.htop (t := dt.readLvE f) ⟨c₀, hlt⟩
  · by_cases heq : c₀ = dt.eDim
    · refine (uGDefinable_forall fun j : Fin dt.eDim =>
        uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvE j)).congr fun e f _ => ?_
      rw [heq]
      exact tupCarry_eq_card_iff e.htop (t := dt.readLvE f)
    · refine (uGDefinable_false (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
        fun e f _ => ?_
      refine iff_of_false (fun hc => ?_) not_false
      have := tupCarry_le (t := dt.readLvE f)
      omega

/-! ### The narrow width -/

/-- **A narrow loop element's coordinate is definable after the advance.** -/
theorem uSlotDefinable_tupNext_lvC (j : Fin dt.dd0) :
    USlotDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun _ f _ => tupNext (dt.readLv f) j := by
  refine uSlotDefinable_cases
    (R := fun p : Fin dt.dd0 => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      f (dt.lvC p) ≠ e.one ∧ ∀ j' : Fin dt.dd0, p < j' → f (dt.lvC j') = e.one)
    (U := fun p : Fin dt.dd0 => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      if j < p then f (dt.lvC j) else if j = p then ordSucc (f (dt.lvC j)) else e.zero)
    (V' := fun _ f _ => f (dt.lvC j))
    (fun p => (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvC p)).not.and
      (uGDefinable_forall fun j' : Fin dt.dd0 =>
        (uGDefinable_const (p < j')).imp
          (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvC j'))))
    (fun p => ((uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (dt.lvC j)).ite
      ((uSlotDefinable_ctlSucc (L := L) (W := dt.SlotIx) (dt.lvC j)).ite
        uSlotDefinable_zero)))
    (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (dt.lvC j)) ?_ ?_
  · rintro e f g p ⟨hp, hab⟩
    refine tupNext_apply_of_carry e.hbot (t := dt.readLv f) (p := p) ?_ ?_ j
    · exact fun hc => hp (le_antisymm (e.htop _) (hc e.one))
    · intro j' hj'
      have hj1 : dt.readLv f j' = e.one := hab j' hj'
      rw [hj1]
      exact e.htop
  · intro e f g hno
    have hmax : IsMaxTup (dt.readLv f) := by
      by_contra hc
      obtain ⟨p, hp, hab⟩ := exists_carry e.htop hc
      exact hno p ⟨hp, hab⟩
    rw [tupNext_of_isMaxTup hmax]
    rfl

/-- **The narrow loop, advanced, is definable.** -/
theorem uStDefinable_advLvN :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.advLvN f := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.dd0, q = dt.lvC j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_tupNext_lvC j).congr fun e f _ => ?_
    exact congrFun (dt.readLv_putLv f (tupNext (dt.readLv f))) j
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f _ => ?_
    exact putLv_of_not_lv fun j hc => hq ⟨j, hc⟩

/-- **The narrow loop, started, is definable.** -/
theorem uStDefinable_initLvN :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.initLvN f := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.dd0, q = dt.lvC j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun e f _ => ?_
    exact (congrFun (dt.readLv_putLv f (botTup : Fin dt.dd0 → e.α)) j).trans
      (botTup_eq e.hbot j)
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f _ => ?_
    exact putLv_of_not_lv fun j hc => hq ⟨j, hc⟩

/-- **The narrow loop's exhaustion test is definable.** -/
theorem uGDefinable_isMaxLvN :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.IsMaxLvN f :=
  (uGDefinable_forall fun j : Fin dt.dd0 =>
    uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (dt.lvC j)).congr
    fun e f _ => (isMaxTup_iff_eq_top e.htop (dt.readLv f)).trans Iff.rfl

end DrawData

end Draw

end DescriptiveComplexity
