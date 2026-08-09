/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Blocks
import DescriptiveComplexity.Problems.Machine.Program

/-!
# The sweep of a wide machine

The primitive every program of a hardness reduction into a wide machine will
cite, and the last piece of the address layer:

> **A machine that takes a step at every increment of its address runs from the
> empty address to any address, and does so within its clock.**

`DescriptiveComplexity.stepsIn_of_wideSweep` and
`DescriptiveComplexity.accepts_of_wideSweep`. So a phase is described by giving
its intended configuration *at each address* and discharging a single-step
obligation between an address and its increment – a statement about the
transition table, with no induction and no counting.

Nothing here is new machinery: `DescriptiveComplexity.TMData.stepsIn_of_segment`
already does the induction along the order, at an arbitrary position type, and
`DescriptiveComplexity.bitRank_lt_card` already does the clock. What this file
supplies is the identification of the three ends of that statement with the
address layer – the empty address is the least position
(`DescriptiveComplexity.minPos_wpLe_iff`), the full one is the last
(`DescriptiveComplexity.maxPos_wpLe_iff`), and a step is the binary increment
(`DescriptiveComplexity.succPos_wpLe_iff`) – so that a program never mentions
`SuccPos` again.

The initial configuration is settled here too. A reduction has no use for the
instance's input channel, its control being instance data already, so it leaves
`wmInp` empty; then the initial tape is **blank everywhere**
(`DescriptiveComplexity.initTape_of_no_wmInp`) and
`DescriptiveComplexity.isInit_wide` exhibits the one initial configuration: a
start state, the head on the empty address, every cell blank.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Sweep

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-! ### The two ends of the tape -/

/-- **The empty address is the only least position.** -/
theorem minPos_wpLe_iff (h : IsLinOrd (WMLe (A := A))) (p : WPoint A) :
    MinPos wpLe wpPosn p ↔ p = Sum.inl fun _ => False := by
  refine ⟨fun hmin => ?_, fun hp => hp ▸ minPos_wpLe h⟩
  exact (isLinOrd_wpLe h).2.2.1 p _ (hmin.2 _ trivial) ((minPos_wpLe h).2 p hmin.1)

/-- **The full address is the only last position.** -/
theorem maxPos_wpLe_iff (h : IsLinOrd (WMLe (A := A))) (p : WPoint A) :
    MaxPos wpLe wpPosn p ↔ p = Sum.inl fun _ => True := by
  refine ⟨fun hmax => ?_, fun hp => hp ▸ maxPos_wpLe h⟩
  exact (isLinOrd_wpLe h).2.2.1 p _ ((maxPos_wpLe h).2 p hmax.1) (hmax.2 _ trivial)

/-! ### The initial configuration -/

omit [Finite A] in
/-- **With no input in the instance the initial tape is blank everywhere.** A
reduction leaves `wmInp` empty: its machine's control is instance data already, so
it has nothing to read. -/
theorem initTape_of_no_wmInp (hno : ∀ x y : A, ¬WMInp x y) (p a : WPoint A) :
    (wideData A).InitTape p a ↔ (wideData A).Blank a := by
  have hinp : ∀ b : WPoint A, ¬(wideData A).Inp p b := by
    rintro (t | y)
    · match p with
      | Sum.inl s => exact fun hc => hc
      | Sum.inr x => exact fun hc => hc
    · match p with
      | Sum.inl s =>
        rintro ⟨x, -, hi⟩
        exact hno x y hi
      | Sum.inr x => exact fun hc => hc
  exact ⟨fun hc => hc.elim (fun hc' => absurd hc' (hinp a)) fun hc' => hc'.2,
    fun hc => Or.inr ⟨hinp, hc⟩⟩

/-- **The initial configuration of a wide machine**: a start state, the head on
the empty address, every cell blank. -/
theorem isInit_wide (h : IsLinOrd (WMLe (A := A))) (hno : ∀ x y : A, ¬WMInp x y)
    {q₀ b : A} (hq : WMStart q₀) (hb : WMBlank b) :
    (wideData A).IsInit
      ⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩ :=
  ⟨hq, minPos_wpLe h, fun p => (initTape_of_no_wmInp hno p _).mpr hb⟩

/-! ### The sweep -/

/-- Both ends of a step of a wide machine are addresses, and the step is the
binary increment. -/
theorem step_ends_wide (h : IsLinOrd (WMLe (A := A))) {p q : WPoint A}
    (hs : SuccPos wpLe wpPosn p q) :
    ∃ s t : A → Prop, p = Sum.inl s ∧ q = Sum.inl t ∧ WMIncr WMLe s t := by
  obtain ⟨s, rfl⟩ := (wpPosn_iff p).mp hs.1
  obtain ⟨t, rfl⟩ := (wpPosn_iff q).mp hs.2.1
  exact ⟨s, t, rfl, rfl, (succPos_wpLe_iff h s t).mp hs⟩

/-- **The sweep of a wide machine.** A machine stepping at every increment of its
address runs from the empty address to any address, in as many steps as that
address has rank. The obligation is one step between an address and its
increment: no induction along the tape, and no `DescriptiveComplexity.SuccPos`. -/
theorem stepsIn_of_wideSweep (h : IsLinOrd (WMLe (A := A)))
    {conf : WPoint A → Config (WPoint A)}
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t →
      (wideData A).Step (conf (Sum.inl s)) (conf (Sum.inl t)))
    (s : A → Prop) :
    (wideData A).StepsIn
      (bitRank (wideData A).Le (wideData A).Posn (Sum.inl s))
      (conf (Sum.inl fun _ => False)) (conf (Sum.inl s)) := by
  have hlin : IsLinOrd (wideData A).Le := isLinOrd_wpLe h
  have hmin := minPos_wpLe h (A := A)
  have hmax := maxPos_wpLe h (A := A)
  have hzero : bitRank (wideData A).Le (wideData A).Posn (Sum.inl fun _ => False : WPoint A) = 0 :=
    bitRank_eq_zero_of_minPos hlin hmin
  have hrun := TMData.stepsIn_of_segment (M := wideData A) hlin (conf := conf)
    (p₀ := (Sum.inl fun _ => False : WPoint A)) (p₁ := (Sum.inl fun _ => True : WPoint A))
    trivial (fun p q hsucc _ _ => ?_) (Sum.inl s) trivial
    (hmin.2 (Sum.inl s) trivial) (hmax.2 (Sum.inl s) trivial)
  · rwa [hzero, Nat.sub_zero] at hrun
  · obtain ⟨s', t', rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s' t' hi

/-- **A sweep that ends accepting makes the machine accept**: the clock counts
the positions, so the rank of the address the sweep stops at is below it by
construction. -/
theorem accepts_of_wideSweep (h : IsLinOrd (WMLe (A := A)))
    {conf : WPoint A → Config (WPoint A)}
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t →
      (wideData A).Step (conf (Sum.inl s)) (conf (Sum.inl t)))
    (hinit : (wideData A).IsInit (conf (Sum.inl fun _ => False)))
    (s : A → Prop) (hacc : (wideData A).Acc (conf (Sum.inl s)).state) :
    (wideData A).Accepts :=
  ⟨conf (Sum.inl fun _ => False), conf (Sum.inl s),
    bitRank (wideData A).Le (wideData A).Posn (Sum.inl s), hinit,
    bitRank_lt_card (p := (Sum.inl s : WPoint A)) trivial,
    stepsIn_of_wideSweep h hstep s, hacc⟩

end Sweep

end DescriptiveComplexity
