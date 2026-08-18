/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Sweep

/-!
# One step of a wide machine, packaged

`DescriptiveComplexity.TMData.Step` asks for eight things at once – a transition,
its source, its read symbol, its destination, its written symbol, the frame
condition on the untouched cells, the direction, and the neighbor relation on the
head. A program of a hardness reduction discharges them at *every* phase, so they
are packaged here once:

> `DescriptiveComplexity.step_wide_right` – a right-moving step from an address to
> its increment, given a transition of the instance and the symbol the head is
> reading.

The new tape is given as an arbitrary function with the two conditions a step
imposes – its value at the head, and agreement elsewhere – rather than as
`Function.update`, since an address is a *set* and equality of addresses is not
decidable. `DescriptiveComplexity.step_wide_left` is the same reading backwards,
for a phase that sweeps down.

On top of it, `DescriptiveComplexity.accepts_of_rightSweep` is the shape a
one-pass program has: give a state and a tape *per address*, check one transition
per increment, start blank on the empty address, and end accepting. That is the
whole of `DescriptiveComplexity.WideAccept` for a monotone sweep, with no run, no
counting and no `DescriptiveComplexity.SuccPos` in sight.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Step

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-- **A right-moving step of a wide machine**: the head is on the address `s`
reading the symbol `a`, the transition `τ` applies to the state `q` and that
symbol, and the machine writes `a'`, moves to the state `q'` and steps to the
increment of `s`.

The new tape is given as an arbitrary function with the two conditions a step
imposes on it – its value at the head, and agreement elsewhere – rather than as
`Function.update`: an address is a *set*, so equality of addresses is not
decidable, and a program's tapes are given by formulas anyway. -/
theorem step_wide_right (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr WMLe s t) {τ q q' a a' : A} {tape tape' : WPoint A → WPoint A}
    (htr : WMTr τ) (hsrc : WMSrc τ q) (hread : WMRead τ a) (hdst : WMDst τ q')
    (hwrite : WMWrite τ a') (hright : WMRight τ) (hcur : tape (Sum.inl s) = Sum.inr a)
    (hnew : tape' (Sum.inl s) = Sum.inr a')
    (hframe : ∀ p : WPoint A, p ≠ Sum.inl s → tape' p = tape p) :
    (wideData A).Step ⟨Sum.inr q, Sum.inl s, tape⟩ ⟨Sum.inr q', Sum.inl t, tape'⟩ := by
  refine ⟨Sum.inr τ, htr, hsrc, ?_, hdst, ?_, hframe, Or.inl ⟨hright, ?_⟩⟩
  · rw [show ((⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).head) = Sum.inr a from hcur]
    exact hread
  · rw [show ((⟨Sum.inr q', Sum.inl t, tape'⟩ : Config (WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).head) = Sum.inr a' from hnew]
    exact hwrite
  · exact (succPos_wpLe_iff h s t).mpr hi

/-- **A left-moving step of a wide machine**: the same, with the head stepping
*down* to the address whose increment it is on. -/
theorem step_wide_left (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr WMLe t s) {τ q q' a a' : A} {tape tape' : WPoint A → WPoint A}
    (htr : WMTr τ) (hsrc : WMSrc τ q) (hread : WMRead τ a) (hdst : WMDst τ q')
    (hwrite : WMWrite τ a') (hright : ¬WMRight τ) (hcur : tape (Sum.inl s) = Sum.inr a)
    (hnew : tape' (Sum.inl s) = Sum.inr a')
    (hframe : ∀ p : WPoint A, p ≠ Sum.inl s → tape' p = tape p) :
    (wideData A).Step ⟨Sum.inr q, Sum.inl s, tape⟩ ⟨Sum.inr q', Sum.inl t, tape'⟩ := by
  refine ⟨Sum.inr τ, htr, hsrc, ?_, hdst, ?_, hframe, Or.inr ⟨hright, ?_⟩⟩
  · rw [show ((⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).head) = Sum.inr a from hcur]
    exact hread
  · rw [show ((⟨Sum.inr q', Sum.inl t, tape'⟩ : Config (WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Config (WPoint A)).head) = Sum.inr a' from hnew]
    exact hwrite
  · exact (succPos_wpLe_iff h t s).mpr hi

/-! ### A one-pass program -/

/-- The configuration of a sweep at an address: the state and the tape it holds
there. Off the addresses the value is irrelevant – a sweep never looks – so it
repeats the one at the empty address. -/
def wideConf (st : (A → Prop) → A) (tp : (A → Prop) → WPoint A → WPoint A) :
    WPoint A → Config (WPoint A)
  | Sum.inl s => ⟨Sum.inr (st s), Sum.inl s, tp s⟩
  | Sum.inr _ => ⟨Sum.inr (st fun _ => False), Sum.inl fun _ => False, tp fun _ => False⟩

omit [Language.wide.Structure A] [Finite A] in
@[simp]
theorem wideConf_addr (st : (A → Prop) → A) (tp : (A → Prop) → WPoint A → WPoint A)
    (s : A → Prop) : wideConf st tp (Sum.inl s) = ⟨Sum.inr (st s), Sum.inl s, tp s⟩ :=
  rfl

/-- **A monotone program accepts.** Give a state and a tape at each address; check
that at every increment some transition of the instance carries the machine from
one to the next, moving right; start on the empty address in a start state with a
blank tape; end at some address in an accepting state. The machine then accepts,
within its clock.

This is the shape of the whole NEXPTIME hardness program: the guess of the
certificate and the fold of the kernel are what the transitions say, and nothing
about runs, ranks or neighbors appears again. -/
theorem accepts_of_rightSweep (h : IsLinOrd (WMLe (A := A)))
    (hno : ∀ x y : A, ¬WMInp x y) {st : (A → Prop) → A}
    {tp : (A → Prop) → WPoint A → WPoint A}
    (hstep : ∀ s t : A → Prop, WMIncr WMLe s t →
      ∃ τ a a' : A, WMTr τ ∧ WMSrc τ (st s) ∧ WMRead τ a ∧ WMDst τ (st t) ∧
        WMWrite τ a' ∧ WMRight τ ∧ tp s (Sum.inl s) = Sum.inr a ∧
        tp t (Sum.inl s) = Sum.inr a' ∧
        ∀ p : WPoint A, p ≠ Sum.inl s → tp t p = tp s p)
    {b : A} (hb : WMBlank b) (hstart : WMStart (st fun _ => False))
    (hblank : tp (fun _ => False) = fun _ => Sum.inr b)
    (s : A → Prop) (hacc : WMAcc (st s)) :
    (wideData A).Accepts := by
  refine accepts_of_wideSweep h (conf := wideConf st tp) (fun s t hi => ?_) ?_ s hacc
  · obtain ⟨τ, a, a', htr, hsrc, hread, hdst, hwrite, hright, hcur, hnew, hframe⟩ :=
      hstep s t hi
    rw [wideConf_addr, wideConf_addr]
    exact step_wide_right h hi htr hsrc hread hdst hwrite hright hcur hnew hframe
  · rw [wideConf_addr, hblank]
    exact isInit_wide h hno hstart hb

end Step

end DescriptiveComplexity
