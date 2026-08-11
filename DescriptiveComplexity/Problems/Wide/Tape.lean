/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Marks

/-!
# A program's tape is a function of the address

`DescriptiveComplexity.TMData` takes the tape to be a function on the whole
universe of the machine, `WPoint A → WPoint A`. A *program*'s tape is never that
general: the control points are not cells, so they keep the blank they started
with for ever, and every real cell holds a symbol – an element of the instance.
So a program's tape is a function

> `f : (A → Prop) → A`, a symbol for each address,

and `DescriptiveComplexity.wideTape` is the machine's tape it presents. Working
in that form is worth a file of its own because it removes the same three
obligations from every step of every phase:

| obligation | in the general form | here |
|---|---|---|
| the symbol under the head | `tp (Sum.inl s) = Sum.inr a` | `f s`, no equation |
| the frame condition | `∀ p : WPoint A, p ≠ Sum.inl s → …` | `∀ r, r ≠ s → f' r = f r` |
| the control points | a case of every proof | discharged once |

`DescriptiveComplexity.step_wideTape_right` and its leftward twin are the step
in that form, `DescriptiveComplexity.reaches_scan_tape` and
`DescriptiveComplexity.reaches_scanBack_tape` are the scans, and
`DescriptiveComplexity.isInit_wideTape` is the initial configuration of a program
that has marked its register file
(`DescriptiveComplexity.Problems.Wide.Marks`).

Note what is *not* here: `Function.update`. An address is a set, so equality of
addresses is not decidable, and a program's tapes come from formulas anyway. A
write is described by naming the new tape function and saying where it agrees
with the old one, which is what `hagree` is in every statement below.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Tape

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-! ### The tape of a program -/

/-- **The tape a symbol assignment presents**: the symbol of each address, and
the blank on the control points, which are not cells and are never written. -/
def wideTape (f : (A → Prop) → A) (b : A) : WPoint A → WPoint A
  | Sum.inl s => Sum.inr (f s)
  | Sum.inr _ => Sum.inr b

omit [Language.wide.Structure A] [Finite A] in
@[simp]
theorem wideTape_addr (f : (A → Prop) → A) (b : A) (s : A → Prop) :
    wideTape f b (Sum.inl s) = Sum.inr (f s) :=
  rfl

omit [Language.wide.Structure A] [Finite A] in
@[simp]
theorem wideTape_ctrl (f : (A → Prop) → A) (b x : A) :
    wideTape f b (Sum.inr x) = Sum.inr b :=
  rfl

omit [Language.wide.Structure A] [Finite A] in
/-- **The frame condition, in the program's form**: two symbol assignments
agreeing off one address present tapes agreeing off that cell. The control points
are where the general statement needs a case and this one does not. -/
theorem wideTape_frame {f f' : (A → Prop) → A} {s : A → Prop}
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) (b : A) :
    ∀ p : WPoint A, p ≠ Sum.inl s → wideTape f' b p = wideTape f b p := by
  rintro (r | x) hne
  · exact congrArg Sum.inr (hagree r fun hc => hne (congrArg Sum.inl hc))
  · rfl

/-! ### One step -/

/-- **A right-moving step of a program.** The head is on `s`, the transition `τ`
applies to the state and to the symbol `f s` written there, and the new
assignment `f'` differs from `f` at `s` only. -/
theorem step_wideTape_right (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr WMLe s t) {τ q q' b : A} {f f' : (A → Prop) → A}
    (htr : WMTr τ) (hsrc : WMSrc τ q) (hread : WMRead τ (f s)) (hdst : WMDst τ q')
    (hwrite : WMWrite τ (f' s)) (hright : WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) :
    (wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩ :=
  step_wide_right h hi htr hsrc hread hdst hwrite hright rfl rfl (wideTape_frame hagree b)

/-- **A left-moving step of a program**, the head stepping down to the address
whose increment it is on. -/
theorem step_wideTape_left (h : IsLinOrd (WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr WMLe t s) {τ q q' b : A} {f f' : (A → Prop) → A}
    (htr : WMTr τ) (hsrc : WMSrc τ q) (hread : WMRead τ (f s)) (hdst : WMDst τ q')
    (hwrite : WMWrite τ (f' s)) (hright : ¬WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) :
    (wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩ :=
  step_wide_left h hi htr hsrc hread hdst hwrite hright rfl rfl (wideTape_frame hagree b)

/-! ### The scans -/

/-- **A program scans right to the first cell that stops it.** The scanning
transition is asked for at the symbol the assignment gives, so no symbol is
quantified: a caller supplies one transition per symbol it does not stop at. -/
theorem reaches_scan_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe r t) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe s t ∧
      (∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reaches_scanRight_least h hex fun r hlb hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hlb hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-- **A program scans left to the first cell that stops it**, the same reading
downwards. -/
theorem reaches_scanBack_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe r s →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t r) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ ¬WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t s ∧
      (∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reaches_scanLeft_greatest h hex fun r hub hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hub hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-! ### The two ends of a run -/

/-- **The initial configuration of a program**: a start state, the head on the
empty address, and the tape whose symbol at the cell of `x` is the name of `x`
and whose symbol everywhere else is the blank. -/
theorem isInit_wideTape (h : IsLinOrd (WMLe (A := A))) {b : A} (hb : WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : WMStart q₀) :
    (wideData A).IsInit ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ :=
  isInit_wide_marks h hb hinp (fun x => congrArg Sum.inr (hmark x))
    (fun p hp => by
      match p with
      | Sum.inl s => exact congrArg Sum.inr (hrest s fun x hc => hp x (congrArg Sum.inl hc))
      | Sum.inr _ => rfl)
    hq

/-- **A program accepts**: it starts as `DescriptiveComplexity.isInit_wideTape`
says, roams, and ends in an accepting state. This is the whole of
`DescriptiveComplexity.WideAcceptSpace` for a program with a register file. -/
theorem acceptsSpace_of_wideTape (h : IsLinOrd (WMLe (A := A))) {b : A} (hb : WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : WMStart q₀)
    {c : Config (WPoint A)}
    (hreach : Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).AcceptsSpace := by
  refine ⟨⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩, c,
    isInit_wideTape h hb hinp hmark hrest hq, hreach, ?_⟩
  change wpMark WMAcc c.state
  rw [hstate]
  exact hacc

end Tape

end DescriptiveComplexity
