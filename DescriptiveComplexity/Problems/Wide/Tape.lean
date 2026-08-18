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
theorem reachesIn_scan_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe r t) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe s t ∧
      (∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r) ∧
      (wideData A).ReachesIn (wideRank t - wideRank s)
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reachesIn_scanRight_least h hex fun r hlb hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hlb hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-- **A program scans right to the first cell that stops it**, the budget
forgotten. -/
theorem reaches_scan_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe s t)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s r →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe r t) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe s t ∧
      (∀ r : A → Prop, WMSetLe WMLe s r → WMSetLt WMLe r t → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ := by
  obtain ⟨t, hstop, hge, hfirst, hrun⟩ := reachesIn_scan_tape h hex hstep
  exact ⟨t, hstop, hge, hfirst, hrun.reflTransGen⟩

/-- **A program scans left to the first cell that stops it**, the same reading
downwards. -/
theorem reachesIn_scanBack_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe r s →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t r) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ ¬WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t s ∧
      (∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r) ∧
      (wideData A).ReachesIn (wideRank s - wideRank t)
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reachesIn_scanLeft_greatest h hex fun r hub hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hub hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-- **A program scans left to the first cell that stops it**, the budget
forgotten. -/
theorem reaches_scanBack_tape (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ WMSetLe WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe r s →
      (∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t r) → ¬Stop r →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ ¬WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ WMSetLe WMLe t s ∧
      (∀ r : A → Prop, WMSetLt WMLe t r → WMSetLe WMLe r s → ¬Stop r) ∧
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ := by
  obtain ⟨t, hstop, hle, hfirst, hrun⟩ := reachesIn_scanBack_tape h hex hstep
  exact ⟨t, hstop, hle, hfirst, hrun.reflTransGen⟩

/-! ### Writing a track across the tape

The phase a program spends laying something out: sweep up, writing one symbol per
address as it goes. The tape it holds part-way through is written below the head
and untouched at and above it, which is the address-scale twin of
`DescriptiveComplexity.Problems.Wide.Mirror`'s mirror during a register walk.

The new symbols are a *parameter*, so the same statement serves a deterministic
layout phase – build the register file, plant a marker – and a **guessing** one:
if the transition offered at each cell may write either of two symbols, the run
below exists for every choice, and the choice is the certificate. -/

open Classical in
/-- **A family in mid-installation**: the new value at the addresses the head has
passed, the old one where it stands and above. The value type is arbitrary – a
sweep installs symbols this way, and a program installs whole backgrounds. -/
noncomputable def midTape {B : Type} (f₀ f₁ : (A → Prop) → B) (s : A → Prop) :
    (A → Prop) → B :=
  fun r => if WMSetLt WMLe r s then f₁ r else f₀ r

/-- Nothing has been written when the sweep starts. -/
theorem midTape_bot {B : Type} (h : IsLinOrd (WMLe (A := A))) (f₀ f₁ : (A → Prop) → B) :
    midTape f₀ f₁ (fun _ => False) = f₀ := by
  refine funext fun r => if_neg fun hlt => ?_
  exact ((wmSetLt_iff _ _).mp hlt).2
    ((isLinOrd_wmSetLe h).2.2.1 r _ ((wmSetLt_iff _ _).mp hlt).1
      (wmSetLe_of_empty h (fun _ hc => hc) r))

omit [Finite A] in
/-- The cell the head stands on still holds its old symbol. -/
theorem midTape_self {B : Type} (f₀ f₁ : (A → Prop) → B) (s : A → Prop) :
    midTape f₀ f₁ s s = f₀ s :=
  if_neg fun hlt => ((wmSetLt_iff _ _).mp hlt).2 rfl

/-- One increment later, the cell holds its new symbol. -/
theorem midTape_incr {B : Type} (h : IsLinOrd (WMLe (A := A))) (f₀ f₁ : (A → Prop) → B)
    {s t : A → Prop}
    (hi : WMIncr WMLe s t) : midTape f₀ f₁ t s = f₁ s :=
  if_pos ((wmSetLt_iff_of_wmIncr h hi s).mpr ((isLinOrd_wmSetLe h).1 s))

/-- **A step of the sweep changes one cell**: off the cell the head is on, the
tape before and after the write agree. -/
theorem midTape_agree {B : Type} (h : IsLinOrd (WMLe (A := A))) (f₀ f₁ : (A → Prop) → B)
    {s t : A → Prop} (hi : WMIncr WMLe s t) :
    ∀ r : A → Prop, r ≠ s → midTape f₀ f₁ t r = midTape f₀ f₁ s r := by
  intro r hne
  have hiff : WMSetLt WMLe r t ↔ WMSetLt WMLe r s := by
    rw [wmSetLt_iff_of_wmIncr h hi r, wmSetLt_iff r s]
    exact ⟨fun hle => ⟨hle, hne⟩, fun hc => hc.1⟩
  unfold midTape
  by_cases hc : WMSetLt WMLe r s
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

/-- **A writing sweep carrying a state.** At every cell of a stretch the machine
writes the new symbol and moves right, and its state advances with the head: at
the cell `r` it is `st r`, and the step to `r`'s successor leaves it in that
successor's state. It arrives at the top of the stretch with the tape rewritten
below it and untouched above.

A state that varies is what lets a sweep write something *different* in every
cell: a rule computes its symbol from what it reads and from the state, and the
tape it reads is blank everywhere, so a phase laying down a pattern has to hold
the pattern's index in the state. That is how a program builds its own register
file – the state holds the element whose register the head is on, and the order
successor moves it along. -/
theorem reachesIn_of_wideWriteSt (h : IsLinOrd (WMLe (A := A))) {b : A}
    {st : (A → Prop) → A} {f₀ f₁ : (A → Prop) → A} {s₀ s₁ : A → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ r r' : A → Prop, WMIncr WMLe r r' → WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ →
      ∃ τ : A, WMTr τ ∧ WMSrc τ (st r) ∧ WMRead τ (f₀ r) ∧ WMDst τ (st r') ∧
        WMWrite τ (f₁ r) ∧ WMRight τ) :
    (wideData A).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (st s₀), Sum.inl s₀, wideTape (midTape f₀ f₁ s₀) b⟩
      ⟨Sum.inr (st s₁), Sum.inl s₁, wideTape (midTape f₀ f₁ s₁) b⟩ :=
  reachesIn_of_wideUp
    (conf := fun r => ⟨Sum.inr (st r), Sum.inl r, wideTape (midTape f₀ f₁ r) b⟩)
    h hle fun r r' hi hlb hub => by
      obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r r' hi hlb hub
      refine step_wideTape_right h hi htr hsrc ?_ hdst ?_ hright (midTape_agree h f₀ f₁ hi)
      · rwa [midTape_self]
      · rwa [midTape_incr h f₀ f₁ hi]

/-- **A writing sweep.** The previous statement in a fixed state.

The new assignment `f₁` is universally quantified, so a *guessing* phase is this
statement read at the guess: whatever the certificate, the run that writes it
exists. -/
theorem reachesIn_of_wideWrite (h : IsLinOrd (WMLe (A := A))) {q b : A}
    {f₀ f₁ : (A → Prop) → A} {s₀ s₁ : A → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s₀ r → WMSetLt WMLe r s₁ →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f₀ r) ∧ WMDst τ q ∧ WMWrite τ (f₁ r) ∧
        WMRight τ) :
    (wideData A).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr q, Sum.inl s₀, wideTape (midTape f₀ f₁ s₀) b⟩
      ⟨Sum.inr q, Sum.inl s₁, wideTape (midTape f₀ f₁ s₁) b⟩ :=
  reachesIn_of_wideWriteSt (st := fun _ => q) h hle
    fun r _r' hi hlb hub => hstep r hlb (wmSetLt_of_wmIncr_le h hi hub)

/-- **A writing sweep**, the budget forgotten. -/
theorem reaches_of_wideWrite (h : IsLinOrd (WMLe (A := A))) {q b : A}
    {f₀ f₁ : (A → Prop) → A} {s₀ s₁ : A → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ r : A → Prop, WMSetLe WMLe s₀ r → WMSetLt WMLe r s₁ →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f₀ r) ∧ WMDst τ q ∧ WMWrite τ (f₁ r) ∧
        WMRight τ) :
    Relation.ReflTransGen (wideData A).Step
      ⟨Sum.inr q, Sum.inl s₀, wideTape (midTape f₀ f₁ s₀) b⟩
      ⟨Sum.inr q, Sum.inl s₁, wideTape (midTape f₀ f₁ s₁) b⟩ :=
  (reachesIn_of_wideWrite h hle hstep).reflTransGen

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

/-- **A program on a clock accepts**: the same run with its budget kept and
compared once with the number of addresses. -/
theorem accepts_of_wideTape (h : IsLinOrd (WMLe (A := A))) {b : A} (hb : WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : WMStart q₀)
    {n : ℕ} {c : Config (WPoint A)}
    (hreach : (wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    (hlt : n < Nat.card {p : WPoint A // (wideData A).Posn p})
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).Accepts := by
  refine TMData.accepts_of_reachesIn (isInit_wideTape h hb hinp hmark hrest hq) hreach hlt ?_
  change wpMark WMAcc c.state
  rw [hstate]
  exact hacc

/-- **A program with a register file accepts on its clock**, the budget compared
against `2 ^ n`. -/
theorem accepts_of_wideTape_lt_two_pow (h : IsLinOrd (WMLe (A := A))) {b : A} (hb : WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : WMStart q₀)
    {n : ℕ} {c : Config (WPoint A)}
    (hreach : (wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    (hlt : n < 2 ^ Nat.card A)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : WMAcc qa) :
    (wideData A).Accepts :=
  accepts_of_wideTape h hb hinp hmark hrest hq hreach
    (by rw [card_wideAddr]; exact hlt) hstate hacc

end Tape

end DescriptiveComplexity
