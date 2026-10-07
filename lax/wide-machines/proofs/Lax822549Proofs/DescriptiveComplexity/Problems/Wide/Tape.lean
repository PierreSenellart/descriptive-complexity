/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Marks
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMRead WMRight WMSetLe WMSrc WMStart WMTr WMWrite WPoint wideData wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Tape

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-! ### The tape of a program -/

/-- **The tape a symbol assignment presents**: the symbol of each address, and
the blank on the control points, which are not cells and are never written. -/
def wideTape (f : (A → Prop) → A) (b : A) : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A
  | Sum.inl s => Sum.inr (f s)
  | Sum.inr _ => Sum.inr b

omit [Lax822549.WideMachines.wide.Structure A] [Finite A] in
@[simp]
theorem wideTape_addr (f : (A → Prop) → A) (b : A) (s : A → Prop) :
    wideTape f b (Sum.inl s) = Sum.inr (f s) :=
  rfl

omit [Lax822549.WideMachines.wide.Structure A] [Finite A] in
@[simp]
theorem wideTape_ctrl (f : (A → Prop) → A) (b x : A) :
    wideTape f b (Sum.inr x) = Sum.inr b :=
  rfl

omit [Lax822549.WideMachines.wide.Structure A] [Finite A] in
/-- **The frame condition, in the program's form**: two symbol assignments
agreeing off one address present tapes agreeing off that cell. The control points
are where the general statement needs a case and this one does not. -/
theorem wideTape_frame {f f' : (A → Prop) → A} {s : A → Prop}
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) (b : A) :
    ∀ p : Lax822549.WideMachines.WPoint A, p ≠ Sum.inl s → wideTape f' b p = wideTape f b p := by
  rintro (r | x) hne
  · exact congrArg Sum.inr (hagree r fun hc => hne (congrArg Sum.inl hc))
  · rfl

/-! ### One step -/

/-- **A right-moving step of a program.** The head is on `s`, the transition `τ`
applies to the state and to the symbol `f s` written there, and the new
assignment `f'` differs from `f` at `s` only. -/
theorem step_wideTape_right (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe s t) {τ q q' b : A} {f f' : (A → Prop) → A}
    (htr : Lax822549.WideMachines.WMTr τ) (hsrc : Lax822549.WideMachines.WMSrc τ q) (hread : Lax822549.WideMachines.WMRead τ (f s)) (hdst : Lax822549.WideMachines.WMDst τ q')
    (hwrite : Lax822549.WideMachines.WMWrite τ (f' s)) (hright : Lax822549.WideMachines.WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) :
    (Lax822549.WideMachines.wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩ :=
  step_wide_right h hi htr hsrc hread hdst hwrite hright rfl rfl (wideTape_frame hagree b)

/-- **A left-moving step of a program**, the head stepping down to the address
whose increment it is on. -/
theorem step_wideTape_left (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe t s) {τ q q' b : A} {f f' : (A → Prop) → A}
    (htr : Lax822549.WideMachines.WMTr τ) (hsrc : Lax822549.WideMachines.WMSrc τ q) (hread : Lax822549.WideMachines.WMRead τ (f s)) (hdst : Lax822549.WideMachines.WMDst τ q')
    (hwrite : Lax822549.WideMachines.WMWrite τ (f' s)) (hright : ¬Lax822549.WideMachines.WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ s → f' r = f r) :
    (Lax822549.WideMachines.wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩ :=
  step_wide_left h hi htr hsrc hread hdst hwrite hright rfl rfl (wideTape_frame hagree b)

/-! ### The scans -/

/-- **A program scans right to the first cell that stops it.** The scanning
transition is asked for at the symbol the assignment gives, so no symbol is
quantified: a caller supplies one transition per symbol it does not stop at. -/
theorem reachesIn_scan_tape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t)
    (hstep : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r →
      (∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r t) → ¬Stop r →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (f r) ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ (f r) ∧ Lax822549.WideMachines.WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t ∧
      (∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r → WMSetLt Lax822549.WideMachines.WMLe r t → ¬Stop r) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn (wideRank t - wideRank s)
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reachesIn_scanRight_least h hex fun r hlb hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hlb hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-- **A program scans left to the first cell that stops it**, the same reading
downwards. -/
theorem reachesIn_scanBack_tape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q b : A} {f : (A → Prop) → A}
    {Stop : (A → Prop) → Prop} {s : A → Prop} (hex : ∃ t, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s)
    (hstep : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s →
      (∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t r) → ¬Stop r →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (f r) ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ (f r) ∧ ¬Lax822549.WideMachines.WMRight τ) :
    ∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s ∧
      (∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe t r → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s → ¬Stop r) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn (wideRank s - wideRank t)
        ⟨Sum.inr q, Sum.inl s, wideTape f b⟩ ⟨Sum.inr q, Sum.inl t, wideTape f b⟩ :=
  reachesIn_scanLeft_greatest h hex fun r hub hahead hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep r hub hahead hstop
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

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
  fun r => if WMSetLt Lax822549.WideMachines.WMLe r s then f₁ r else f₀ r

omit [Finite A] in
/-- The cell the head stands on still holds its old symbol. -/
theorem midTape_self {B : Type} (f₀ f₁ : (A → Prop) → B) (s : A → Prop) :
    midTape f₀ f₁ s s = f₀ s :=
  if_neg fun hlt => ((wmSetLt_iff _ _).mp hlt).2 rfl

/-- One increment later, the cell holds its new symbol. -/
theorem midTape_incr {B : Type} (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (f₀ f₁ : (A → Prop) → B)
    {s t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe s t) : midTape f₀ f₁ t s = f₁ s :=
  if_pos ((wmSetLt_iff_of_wmIncr h hi s).mpr ((isLinOrd_wmSetLe h).1 s))

/-- **A step of the sweep changes one cell**: off the cell the head is on, the
tape before and after the write agree. -/
theorem midTape_agree {B : Type} (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (f₀ f₁ : (A → Prop) → B)
    {s t : A → Prop} (hi : WMIncr Lax822549.WideMachines.WMLe s t) :
    ∀ r : A → Prop, r ≠ s → midTape f₀ f₁ t r = midTape f₀ f₁ s r := by
  intro r hne
  have hiff : WMSetLt Lax822549.WideMachines.WMLe r t ↔ WMSetLt Lax822549.WideMachines.WMLe r s := by
    rw [wmSetLt_iff_of_wmIncr h hi r, wmSetLt_iff r s]
    exact ⟨fun hle => ⟨hle, hne⟩, fun hc => hc.1⟩
  unfold midTape
  by_cases hc : WMSetLt Lax822549.WideMachines.WMLe r s
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

/-! ### The two ends of a run -/

/-- **The initial configuration of a program**: a start state, the head on the
empty address, and the tape whose symbol at the cell of `x` is the name of `x`
and whose symbol everywhere else is the blank. -/
theorem isInit_wideTape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} (hb : Lax822549.WideMachines.WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀) :
    (Lax822549.WideMachines.wideData A).IsInit ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ :=
  isInit_wide_marks h hb hinp (fun x => congrArg Sum.inr (hmark x))
    (fun p hp => by
      match p with
      | Sum.inl s => exact congrArg Sum.inr (hrest s fun x hc => hp x (congrArg Sum.inl hc))
      | Sum.inr _ => rfl)
    hq

/-- **A program accepts**: it starts as `DescriptiveComplexity.isInit_wideTape`
says, roams, and ends in an accepting state. This is the whole of
`DescriptiveComplexity.WideAcceptSpace` for a program with a register file. -/
theorem acceptsSpace_of_wideTape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} (hb : Lax822549.WideMachines.WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, f (wmSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, s ≠ wmSeg x) → f s = b) {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀)
    {c : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)}
    (hreach : Relation.ReflTransGen (Lax822549.WideMachines.wideData A).Step
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : Lax822549.WideMachines.WMAcc qa) :
    (Lax822549.WideMachines.wideData A).AcceptsSpace := by
  refine ⟨⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩, c,
    isInit_wideTape h hb hinp hmark hrest hq, hreach, ?_⟩
  change Lax822549.WideMachines.wpMark Lax822549.WideMachines.WMAcc c.state
  rw [hstate]
  exact hacc

end Tape

end Lax822549Proofs.DescriptiveComplexity


