/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannel
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Tape
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

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideRegChannel
end Lax822549.WideRegChannel

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMHasInp WMInp WMLe WMRegSeg WMStart WPoint wideData wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideRegChannel (wideRegData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Starting a run at the register channel

The two machines an instance describes – `DescriptiveComplexity.wideData` and
`DescriptiveComplexity.wideRegData` – differ in one field, the channel, and it
is read nowhere but in the *initial tape*: a step reads the transitions, the
order and the positions and nothing else. So every run lemma of the library
transfers by definition (`wideRegData_step`, `wideRegData_reachesIn`), and what
has to be redone is the pair of statements at the two ends of a run.

They are the segment channel's own with two changes: the cell of `x` is
`wmRegSeg x`, and only the elements that *carry* input have one. Where the
segment channel says “every cell holds its element's symbol, every other
address is blank”, the register channel says the same of the elements it writes
for, and an address that is nobody's cell is blank as before.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section RegRun

variable {A : Type} [Lax822549.WideMachines.wide.Structure A]

/-- **And so they take the same runs.** -/
theorem wideRegData_stepsIn : ∀ (n : ℕ) (c c' : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)),
    (Lax822549.WideRegChannel.wideRegData A).StepsIn n c c' ↔ (Lax822549.WideMachines.wideData A).StepsIn n c c'
  | 0, _, _ => Iff.rfl
  | n + 1, c, c' => by
    constructor
    · rintro ⟨d, hs, hr⟩
      exact ⟨d, hs, (wideRegData_stepsIn n d c').mp hr⟩
    · rintro ⟨d, hs, hr⟩
      exact ⟨d, hs, (wideRegData_stepsIn n d c').mpr hr⟩

/-- **And the same bounded runs.** -/
theorem wideRegData_reachesIn (n : ℕ) (c c' : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)) :
    (Lax822549.WideRegChannel.wideRegData A).ReachesIn n c c' ↔ (Lax822549.WideMachines.wideData A).ReachesIn n c c' :=
  exists_congr fun k => and_congr_right fun _ => wideRegData_stepsIn k c c'

/-- **A register cell starts holding its element's symbol.** -/
theorem initTape_wmRegSeg {x a : A} (hinp : Lax822549.WideMachines.WMInp x a) :
    (Lax822549.WideRegChannel.wideRegData A).InitTape (Sum.inl (wmRegSeg x)) (Sum.inr a) :=
  Or.inl ⟨x, wmRegSeg_self x, hinp⟩

/-- **Every other address starts blank**: one that is no writing element's
cell. -/
theorem initTape_of_not_wmRegSeg {s : A → Prop}
    (hno : ∀ x y : A, Lax822549.WideMachines.WMRegSeg s x → ¬Lax822549.WideMachines.WMInp x y) (a : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideRegChannel.wideRegData A).InitTape (Sum.inl s) a ↔ (Lax822549.WideRegChannel.wideRegData A).Blank a := by
  have hinp : ∀ b : Lax822549.WideMachines.WPoint A, ¬(Lax822549.WideRegChannel.wideRegData A).Inp (Sum.inl s) b := by
    rintro (t | y)
    · exact fun hc => hc
    · rintro ⟨x, hd, hi⟩
      exact hno x y hd hi
  exact ⟨fun hc => hc.elim (fun hc' => absurd hc' (hinp a)) fun hc' => hc'.2,
    fun hc => Or.inr ⟨hinp, hc⟩⟩

/-- **The initial tape at the register channel**: the symbol of `x` at the cell
of `x` for every element the channel writes for, the blank at every address that
is no such element's cell. -/
theorem initTape_of_marksReg {b : A} (hb : Lax822549.WideMachines.WMBlank b) {sym : A → A}
    (hinp : ∀ x : A, Lax822549.WideMachines.WMHasInp x → Lax822549.WideMachines.WMInp x (sym x)) {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A}
    (hmark : ∀ x : A, Lax822549.WideMachines.WMHasInp x → tp (Sum.inl (wmRegSeg x)) = Sum.inr (sym x))
    (hrest : ∀ p : Lax822549.WideMachines.WPoint A, (∀ x : A, Lax822549.WideMachines.WMHasInp x → p ≠ Sum.inl (wmRegSeg x)) →
      tp p = Sum.inr b) :
    ∀ p, (Lax822549.WideRegChannel.wideRegData A).InitTape p (tp p) := by
  classical
  rintro (s | y)
  · by_cases hex : ∃ x : A, Lax822549.WideMachines.WMHasInp x ∧ s = wmRegSeg x
    · obtain ⟨x, hx, rfl⟩ := hex
      rw [hmark x hx]
      exact initTape_wmRegSeg (hinp x hx)
    · rw [hrest _ fun x hx hc => hex ⟨x, hx, Sum.inl_injective hc⟩]
      refine (initTape_of_not_wmRegSeg (fun z c hd hi => ?_) _).mpr hb
      exact hex ⟨z, ⟨c, hi⟩, (wmRegSeg_iff_eq _ z).mp hd⟩
  · rw [hrest _ fun x _ hc => Sum.inl_ne_inr hc.symm]
    exact Or.inr ⟨fun c hc => hc, hb⟩

variable [Finite A]

/-- **The promise of the register-channel machine is the same promise about the
instance**: a linear order, a functional input and a unique blank. The channel
enters only through the functionality of the input, and there two elements with
the same cell that both carry input are equal. -/
theorem wideRegData_wellFormed_iff : (Lax822549.WideRegChannel.wideRegData A).WellFormed ↔ WideWF A := by
  constructor
  · rintro ⟨hlin, -, hinp, ⟨b, hb⟩, huniq⟩
    have h1 : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)) :=
      ⟨fun x => hlin.1 (Sum.inr x),
        fun x y z h1 h2 => hlin.2.1 (Sum.inr x) (Sum.inr y) (Sum.inr z) h1 h2,
        fun x y h1 h2 => Sum.inr_injective (hlin.2.2.1 (Sum.inr x) (Sum.inr y) h1 h2),
        fun x y => hlin.2.2.2 (Sum.inr x) (Sum.inr y)⟩
    refine ⟨h1, fun x a c ha hc => ?_, ?_, fun a c ha hc => ?_⟩
    · exact Sum.inr_injective (hinp (Sum.inl (wmRegSeg x)) (Sum.inr a) (Sum.inr c)
        ⟨x, wmRegSeg_self x, ha⟩ ⟨x, wmRegSeg_self x, hc⟩)
    · match b with
      | Sum.inl s => exact False.elim hb
      | Sum.inr y => exact ⟨y, hb⟩
    · exact Sum.inr_injective (huniq (Sum.inr a) (Sum.inr c) ha hc)
  · rintro ⟨hlin, hinp, ⟨b, hb⟩, huniq⟩
    refine ⟨isLinOrd_wpLe hlin, ⟨Sum.inl fun _ => False, trivial⟩, ?_, ⟨Sum.inr b, hb⟩, ?_⟩
    · rintro (s | x) (a | a) (c | c) h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | skip
      obtain ⟨u, hu, hau⟩ := h1
      obtain ⟨v, hv, hcv⟩ := h2
      have huv : u = v := wmRegSeg_injOn hlin ⟨a, hau⟩ ⟨c, hcv⟩
        (((wmRegSeg_iff_eq s u).mp hu).symm.trans ((wmRegSeg_iff_eq s v).mp hv))
      exact congrArg Sum.inr (hinp u a c hau (huv ▸ hcv))
    · rintro (s | x) (t | y) h1 h2 <;>
        first
          | exact False.elim h1
          | exact False.elim h2
          | exact congrArg Sum.inr (huniq x y h1 h2)

/-- **The initial configuration at the register channel**: a start state, the
head on the empty address – which is no register's cell, a register's cell
holding its own element – and the marked tape. -/
theorem isInit_wideReg_marks (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} (hb : Lax822549.WideMachines.WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMHasInp x → Lax822549.WideMachines.WMInp x (sym x))
    {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A}
    (hmark : ∀ x : A, Lax822549.WideMachines.WMHasInp x → tp (Sum.inl (wmRegSeg x)) = Sum.inr (sym x))
    (hrest : ∀ p : Lax822549.WideMachines.WPoint A, (∀ x : A, Lax822549.WideMachines.WMHasInp x → p ≠ Sum.inl (wmRegSeg x)) →
      tp p = Sum.inr b)
    {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀) :
    (Lax822549.WideRegChannel.wideRegData A).IsInit ⟨Sum.inr q₀, Sum.inl fun _ => False, tp⟩ :=
  ⟨hq, minPos_wpLe h, initTape_of_marksReg hb hinp hmark hrest⟩

/-- **The initial configuration of a program at the register channel**, its tape
given as a function of the addresses. -/
theorem isInit_wideRegTape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} (hb : Lax822549.WideMachines.WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMHasInp x → Lax822549.WideMachines.WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, Lax822549.WideMachines.WMHasInp x → f (wmRegSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, Lax822549.WideMachines.WMHasInp x → s ≠ wmRegSeg x) → f s = b)
    {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀) :
    (Lax822549.WideRegChannel.wideRegData A).IsInit ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ :=
  isInit_wideReg_marks h hb hinp (fun x hx => congrArg Sum.inr (hmark x hx))
    (fun p hp => by
      match p with
      | Sum.inl s =>
        exact congrArg Sum.inr (hrest s fun x hx hc => hp x hx (congrArg Sum.inl hc))
      | Sum.inr _ => rfl)
    hq

/-- **A program at the register channel accepts on its clock**: it starts as
`isInit_wideRegTape` says, runs for fewer steps than there are addresses, and
ends in an accepting state. -/
theorem accepts_of_wideRegTape (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} (hb : Lax822549.WideMachines.WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMHasInp x → Lax822549.WideMachines.WMInp x (sym x)) {f : (A → Prop) → A}
    (hmark : ∀ x : A, Lax822549.WideMachines.WMHasInp x → f (wmRegSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, Lax822549.WideMachines.WMHasInp x → s ≠ wmRegSeg x) → f s = b)
    {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀) {n : ℕ} {c : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)}
    (hreach : (Lax822549.WideMachines.wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    (hlt : n < Nat.card {p : Lax822549.WideMachines.WPoint A // (Lax822549.WideMachines.wideData A).Posn p})
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : Lax822549.WideMachines.WMAcc qa) :
    (Lax822549.WideRegChannel.wideRegData A).Accepts := by
  refine TMData.accepts_of_reachesIn (isInit_wideRegTape h hb hinp hmark hrest hq)
    ((wideRegData_reachesIn n _ _).mpr hreach) hlt ?_
  change Lax822549.WideMachines.wpMark Lax822549.WideMachines.WMAcc c.state
  rw [hstate]
  exact hacc

/-- **The same, with the budget compared against `2 ^ n`.** -/
theorem accepts_of_wideRegTape_lt_two_pow (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A}
    (hb : Lax822549.WideMachines.WMBlank b) {sym : A → A} (hinp : ∀ x : A, Lax822549.WideMachines.WMHasInp x → Lax822549.WideMachines.WMInp x (sym x))
    {f : (A → Prop) → A} (hmark : ∀ x : A, Lax822549.WideMachines.WMHasInp x → f (wmRegSeg x) = sym x)
    (hrest : ∀ s : A → Prop, (∀ x : A, Lax822549.WideMachines.WMHasInp x → s ≠ wmRegSeg x) → f s = b)
    {q₀ : A} (hq : Lax822549.WideMachines.WMStart q₀) {n : ℕ} {c : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)}
    (hreach : (Lax822549.WideMachines.wideData A).ReachesIn n
      ⟨Sum.inr q₀, Sum.inl fun _ => False, wideTape f b⟩ c)
    (hlt : n < 2 ^ Nat.card A)
    {qa : A} (hstate : c.state = Sum.inr qa) (hacc : Lax822549.WideMachines.WMAcc qa) :
    (Lax822549.WideRegChannel.wideRegData A).Accepts :=
  accepts_of_wideRegTape h hb hinp hmark hrest hq hreach
    (by rw [card_wideAddr]; exact hlt) hstate hacc

end RegRun

end Lax822549Proofs.DescriptiveComplexity


