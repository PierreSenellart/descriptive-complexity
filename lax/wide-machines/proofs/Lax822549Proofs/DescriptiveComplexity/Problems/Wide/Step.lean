/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Sweep
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMRead WMRight WMSrc WMStart WMTr WMWrite WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Step

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-- **A right-moving step of a wide machine**: the head is on the address `s`
reading the symbol `a`, the transition `τ` applies to the state `q` and that
symbol, and the machine writes `a'`, moves to the state `q'` and steps to the
increment of `s`.

The new tape is given as an arbitrary function with the two conditions a step
imposes on it – its value at the head, and agreement elsewhere – rather than as
`Function.update`: an address is a *set*, so equality of addresses is not
decidable, and a program's tapes are given by formulas anyway. -/
theorem step_wide_right (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe s t) {τ q q' a a' : A} {tape tape' : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A}
    (htr : Lax822549.WideMachines.WMTr τ) (hsrc : Lax822549.WideMachines.WMSrc τ q) (hread : Lax822549.WideMachines.WMRead τ a) (hdst : Lax822549.WideMachines.WMDst τ q')
    (hwrite : Lax822549.WideMachines.WMWrite τ a') (hright : Lax822549.WideMachines.WMRight τ) (hcur : tape (Sum.inl s) = Sum.inr a)
    (hnew : tape' (Sum.inl s) = Sum.inr a')
    (hframe : ∀ p : Lax822549.WideMachines.WPoint A, p ≠ Sum.inl s → tape' p = tape p) :
    (Lax822549.WideMachines.wideData A).Step ⟨Sum.inr q, Sum.inl s, tape⟩ ⟨Sum.inr q', Sum.inl t, tape'⟩ := by
  refine ⟨Sum.inr τ, htr, hsrc, ?_, hdst, ?_, hframe, Or.inl ⟨hright, ?_⟩⟩
  · rw [show ((⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).head) = Sum.inr a from hcur]
    exact hread
  · rw [show ((⟨Sum.inr q', Sum.inl t, tape'⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).head) = Sum.inr a' from hnew]
    exact hwrite
  · exact (succPos_wpLe_iff h s t).mpr hi

/-- **A left-moving step of a wide machine**: the same, with the head stepping
*down* to the address whose increment it is on. -/
theorem step_wide_left (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe t s) {τ q q' a a' : A} {tape tape' : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A}
    (htr : Lax822549.WideMachines.WMTr τ) (hsrc : Lax822549.WideMachines.WMSrc τ q) (hread : Lax822549.WideMachines.WMRead τ a) (hdst : Lax822549.WideMachines.WMDst τ q')
    (hwrite : Lax822549.WideMachines.WMWrite τ a') (hright : ¬Lax822549.WideMachines.WMRight τ) (hcur : tape (Sum.inl s) = Sum.inr a)
    (hnew : tape' (Sum.inl s) = Sum.inr a')
    (hframe : ∀ p : Lax822549.WideMachines.WPoint A, p ≠ Sum.inl s → tape' p = tape p) :
    (Lax822549.WideMachines.wideData A).Step ⟨Sum.inr q, Sum.inl s, tape⟩ ⟨Sum.inr q', Sum.inl t, tape'⟩ := by
  refine ⟨Sum.inr τ, htr, hsrc, ?_, hdst, ?_, hframe, Or.inr ⟨hright, ?_⟩⟩
  · rw [show ((⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).head) = Sum.inr a from hcur]
    exact hread
  · rw [show ((⟨Sum.inr q', Sum.inl t, tape'⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).tape
      (⟨Sum.inr q, Sum.inl s, tape⟩ : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)).head) = Sum.inr a' from hnew]
    exact hwrite
  · exact (succPos_wpLe_iff h t s).mpr hi

/-! ### A one-pass program -/

end Step

end Lax822549Proofs.DescriptiveComplexity


