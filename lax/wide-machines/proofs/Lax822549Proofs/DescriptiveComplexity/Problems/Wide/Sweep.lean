/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Blocks
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Program
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMBlank WMInp WMLe WMStart WPoint wideData wpLe wpPosn)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (MaxPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax822549Proofs.DescriptiveComplexity

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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Sweep

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-! ### The two ends of the tape -/

/-- **The empty address is the only least position.** -/
theorem minPos_wpLe_iff (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (p : Lax822549.WideMachines.WPoint A) :
    Lax904597.Machines.MinPos Lax822549.WideMachines.wpLe Lax822549.WideMachines.wpPosn p ↔ p = Sum.inl fun _ => False := by
  refine ⟨fun hmin => ?_, fun hp => hp ▸ minPos_wpLe h⟩
  exact (isLinOrd_wpLe h).2.2.1 p _ (hmin.2 _ trivial) ((minPos_wpLe h).2 p hmin.1)

/-! ### The initial configuration -/

omit [Finite A] in
/-- **With no input in the instance the initial tape is blank everywhere.** A
reduction leaves `wmInp` empty: its machine's control is instance data already, so
it has nothing to read. -/
theorem initTape_of_no_wmInp (hno : ∀ x y : A, ¬Lax822549.WideMachines.WMInp x y) (p a : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideMachines.wideData A).InitTape p a ↔ (Lax822549.WideMachines.wideData A).Blank a := by
  have hinp : ∀ b : Lax822549.WideMachines.WPoint A, ¬(Lax822549.WideMachines.wideData A).Inp p b := by
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
theorem isInit_wide (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (hno : ∀ x y : A, ¬Lax822549.WideMachines.WMInp x y)
    {q₀ b : A} (hq : Lax822549.WideMachines.WMStart q₀) (hb : Lax822549.WideMachines.WMBlank b) :
    (Lax822549.WideMachines.wideData A).IsInit
      ⟨Sum.inr q₀, Sum.inl fun _ => False, fun _ => Sum.inr b⟩ :=
  ⟨hq, minPos_wpLe h, fun p => (initTape_of_no_wmInp hno p _).mpr hb⟩

/-! ### The sweep -/

/-- Both ends of a step of a wide machine are addresses, and the step is the
binary increment. -/
theorem step_ends_wide (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {p q : Lax822549.WideMachines.WPoint A}
    (hs : Lax904597.Machines.SuccPos Lax822549.WideMachines.wpLe Lax822549.WideMachines.wpPosn p q) :
    ∃ s t : A → Prop, p = Sum.inl s ∧ q = Sum.inl t ∧ WMIncr Lax822549.WideMachines.WMLe s t := by
  obtain ⟨s, rfl⟩ := (wpPosn_iff p).mp hs.1
  obtain ⟨t, rfl⟩ := (wpPosn_iff q).mp hs.2.1
  exact ⟨s, t, rfl, rfl, (succPos_wpLe_iff h s t).mp hs⟩

end Sweep

end Lax822549Proofs.DescriptiveComplexity


