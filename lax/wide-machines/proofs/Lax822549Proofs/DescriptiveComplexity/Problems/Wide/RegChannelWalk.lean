/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannelEnum
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
export Lax822549.WideMachines (WMHasInp WMLe WMSetLe)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The opening's walk at the register channel

The opening of a handed program leaves the marker, walks up to the file, steps
onto its first register, turns, comes home, guesses, and enters the evaluation.
What it asks of the instance is four addresses and five order facts
(`DescriptiveComplexity.Draw.Data.reachesIn_openingHanded`), and at this
channel they are all forced:

* the marker is the **empty address**, and the walk's first step is its
  increment;
* the file's first register is the **singleton of the element the reduction
  marks below the argument tags** (`DescriptiveComplexity.wmRegSeg_least`), so
  the address the walk stops on is that singleton's predecessor;
* the walk reaches it as long as the singleton is not itself the second address
  – which it is not, there being an argument element above the marked one.

So the whole geometry follows from the marking, and this file derives it.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section Walk

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

variable (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' P' dt.KIx dt.dd)))

variable (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, Lax822549.WideMachines.WMLe x y ↔ tagTupleLe x y)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
include h in
/-- **The opening's walk exists**: the marker's increment, the address the walk
stops on, the file's first register and its own increment, with the five order
facts the opening asks of them.

The one thing the instance has to bring is an element **above** the one the
channel marks below the argument tags – any argument element will do – which is
what makes the file's first register more than one step above the marker. -/
theorem exists_openingWalkReg {botE : Univ A R' P' dt.KIx dt.dd}
    (hbotm : Lax822549.WideMachines.WMHasInp botE)
    (hleast : ∀ y : Univ A R' P' dt.KIx dt.dd, Lax822549.WideMachines.WMHasInp y → Lax822549.WideMachines.WMLe botE y)
    (habove : ∃ z : Univ A R' P' dt.KIx dt.dd, WMLt Lax822549.WideMachines.WMLe botE z) :
    ∃ v₁ x y' : Univ A R' P' dt.KIx dt.dd → Prop,
      WMIncr Lax822549.WideMachines.WMLe (fun _ => False) v₁ ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe v₁ x ∧
        WMIncr Lax822549.WideMachines.WMLe x (wmRegSeg botE) ∧ WMIncr Lax822549.WideMachines.WMLe (wmRegSeg botE) y' ∧
        Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (fun _ => False) (wmRegSeg botE) := by
  classical
  obtain ⟨z, hz⟩ := habove
  -- the first register is the marked element's own singleton
  have hcell : wmRegSeg botE = fun w => w = botE := wmRegSeg_least h hbotm hleast
  have hne : ∃ w, wmRegSeg botE w := ⟨botE, h.1 botE, hbotm⟩
  -- the marker's increment, and the address the walk stops on
  obtain ⟨v₁, hvi₁⟩ := exists_wmIncr h (s := fun _ : Univ A R' P' dt.KIx dt.dd => False)
    ⟨botE, not_false⟩
  obtain ⟨x, hxy⟩ := exists_wmPred h hne
  obtain ⟨y', hyy'⟩ := exists_wmIncr h (s := wmRegSeg botE) ⟨z, fun hc => hz.2 hc.1⟩
  refine ⟨v₁, x, y', hvi₁, ?_, hxy, hyy',
    wmSetLe_of_empty h (fun _ => not_false) _⟩
  -- the walk reaches the register's predecessor: the register is not the
  -- marker's own increment, since an element lies above the one it holds
  refine (wmSetLt_iff_of_wmIncr h hxy v₁).mp ?_
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_succ_bot_of_nonempty h hvi₁ hne, fun hc => ?_⟩
  -- were they equal, the register would be the least nonempty address, and the
  -- singleton of an element above the marked one is below it
  have hz1 : WMSetLt Lax822549.WideMachines.WMLe (fun w => w = z) (wmRegSeg botE) := by
    rw [hcell]
    refine ⟨botE, fun w hw => iff_of_false ?_ ?_, fun hcz => hz.2 ?_, rfl⟩
    · rintro rfl
      exact hw.2 hz.1
    · rintro rfl
      exact hw.2 (h.1 w)
    · rw [← hcz]
      exact h.1 botE
  have hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe v₁ (fun w => w = z) :=
    wmSetLe_succ_bot_of_nonempty h hvi₁ ⟨z, rfl⟩
  rw [hc] at hle
  exact ((wmSetLt_iff _ _).mp hz1).2
    ((isLinOrd_wmSetLe h).2.2.1 _ _ ((wmSetLt_iff _ _).mp hz1).1 hle)

end Walk

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


