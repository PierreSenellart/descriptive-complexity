/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Step
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

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMStart WMTr WMWrite WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# A wide machine that accepts

The three wide problems fold their promises into their yes-instances, and a
membership theorem about a *vacuous* problem would say nothing. This file closes
that gap by exhibiting one instance, the smallest there is, and proving all three
problems hold of it:

> two elements – one that is both a start state and an accepting state, one that
> is the blank – no transitions at all, and the order they come in.

Its machine starts on the empty address in an accepting state, so it accepts in
**no steps**; having no transitions it is deterministic, so the deterministic
space-bounded problem holds of it too. Nothing about addresses is used beyond
`DescriptiveComplexity.isInit_wide` – the head starts on the empty address and the
tape is blank – which is the point: the promises reduce to conditions on the
instance (`DescriptiveComplexity.wideData_wellFormed_iff`,
`DescriptiveComplexity.wideData_deterministic_iff`) and those conditions are
satisfiable.

The instance is also the smallest exercise of the interface a hardness reduction
will use, so it is worth reading as a template: a `FirstOrder.Language.wide`
structure is eleven relations on a finite type, and the two promises are then
four conditions and four more.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace WideSmoke

/-- **The smallest wide-machine instance**: `0` is a start state and an accepting
state, `1` is the blank, there are no transitions, and `wmLe` is the order of
`Fin 2`. -/
instance structure₂ : Lax822549.WideMachines.wide.Structure (Fin 2) where
  funMap f := isEmptyElim f
  RelMap {k} r v :=
    match k, r with
    | _, .wle => v 0 ≤ v 1
    | _, .tr => False
    | _, .start => v 0 = 0
    | _, .acc => v 0 = 0
    | _, .blank => v 0 = 1
    | _, .right => False
    | _, .src => False
    | _, .read => False
    | _, .dst => False
    | _, .write => False
    | _, .inp => False

@[simp] theorem wmLe_iff (a b : Fin 2) : Lax822549.WideMachines.WMLe a b ↔ a ≤ b := Iff.rfl

@[simp] theorem wmTr_iff (a : Fin 2) : Lax822549.WideMachines.WMTr a ↔ False := Iff.rfl

@[simp] theorem wmStart_iff (a : Fin 2) : Lax822549.WideMachines.WMStart a ↔ a = 0 := Iff.rfl

@[simp] theorem wmAcc_iff (a : Fin 2) : Lax822549.WideMachines.WMAcc a ↔ a = 0 := Iff.rfl

@[simp] theorem wmBlank_iff (a : Fin 2) : Lax822549.WideMachines.WMBlank a ↔ a = 1 := Iff.rfl

@[simp] theorem wmInp_iff (a b : Fin 2) : Lax822549.WideMachines.WMInp a b ↔ False := Iff.rfl

@[simp] theorem wmDst_iff (a b : Fin 2) : Lax822549.WideMachines.WMDst a b ↔ False := Iff.rfl

@[simp] theorem wmWrite_iff (a b : Fin 2) : Lax822549.WideMachines.WMWrite a b ↔ False := Iff.rfl

/-- The order of the instance is linear, being the order of `Fin 2`. -/
theorem isLinOrd_wmLe : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Fin 2)) := isLinOrd_le

/-- The instance is well formed: a linear order, no input to be functional about,
and exactly one blank. -/
theorem wellFormed : (Lax822549.WideMachines.wideData (Fin 2)).WellFormed :=
  wideData_wellFormed_iff.mpr
    ⟨isLinOrd_wmLe, fun _ _ _ hc => absurd hc (wmInp_iff _ _).mp,
      ⟨1, rfl⟩, fun _a _b ha hb => ha.trans hb.symm⟩

/-- The instance is deterministic: it has one start state and no transitions. -/
theorem deterministic : (Lax822549.WideMachines.wideData (Fin 2)).Deterministic :=
  wideData_deterministic_iff.mpr
    ⟨fun _ _ hq hq' => hq.trans hq'.symm, fun _ _ _ _ ht => absurd ht (wmTr_iff _).mp,
      fun _ _ _ hd => absurd hd (wmDst_iff _ _).mp,
      fun _ _ _ hw => absurd hw (wmWrite_iff _ _).mp⟩

/-- **The machine accepts, in no steps**: it starts on the empty address with a
blank tape in the state `0`, which is accepting. -/
theorem accepts : (Lax822549.WideMachines.wideData (Fin 2)).Accepts := by
  have hpos : 0 < Nat.card {p : Lax822549.WideMachines.WPoint (Fin 2) // (Lax822549.WideMachines.wideData (Fin 2)).Posn p} := by
    have : Nonempty {p : Lax822549.WideMachines.WPoint (Fin 2) // (Lax822549.WideMachines.wideData (Fin 2)).Posn p} :=
      ⟨⟨Sum.inl fun _ => False, trivial⟩⟩
    exact Nat.card_pos
  exact ⟨⟨Sum.inr 0, Sum.inl fun _ => False, fun _ => Sum.inr 1⟩,
    ⟨Sum.inr 0, Sum.inl fun _ => False, fun _ => Sum.inr 1⟩, 0,
    isInit_wide isLinOrd_wmLe (fun _ _ hc => absurd hc (wmInp_iff _ _).mp) rfl rfl,
    hpos, rfl, rfl⟩

/-- **The machine accepts in bounded space too**, the same run with the step bound
dropped. -/
theorem acceptsSpace : (Lax822549.WideMachines.wideData (Fin 2)).AcceptsSpace :=
  ⟨⟨Sum.inr 0, Sum.inl fun _ => False, fun _ => Sum.inr 1⟩,
    ⟨Sum.inr 0, Sum.inl fun _ => False, fun _ => Sum.inr 1⟩,
    isInit_wide isLinOrd_wmLe (fun _ _ hc => absurd hc (wmInp_iff _ _).mp) rfl rfl,
    Relation.ReflTransGen.refl, rfl⟩

end WideSmoke

/-! ### The three problems are not vacuous -/

/-- **`DescriptiveComplexity.WideAccept` has a yes-instance**, so the membership
`DescriptiveComplexity.wideAccept_mem_NEXPTIME` is not about an empty problem. -/
theorem wideAccept_nonvacuous : WideAccept (Fin 2) :=
  ⟨WideSmoke.wellFormed, WideSmoke.accepts⟩

/-- **`DescriptiveComplexity.WideAcceptSpace` has a yes-instance.** -/
theorem wideAcceptSpace_nonvacuous : WideAcceptSpace (Fin 2) :=
  ⟨WideSmoke.wellFormed, WideSmoke.acceptsSpace⟩

/-- **`DescriptiveComplexity.DWideAcceptSpace` has a yes-instance**: the instance
has no transitions, so it is deterministic. -/
theorem dwideAcceptSpace_nonvacuous : DWideAcceptSpace (Fin 2) :=
  ⟨WideSmoke.wellFormed, WideSmoke.deterministic, WideSmoke.acceptsSpace⟩

end Lax822549Proofs.DescriptiveComplexity


