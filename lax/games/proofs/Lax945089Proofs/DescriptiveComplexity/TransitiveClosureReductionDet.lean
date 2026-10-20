/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.TransitiveClosureReduction
import Lax945089Proofs.DescriptiveComplexity.TransitiveClosureDet
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax945089.TransitiveClosureReductions
end Lax945089.TransitiveClosureReductions

namespace Lax945089Proofs.DescriptiveComplexity.DTCReduction
end Lax945089Proofs.DescriptiveComplexity.DTCReduction

namespace Lax945089Proofs.DescriptiveComplexity.FOReduction
end Lax945089Proofs.DescriptiveComplexity.FOReduction

namespace Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax945089Proofs.DescriptiveComplexity.ParamTCSpec
end Lax945089Proofs.DescriptiveComplexity.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity.RelOrderedFOReduction
end Lax945089Proofs.DescriptiveComplexity.RelOrderedFOReduction

namespace Lax945089Proofs.DescriptiveComplexity.TCFamily
end Lax945089Proofs.DescriptiveComplexity.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity.TCSpec
end Lax945089Proofs.DescriptiveComplexity.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.TransitiveClosureReductions (DTCReduction ParamTCSpec TCFamily)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCSpec)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# FO(DTC) reductions: the logarithmic-space reduction of the textbooks

`DescriptiveComplexity.TCReduction` lets a reduction's formulas consult
*nondeterministic* walks. The classical many-one reduction for the classes at
this level is the **deterministic logarithmic-space** one, and this file is it:
`DescriptiveComplexity.DTCReduction`, notation `P ≤ᵈᵗᶜ Q`, where every walk is
read through its determinization – it may follow a step only when that step is
the only one available.

## Determinism as a formula

The packaging is the library's own, from
`DescriptiveComplexity.TransitiveClosureDet`: rather than carrying a proof that
a walk is functional – which is not first-order data, and would have to be
re-established after every pullback – the walk is *read* through

```
detStep(x̄, ȳ, z̄) := step(x̄, ȳ, z̄) ∧ ∀ w̄. step(x̄, w̄, z̄) → w̄ = ȳ
```

(`DescriptiveComplexity.ParamTCSpec.det`), which is again first-order. Every
specification then denotes a legitimate deterministic walk
(`DescriptiveComplexity.ParamTCSpec.det_functional`) and nothing has to be
assumed; on a walk that is already functional the two readings agree
(`DescriptiveComplexity.ParamTCSpec.detStepAt_of_functional`), which is how an
existing walk – the parity walk, say – is reused at this notion.

## Where it sits

`≤ᶠᵒ[≤]` ⊆ `≤ᵈᵗᶜ` ⊆ `≤ᵗᶜ` ⊆ `≤ˡᶠᵖ`: a determinized walk is a walk, so
everything `DescriptiveComplexity.TransitiveClosureReduction` proves transfers,
and PTIME, NP and coNP are closed under `≤ᵈᵗᶜ` as well.

`DescriptiveComplexity.LOGSPACE` is closed under it
(`DescriptiveComplexity.mem_LOGSPACE_of_dtcReduction`, in
`DescriptiveComplexity.TransitiveClosureReductionClosure`), by the same normal
form as NL under `≤ᵗᶜ` with one difference at the atoms: flattening a walk
that consults walks needs non-reachability at the negative occurrences, and a
deterministic walk is witnessed not to arrive by a step budget
(`DescriptiveComplexity.ParamTCSpec.detReachDecider`), where a
nondeterministic one needs inductive counting. Transitivity is
`DescriptiveComplexity.DTCReduction.trans`, the composite of
`DescriptiveComplexity.TransitiveClosureReductionTrans` read through its
determinization.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Determinizing a parameterized walk -/

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

theorem realize_detStep (m n : s.Mode) (x y : Fin s.k → A) (z : Fin s.par → A) :
    (s.detStep m n).Realize (Sum.elim (Sum.elim x y) z) ↔
      (s.step m n).Realize (Sum.elim (Sum.elim x y) z) ∧
        ∀ (m' : s.Mode) (w : Fin s.k → A),
          (s.step m m').Realize (Sum.elim (Sum.elim x w) z) → m' = n ∧ w = y := by
  classical
  rw [Lax945089.TransitiveClosureReductions.ParamTCSpec.detStep, Formula.realize_inf, Formula.realize_iInf]
  have hrel : ∀ w : Fin s.k → A,
      (Sum.elim (Sum.elim (Sum.elim x y) z) w) ∘ s.detVar = Sum.elim (Sum.elim x w) z := by
    intro w
    funext i
    rcases i with (i | i) | i <;> rfl
  refine and_congr Iff.rfl ⟨fun h m' w hw => ?_, fun h m' => ?_⟩
  · have hm := (Formula.realize_iAlls).mp (h m') w
    rw [Formula.realize_imp, Formula.realize_relabel, hrel w] at hm
    have hc := hm hw
    by_cases hmn : m' = n
    · refine ⟨hmn, ?_⟩
      rw [if_pos hmn, Formula.realize_iInf] at hc
      funext i
      have hi := hc i
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var] at hi
      exact hi
    · rw [if_neg hmn, Formula.realize_bot] at hc
      exact hc.elim
  · refine Formula.realize_iAlls.mpr fun w => ?_
    rw [Formula.realize_imp, Formula.realize_relabel, hrel w]
    intro hw
    obtain ⟨hmn, hwy⟩ := h m' w hw
    rw [if_pos hmn, Formula.realize_iInf]
    intro i
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun hwy i

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (realize_detStep)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

/-- **A determinized step is a step with no competitor.** -/
theorem detStepAt_iff (z : Fin s.par → A) (a b : s.Node A) :
    s.det.StepAt z a b ↔ s.StepAt z a b ∧ ∀ c : s.Node A, s.StepAt z a c → c = b := by
  refine Iff.trans (s.realize_detStep a.1 b.1 a.2 b.2 z) (and_congr Iff.rfl ?_)
  exact ⟨fun h c hc => Prod.ext_iff.mpr (h c.1 c.2 hc),
    fun h m' w hw => ⟨congrArg Prod.fst (h (m', w) hw), congrArg Prod.snd (h (m', w) hw)⟩⟩

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (detStepAt_iff)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

variable (A) in
/-- A walk is *functional* at a structure when no node has two successors. -/
def Functional : Prop :=
  ∀ (z : Fin s.par → A) (a b c : s.Node A), s.StepAt z a b → s.StepAt z a c → b = c

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (Functional)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

variable {s}

/-- On a walk that is already functional, the deterministic reading is the
original one. -/
theorem detStepAt_of_functional (h : s.Functional A) (z : Fin s.par → A) (a b : s.Node A) :
    s.det.StepAt z a b ↔ s.StepAt z a b := by
  rw [s.detStepAt_iff z a b]
  exact ⟨And.left, fun hab => ⟨hab, fun c hc => h z a c b hc hab⟩⟩

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (detStepAt_of_functional)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

variable {s}

/-- Reachability is unchanged by determinizing a functional walk. -/
theorem reachAt_det_of_functional (h : s.Functional A) (z : Fin s.par → A) (a b : s.Node A) :
    s.det.ReachAt z a b ↔ s.ReachAt z a b := by
  constructor
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((detStepAt_of_functional h z c d).mp hcd)
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((detStepAt_of_functional h z c d).mpr hcd)

end ParamTCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec

export Lax945089Proofs.DescriptiveComplexity.ParamTCSpec (reachAt_det_of_functional)

end Lax945089.TransitiveClosureReductions.ParamTCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : Lax945089.TransitiveClosureReductions.ParamTCSpec L)

variable {A : Type} [L.Structure A]

variable {s}

end ParamTCSpec

/-! ### Determinizing a family -/

namespace TCFamily

variable {L : Language.{0, 0}} (F : Lax945089.TransitiveClosureReductions.TCFamily L)

variable {F} {A : Type} [L.Structure A]

variable (F A) in
/-- A family is functional when each of its walks is. -/
def Functional : Prop :=
  ∀ i : F.Ix, (F.spec i).Functional A

end TCFamily

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.TCFamily

export Lax945089Proofs.DescriptiveComplexity.TCFamily (Functional)

end Lax945089.TransitiveClosureReductions.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCFamily

variable {L : Language.{0, 0}} (F : Lax945089.TransitiveClosureReductions.TCFamily L)

variable {F} {A : Type} [L.Structure A]

/-- **A functional family is unchanged by determinization**: its relation
variables hold the same relations either way. -/
theorem reachAssign_det_of_functional (h : F.Functional A) :
    F.det.reachAssign A = F.reachAssign A := by
  funext q w
  exact propext (ParamTCSpec.reachAt_det_of_functional (h q.1) _ _ _)

end TCFamily

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.TransitiveClosureReductions.TCFamily

export Lax945089Proofs.DescriptiveComplexity.TCFamily (reachAssign_det_of_functional)

end Lax945089.TransitiveClosureReductions.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCFamily

variable {L : Language.{0, 0}} (F : Lax945089.TransitiveClosureReductions.TCFamily L)

variable {F} {A : Type} [L.Structure A]

end TCFamily

/-! ### An FO(TC) sentence read deterministically -/

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀) {A : Type} [L₀.Structure A] [LinearOrder A]

/-- **A functional walk may be read deterministically at no cost**: its
walk-as-an-atom formula (`DescriptiveComplexity.TCSpec.acceptsF`) still says
acceptance when the relation variables hold the *determinized* reachability
relations. This is what lets an existing walk of the catalog be reused at the
deterministic notion. -/
theorem realize_acceptsF_det (h : (spec.toFamily).Functional A) :
    (@Sentence.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        ((spec.toFamily).det.reachAssign A)) spec.acceptsF) ↔ spec.Accepts A := by
  rw [TCFamily.reachAssign_det_of_functional h]
  exact spec.realize_acceptsF

end TCSpec

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.TransitiveClosure.TCSpec

export Lax945089Proofs.DescriptiveComplexity.TCSpec (realize_acceptsF_det)

end Lax485149.TransitiveClosure.TCSpec

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : Lax485149.TransitiveClosure.TCSpec L₀) {A : Type} [L₀.Structure A] [LinearOrder A]

end TCSpec

/-! ### FO(DTC) reductions -/

variable {L L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 P:51 " ≤ᵈᵗᶜ " Q:51 => Lax945089.TransitiveClosureReductions.DTCReduction P Q

section ToTC

end ToTC

end Lax945089Proofs.DescriptiveComplexity


