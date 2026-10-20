/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Copies
import Lax480241Proofs.DescriptiveComplexity.Exponential.Class
import Mathlib.Data.Finite.Sigma
import Lax480241Proofs.DescriptiveComplexity.ClauseDischarge
import Lax480241Proofs.DescriptiveComplexity.Complexity
import Lax480241Proofs.DescriptiveComplexity.InductiveCounting.Order
import Lax480241Proofs.DescriptiveComplexity.LogSpace
import Lax480241Proofs.DescriptiveComplexity.Ordered
import Lax480241Proofs.DescriptiveComplexity.Problems.Reachability
import Lax480241Proofs.DescriptiveComplexity.SecondOrderKrom
import Lax480241Proofs.DescriptiveComplexity.TwoCnf
import Lax480241Proofs.DescriptiveComplexity.PSpace
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SOTCDefinable
end Lax480241Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity.SOTCSpec
end Lax480241Proofs.DescriptiveComplexity.SOTCSpec

namespace Lax485149.Reachability
end Lax485149.Reachability

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.Reachability (Reachable SGEdge SGSource SGTarget)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign)
end Lax904597.SecondOrder.SOBlock

namespace FirstOrder.Language
export Lax485149.Reachability (stGraph)
end FirstOrder.Language

/-!
# An SO(TC) walk is reachability on an exponential expansion

The construction that connects the exponential classes to the polynomial ones:
**an `DescriptiveComplexity.SOTCSpec` is the graph REACH reads on the expansion
whose points are its states**. Compare the two definitions, which are the same
sentence up to the name of the universe:

```
SOTCSpec.Accepts A = ∃ ρ σ, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ Relation.ReflTransGen spec.Step ρ σ
Reachable       M = ∃ s t, SGSource s   ∧ SGTarget t   ∧ Relation.ReflTransGen SGEdge     s t
```

So the expansion `DescriptiveComplexity.SOTCSpec.toExp` takes `Tag := Unit`, no
domain restriction, the block of the specification, and the vocabulary of
graphs with marked sources and targets, defining the edge symbol by the
transition sentence and the two marks by the endpoint sentences. Its points are
the states (`DescriptiveComplexity.SOTCSpec.toExpEquiv`) and REACH holds of it
exactly when the walk accepts
(`DescriptiveComplexity.SOTCSpec.reachable_toExp_iff`).

Since REACH is in every class from NL up, this gives at once

* `PSPACE ⊆ NL.exp` and `PSPACE ⊆ PTIME.exp = EXPTIME`,

the inclusion that starts the tower above PSPACE. Read on the definitions the
second one is **SO(TC) ⊆ SO(LFP)** – a transitive closure is a least fixed
point – which is the second-order shadow of `NL ⊆ PTIME`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

/-! ### The expansion of a specification -/

/-- **The expansion whose points are the states of the walk**: no tags, no
domain restriction, and the three sentences of the specification defining the
three symbols of the vocabulary of marked graphs. -/
def toExp : Lax480241.Expansions.ExpExpansion L where
  Tag := Unit
  B := spec.B
  E := Lax485149.Reachability.stGraph
  dom _ := ⊤
  relSentence {n} r _ :=
    match n, r with
    | _, .edge => (spec.B.twoLHom (L.sum Language.order)).onSentence spec.step
    | _, .source => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.src
    | _, .target => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.tgt
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨(), spec.B.botAssign A, ?_⟩
    let := spec.B.structure₁ (L := L.sum Language.order) (spec.B.botAssign A)
    exact Formula.realize_top.mpr trivial

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (toExp)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- The expanded structure of `DescriptiveComplexity.SOTCSpec.toExp`, at the
vocabulary of marked graphs – equal to the expansion's own by definition, but
not syntactically, so instance search has to be handed it. -/
@[instance_reducible]
def toExpStructure : Lax485149.Reachability.stGraph.Structure (spec.toExp.Map A) :=
  spec.toExp.mapStructure A

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (toExpStructure)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- The domain of `DescriptiveComplexity.SOTCSpec.toExp` is the whole space of
tagged assignments: its domain sentence is `⊤`. -/
theorem domHolds_toExp (p : spec.toExp.Point A) : Lax480241.Expansions.ExpExpansion.DomHolds p := by
  let := spec.toExp.B.structure₁ (L := L.sum Language.order) p.2
  exact Formula.realize_top.mpr trivial

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (domHolds_toExp)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- **The points of the expansion are the states of the walk.** -/
def toExpEquiv : spec.toExp.Map A ≃ spec.State A where
  toFun x := x.1.2
  invFun ρ := ⟨((), ρ), spec.domHolds_toExp A ((), ρ)⟩
  left_inv _ := ExpExpansion.map_ext rfl rfl
  right_inv _ := rfl

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (toExpEquiv)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

/-! ### The three symbols -/

variable {A}

/-- **The edge symbol is the transition sentence.** -/
theorem sgEdge_toExp (x y : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax485149.Reachability.SGEdge x y ↔ spec.Step x.1.2 y.1.2 :=
  SOBlock.realize_twoLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x, y] : Fin 2 → spec.toExp.Map A) i).1.2) spec.step

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (sgEdge_toExp)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

/-- **The marked sources are the starting states.** -/
theorem sgSource_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax485149.Reachability.SGSource x ↔ spec.IsSrc x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.src

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (sgSource_toExp)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

/-- **The marked targets are the accepting states.** -/
theorem sgTarget_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax485149.Reachability.SGTarget x ↔ spec.IsTgt x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.tgt

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (sgTarget_toExp)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

/-! ### Acceptance is reachability -/

theorem reach_of_reflTransGen :
    letI := spec.toExpStructure A
    ∀ {s t : spec.toExp.Map A}, Relation.ReflTransGen Lax485149.Reachability.SGEdge s t → spec.Reach s.1.2 t.1.2 := by
  let := spec.toExpStructure A
  intro s t h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((spec.sgEdge_toExp _ _).mp hbc)

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (reach_of_reflTransGen)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

theorem reflTransGen_of_reach :
    letI := spec.toExpStructure A
    ∀ {ρ σ : spec.State A}, spec.Reach ρ σ →
      Relation.ReflTransGen Lax485149.Reachability.SGEdge ((spec.toExpEquiv A).symm ρ) ((spec.toExpEquiv A).symm σ) := by
  let := spec.toExpStructure A
  intro ρ σ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((spec.sgEdge_toExp _ _).mpr hbc)

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (reflTransGen_of_reach)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

variable (A)

/-- **The walk accepts exactly when REACH holds of the expansion.** -/
theorem reachable_toExp_iff :
    letI := spec.toExpStructure A
    Lax485149.Reachability.Reachable (spec.toExp.Map A) ↔ spec.Accepts A := by
  let := spec.toExpStructure A
  constructor
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨s.1.2, t.1.2, (spec.sgSource_toExp s).mp hs, (spec.sgTarget_toExp t).mp ht,
      spec.reach_of_reflTransGen hpath⟩
  · rintro ⟨ρ, σ, hρ, hσ, hreach⟩
    exact ⟨(spec.toExpEquiv A).symm ρ, (spec.toExpEquiv A).symm σ,
      (spec.sgSource_toExp _).mpr hρ, (spec.sgTarget_toExp _).mpr hσ,
      spec.reflTransGen_of_reach hreach⟩

end SOTCSpec

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (reachable_toExp_iff)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOTCSpec

variable {L : Language.{0, 0}} (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable (A : Type) [L.Structure A] [LinearOrder A]

variable {A}

variable (A)

end SOTCSpec

/-! ### Polynomial space sits inside every exponential class above NL -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **An SO(TC) definable problem is definable over an expanded universe by
REACH**: the walk is the graph the expansion draws, so any class containing
REACH contains the problem one exponential up. -/
theorem SOTCDefinable.expDefinable {C : ComplexityClass} (hreach : REACH ∈ C)
    {P : Lax904597.Problems.DecisionProblem L} (h : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P) : ExpDefinable C P := by
  obtain ⟨spec, hspec⟩ := h
  let hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      Lax485149.Reachability.stGraph.Structure (spec.toExp.Map A) := fun A => spec.toExpStructure A
  refine ⟨spec.toExp, REACH, hreach, ?_⟩
  intro A _ _ _ _
  exact (hspec A).trans (spec.reachable_toExp_iff A).symm

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax480241Proofs.DescriptiveComplexity.SOTCDefinable (expDefinable)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **`PSPACE ⊆ PTIME.exp`**, i.e., `PSPACE ⊆ EXPTIME` once the class is named
(`DescriptiveComplexity.PSPACE_subset_EXPTIME`). Read on the definitions it is
**SO(TC) ⊆ SO(LFP)**, the second-order shadow of `NL ⊆ PTIME`. -/
theorem PSPACE_subset_PTIME_exp : PSPACE ⊆ PTIME.exp :=
  fun _ _ P h => SOTCDefinable.expDefinable reach_mem_PTIME ((mem_PSPACE_iff P).mp h)

end Lax480241Proofs.DescriptiveComplexity


