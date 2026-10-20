/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.SecondOrder
import Lax134656Proofs.DescriptiveComplexity.Ordered
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656Proofs.DescriptiveComplexity.HornClause
end Lax134656Proofs.DescriptiveComplexity.HornClause

namespace Lax134656Proofs.DescriptiveComplexity.HornProgram
end Lax134656Proofs.DescriptiveComplexity.HornProgram

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax134656Proofs.DescriptiveComplexity

/-!
# SO-Horn: existential second-order logic with a Horn kernel

The fragment SO-Horn of Grädel ([Grädel 1992][gradel1992capturing]): existential
second-order sentences whose first-order kernel is a conjunction of *Horn
clauses* in the quantified relation variables. On ordered structures SO-Horn
captures polynomial time – the Horn kernel is exactly what makes the guessed
relations *determined* rather than merely guessed, since a satisfiable Horn
formula has a least model, computable by unit propagation.

## The kernel, as data

The Horn condition constrains only the occurrences of the *second-order*
variables: a clause is

```
guard(x̄) ∧ R₁(x̄) ∧ … ∧ Rₙ(x̄) → R₀(x̄)   (or → ⊥)
```

where `guard` is an arbitrary first-order formula over the *input* vocabulary
alone (in the definability notion below, over its ordered expansion). Rather
than carve this shape out of `FirstOrder.Language.BoundedFormula` with a
syntactic predicate, the kernel is represented here *as data*: a
`DescriptiveComplexity.HornClause` bundles its guard, the list of its body atoms and its
optional head atom, and a `DescriptiveComplexity.HornProgram` is a list of clauses
sharing `k` universally quantified first-order variables. This is Grädel's
clausal normal form, and it is what a reduction consuming an SO-Horn definition
needs to see: the discharge of `DescriptiveComplexity.Problems.HornSat.Hardness` reads the
clause list directly, and emits one propositional Horn clause per clause and
per instantiation of the `k` variables.

`DescriptiveComplexity.SigmaSOHornDefinable` is the resulting definability notion,
the SO-Horn analogue of `DescriptiveComplexity.SigmaSODefinable`; it is closed under
(ordered) first-order reductions by
`DescriptiveComplexity.SecondOrderHornPull`, which is what makes it a
`DescriptiveComplexity.ComplexityClass` – the class `DescriptiveComplexity.PTIME` of
`DescriptiveComplexity.Hierarchy`.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Horn programs -/

/-! ### Semantics -/

section Semantics

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {A : Type} [L.Structure A]

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem HornClause.holds_equiv (e : M ≃[L] N) (c : Lax535992.HornFragment.HornClause L B k)
    (ρ : B.Assignment M) (v : Fin k → M) :
    c.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ c.Holds ρ v := by
  have hhead : c.HeadHolds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔
      c.HeadHolds ρ v := by
    rw [Lax535992.HornFragment.HornClause.HeadHolds, Lax535992.HornFragment.HornClause.HeadHolds]
    cases c.head with
    | none => exact Iff.rfl
    | some a => exact a.holds_equiv e ρ v
  refine imp_congr (and_congr ?_ ?_) hhead
  · exact StrongHomClass.realize_formula e c.guard
  · exact forall_congr' fun a => imp_congr Iff.rfl (a.holds_equiv e ρ v)

end Iso

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornClause

export Lax134656Proofs.DescriptiveComplexity.HornClause (holds_equiv)

end Lax535992.HornFragment.HornClause

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem HornProgram.holds_equiv (e : M ≃[L] N) (prog : Lax535992.HornFragment.HornProgram L B k)
    (ρ : B.Assignment M) : prog.Holds (B.mapAssign e.toEquiv ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    exact (c.holds_equiv e ρ v).mp (h (fun j => e (v j)) c hc)
  · intro h v c hc
    have := (c.holds_equiv e ρ fun j => e.symm (v j)).mpr
      (h (fun j => e.symm (v j)) c hc)
    simpa using this

end Iso

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.HornProgram

export Lax134656Proofs.DescriptiveComplexity.HornProgram (holds_equiv)

end Lax535992.HornFragment.HornProgram

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

/-- **Horn satisfiability is isomorphism-invariant**: a program has a
satisfying assignment on one structure iff it has one on any isomorphic
structure. -/
theorem exists_holds_equiv (e : M ≃[L] N) (prog : Lax535992.HornFragment.HornProgram L B k) :
    (∃ ρ : B.Assignment M, prog.Holds ρ) ↔ ∃ ρ : B.Assignment N, prog.Holds ρ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.mapAssign e.toEquiv ρ, (prog.holds_equiv e ρ).mpr hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨B.mapAssign e.toEquiv.symm ρ, ?_⟩
    have hkey : B.mapAssign e.toEquiv (B.mapAssign e.toEquiv.symm ρ) = ρ := by
      funext i x
      rw [SOBlock.mapAssign, SOBlock.mapAssign]
      exact congrArg _ (funext fun j => e.toEquiv.apply_symm_apply _)
    rw [← prog.holds_equiv e (B.mapAssign e.toEquiv.symm ρ), hkey]
    exact hρ

end Iso

/-! ### SO-Horn definability -/

variable {L : Language.{0, 0}}

/-- SO-Horn definability only depends on the finite instances of a problem. -/
theorem sigmaSOHornDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax535992.HornFragment.SigmaSOHornDefinable P ↔ Lax535992.HornFragment.SigmaSOHornDefinable Q := by
  constructor <;> rintro ⟨B, k, prog, hprog⟩ <;> refine ⟨B, k, prog, ?_⟩ <;>
    intro A _ _ _ _
  · exact (h A).symm.trans (hprog A)
  · exact (h A).trans (hprog A)

end Lax134656Proofs.DescriptiveComplexity


