/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.SecondOrder
import Lax895169Proofs.DescriptiveComplexity.Ordered
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

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax895169Proofs.DescriptiveComplexity.KromClause
end Lax895169Proofs.DescriptiveComplexity.KromClause

namespace Lax895169Proofs.DescriptiveComplexity.KromLit
end Lax895169Proofs.DescriptiveComplexity.KromLit

namespace Lax895169Proofs.DescriptiveComplexity.KromProgram
end Lax895169Proofs.DescriptiveComplexity.KromProgram

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.KromFragment (KromClause KromLit KromProgram SigmaSOKromDefinable)
end Lax895169Proofs.DescriptiveComplexity

/-!
# SO-Krom: existential second-order logic with a Krom kernel

The fragment SO-Krom of Grädel ([Grädel 1992][gradel1992capturing]): existential
second-order sentences whose first-order kernel is a conjunction of *Krom
clauses* – 2-clauses – in the quantified relation variables. On ordered
structures SO-Krom captures nondeterministic logarithmic space, the NL analogue
of the SO-Horn characterization of polynomial time
(`DescriptiveComplexity.SecondOrderHorn`).

## Horn and Krom, side by side

Both fragments restrict the occurrences of the *second-order* variables only,
leaving the input vocabulary unconstrained – it is *evaluated* in the
structure, not guessed. They ration the guessed relations differently:

* SO-Horn: any number of negative second-order atoms, **at most one positive**.
  A satisfiable Horn formula has a *least* model, computable by unit
  propagation, which is what makes the guess deterministic and the class P.
* SO-Krom: **at most two second-order atoms**, of either sign. A 2-CNF has no
  least model, so the guess stays a genuine guess; what keeps it below NP is
  that binary clauses propagate one implication at a time, i.e., along a *path*.
  Satisfiability of the instantiated kernel is 2-SAT, decided by reachability
  in the implication graph.

Neither fragment contains the other: Horn clauses may be arbitrarily wide,
Krom clauses may have two positive literals.

## The kernel, as data

As in the Horn case, the kernel is represented as data rather than carved out
of `FirstOrder.Language.BoundedFormula` by a syntactic predicate. A clause is

```
guard(x̄) → ℓ₁ ∨ ℓ₂
```

where each `ℓᵢ` is a *signed* atom in the relation variables
(`DescriptiveComplexity.KromLit`) and `guard` is an arbitrary first-order formula over
the input vocabulary alone (in the definability notion below, over its ordered
expansion). A `DescriptiveComplexity.KromClause` carries its guard and its two literals
as `Option`s, so unit clauses and the empty clause (`guard → ⊥`, the goal
clause of the Horn presentation) need no separate treatment; a
`DescriptiveComplexity.KromProgram` is a list of clauses sharing `k` universally
quantified first-order variables. This clausal form is what a reduction
consuming an SO-Krom definition needs to see: a discharge emits one
propositional 2-clause per clause and per instantiation of the `k` variables,
its literal signs read off the clause.

`DescriptiveComplexity.SigmaSOKromDefinable` is the resulting definability notion; it is
closed under (ordered) first-order reductions by
`DescriptiveComplexity.SecondOrderKromPull`, which is what makes it a
`DescriptiveComplexity.ComplexityClass` – the class `DescriptiveComplexity.NL` of
`DescriptiveComplexity.LogSpace`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Krom programs -/

/-! ### Semantics -/

section Semantics

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {A : Type} [L.Structure A]

theorem KromLit.slotHolds_iff {o : Option (Lax485149.KromFragment.KromLit B k)} {ρ : B.Assignment A}
    {v : Fin k → A} : Lax485149.KromFragment.KromLit.slotHolds o ρ v ↔ ∃ l ∈ o, l.Holds ρ v := by
  cases o with
  | none => simp [Lax485149.KromFragment.KromLit.slotHolds]
  | some l => simp [Lax485149.KromFragment.KromLit.slotHolds]

end Semantics

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (slotHolds_iff)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {A : Type} [L.Structure A]

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem KromLit.holds_equiv (e : M ≃[L] N) (l : Lax485149.KromFragment.KromLit B k) (ρ : B.Assignment M)
    (v : Fin k → M) :
    l.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ l.Holds ρ v := by
  rw [Lax485149.KromFragment.KromLit.Holds, Lax485149.KromFragment.KromLit.Holds]
  cases l.positive with
  | false => exact not_congr (l.atom.holds_equiv e ρ v)
  | true => exact l.atom.holds_equiv e ρ v

end Iso

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (holds_equiv)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem KromLit.slotHolds_equiv (e : M ≃[L] N) (o : Option (Lax485149.KromFragment.KromLit B k))
    (ρ : B.Assignment M) (v : Fin k → M) :
    Lax485149.KromFragment.KromLit.slotHolds o (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔
      Lax485149.KromFragment.KromLit.slotHolds o ρ v := by
  rw [Lax485149.KromFragment.KromLit.slotHolds, Lax485149.KromFragment.KromLit.slotHolds]
  cases o with
  | none => exact Iff.rfl
  | some l => exact l.holds_equiv e ρ v

end Iso

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromLit

export Lax895169Proofs.DescriptiveComplexity.KromLit (slotHolds_equiv)

end Lax485149.KromFragment.KromLit

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem KromClause.holds_equiv (e : M ≃[L] N) (c : Lax485149.KromFragment.KromClause L B k)
    (ρ : B.Assignment M) (v : Fin k → M) :
    c.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ c.Holds ρ v :=
  imp_congr (StrongHomClass.realize_formula e c.guard)
    (or_congr (KromLit.slotHolds_equiv e c.lit₁ ρ v) (KromLit.slotHolds_equiv e c.lit₂ ρ v))

end Iso

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromClause

export Lax895169Proofs.DescriptiveComplexity.KromClause (holds_equiv)

end Lax485149.KromFragment.KromClause

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

theorem KromProgram.holds_equiv (e : M ≃[L] N) (prog : Lax485149.KromFragment.KromProgram L B k)
    (ρ : B.Assignment M) : prog.Holds (B.mapAssign e.toEquiv ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    exact (c.holds_equiv e ρ v).mp (h (fun j => e (v j)) c hc)
  · intro h v c hc
    have := (c.holds_equiv e ρ fun j => e.symm (v j)).mpr
      (h (fun j => e.symm (v j)) c hc)
    simpa using this

end Iso

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (holds_equiv)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

/-- **Krom satisfiability is isomorphism-invariant**: a program has a
satisfying assignment on one structure iff it has one on any isomorphic
structure. -/
theorem KromProgram.exists_holds_equiv (e : M ≃[L] N) (prog : Lax485149.KromFragment.KromProgram L B k) :
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

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.KromFragment.KromProgram

export Lax895169Proofs.DescriptiveComplexity.KromProgram (exists_holds_equiv)

end Lax485149.KromFragment.KromProgram

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Iso

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {M N : Type}

variable [L.Structure M] [L.Structure N]

end Iso

/-! ### SO-Krom definability -/

variable {L : Language.{0, 0}}

/-- SO-Krom definability only depends on the finite instances of a problem. -/
theorem sigmaSOKromDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax485149.KromFragment.SigmaSOKromDefinable P ↔ Lax485149.KromFragment.SigmaSOKromDefinable Q := by
  constructor <;> rintro ⟨B, k, prog, hprog⟩ <;> refine ⟨B, k, prog, ?_⟩ <;>
    intro A _ _ _ _
  · exact (h A).symm.trans (hprog A)
  · exact (h A).trans (hprog A)

end Lax895169Proofs.DescriptiveComplexity


