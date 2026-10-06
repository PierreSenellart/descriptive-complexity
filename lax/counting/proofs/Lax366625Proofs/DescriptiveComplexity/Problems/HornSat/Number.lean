/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Unsat
import Lax366625Proofs.DescriptiveComplexity.FixedPointOrderTransfer
import Lax366625Proofs.DescriptiveComplexity.Counting
import Lax366625Proofs.DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.BigOperators.Finprod
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.HornNumbers
end Lax366625.HornNumbers

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.HornNumbers (Forced ForcedDigit ForcedIn LowerVar VarOrder hnBelow hnOut hornNumber satOutStructure varRank)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornSat (HornSatisfiable)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.HornNumbers (dgoBelow dgoOut digitOrder satOut)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# The number written by unit propagation: definition

The function counterpart of HORN-SAT (`DescriptiveComplexity.HORNSAT`): some
variables of a Horn formula are marked as *outputs* and compared by
significance, and the problem is to compute the number whose binary digits say
which of them unit propagation forces to be true
(`DescriptiveComplexity.Forced`), i.e., which are true in the least model.

* The vocabulary is the one of CNF instances (`FirstOrder.Language.sat`) with
  two more symbols (`FirstOrder.Language.digitOrder`): `out` marks the output
  variables and `below` compares them.
* `DescriptiveComplexity.hornNumber`: a forced output variable contributes
  `2 ^ r`, where `r` is the number of output variables strictly below it, when
  `below` linearly orders the output variables
  (`DescriptiveComplexity.VarOrder`). An instance that is not a satisfiable
  Horn formula, or whose `below` is not such an order, writes `0`.

This is the problem through which the number written by a machine
(`DescriptiveComplexity.DTMNumber`) is shown hard for FP: the least fixed
point of a system of rules is the least model of a Horn formula, and the
unit-propagation machine leaves that model on its tape.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The propagation closure is isomorphism-invariant -/

section ForcedIso

variable {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]

theorem forcedIn_map (e : A ≃[Lax904597.Sat.sat] B) :
    ∀ (n : ℕ) (x : A), Lax366625.HornNumbers.ForcedIn n x → Lax366625.HornNumbers.ForcedIn n (e x) := by
  intro n
  induction n with
  | zero => exact fun _ h => h.elim
  | succ n ih =>
    rintro x ⟨c, hc, hp, hneg⟩
    refine ⟨e c, (relMap_equiv₁ e Lax904597.Sat.satIsClause c).mp hc, (relMap_equiv₂ e Lax904597.Sat.satPosIn c x).mp hp,
      fun y hy => ?_⟩
    have hy' : RelMap Lax904597.Sat.satNegIn ![c, e.symm y] := by
      refine (relMap_equiv₂ e Lax904597.Sat.satNegIn c (e.symm y)).mpr ?_
      rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y]
    have := ih (e.symm y) (hneg _ hy')
    rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y] at this

theorem forced_equiv (e : A ≃[Lax904597.Sat.sat] B) (x : A) : Lax366625.HornNumbers.Forced (e x) ↔ Lax366625.HornNumbers.Forced x := by
  constructor
  · rintro ⟨n, hn⟩
    have := forcedIn_map e.symm n (e x) hn
    rw [show (e.symm (e x) : A) = x from e.toEquiv.symm_apply_apply x] at this
    exact ⟨n, this⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, forcedIn_map e n x hn⟩

end ForcedIso

/-! ### The number -/

section Semantics

variable {A : Type} [Lax366625.HornNumbers.satOut.Structure A]

end Semantics

section Iso

variable {A B : Type} [Lax366625.HornNumbers.satOut.Structure A] [Lax366625.HornNumbers.satOut.Structure B]

theorem forcedDigit_equiv (e : A ≃[Lax366625.HornNumbers.satOut] B) (x : A) :
    Lax366625.HornNumbers.ForcedDigit (e x) ↔ Lax366625.HornNumbers.ForcedDigit x :=
  and_congr (relMap_equiv₁ e Lax366625.HornNumbers.hnOut x).symm (forced_equiv (reductSumInlEquiv e) x)

theorem lowerVar_equiv (e : A ≃[Lax366625.HornNumbers.satOut] B) (x y : A) :
    Lax366625.HornNumbers.LowerVar (e x) (e y) ↔ Lax366625.HornNumbers.LowerVar x y :=
  and_congr (relMap_equiv₁ e Lax366625.HornNumbers.hnOut y).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e Lax366625.HornNumbers.hnBelow y x).symm)

theorem varRank_equiv (e : A ≃[Lax366625.HornNumbers.satOut] B) (x : A) : Lax366625.HornNumbers.varRank (e x) = Lax366625.HornNumbers.varRank x :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun y => (lowerVar_equiv e x y).symm)).symm

theorem varOrder_equiv (e : A ≃[Lax366625.HornNumbers.satOut] B) : Lax366625.HornNumbers.VarOrder A ↔ Lax366625.HornNumbers.VarOrder B := by
  have h1 : ∀ p, (RelMap Lax366625.HornNumbers.hnOut ![e p] : Prop) ↔ RelMap Lax366625.HornNumbers.hnOut ![p] :=
    fun p => (relMap_equiv₁ e Lax366625.HornNumbers.hnOut p).symm
  have h2 : ∀ p q, (RelMap Lax366625.HornNumbers.hnBelow ![e p, e q] : Prop) ↔ RelMap Lax366625.HornNumbers.hnBelow ![p, q] :=
    fun p q => (relMap_equiv₂ e Lax366625.HornNumbers.hnBelow p q).symm
  constructor
  · rintro ⟨hr, ht, ha, hl⟩
    refine ⟨fun p hp => ?_, fun p q r hp hq hr' hpq hqr => ?_, fun p q hp hq hpq hqp => ?_,
      fun p q hp hq => ?_⟩
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      exact (h2 p p).mpr (hr p ((h1 p).mp hp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      obtain ⟨r, rfl⟩ := e.toEquiv.surjective r
      exact (h2 p r).mpr (ht p q r ((h1 p).mp hp) ((h1 q).mp hq) ((h1 r).mp hr')
        ((h2 p q).mp hpq) ((h2 q r).mp hqr))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact congrArg e (ha p q ((h1 p).mp hp) ((h1 q).mp hq) ((h2 p q).mp hpq) ((h2 q p).mp hqp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact (hl p q ((h1 p).mp hp) ((h1 q).mp hq)).imp (h2 p q).mpr (h2 q p).mpr
  · rintro ⟨hr, ht, ha, hl⟩
    exact ⟨fun p hp => (h2 p p).mp (hr _ ((h1 p).mpr hp)),
      fun p q r hp hq hr' hpq hqr => (h2 p r).mp (ht _ _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)
        ((h1 r).mpr hr') ((h2 p q).mpr hpq) ((h2 q r).mpr hqr)),
      fun p q hp hq hpq hqp => e.toEquiv.injective
        (ha _ _ ((h1 p).mpr hp) ((h1 q).mpr hq) ((h2 p q).mpr hpq) ((h2 q p).mpr hqp)),
      fun p q hp hq => (hl _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)).imp (h2 p q).mp (h2 q p).mp⟩

/-- The number written is isomorphism-invariant. -/
theorem hornNumber_iso (e : A ≃[Lax366625.HornNumbers.satOut] B) : Lax366625.HornNumbers.hornNumber A = Lax366625.HornNumbers.hornNumber B := by
  classical
  have hsum : (∑ᶠ x : A, if Lax366625.HornNumbers.ForcedDigit x then 2 ^ Lax366625.HornNumbers.varRank x else 0) =
      ∑ᶠ x : B, if Lax366625.HornNumbers.ForcedDigit x then 2 ^ Lax366625.HornNumbers.varRank x else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun x => ?_
    change _ = if Lax366625.HornNumbers.ForcedDigit (e x) then 2 ^ Lax366625.HornNumbers.varRank (e x) else 0
    rw [varRank_equiv e x, if_congr (forcedDigit_equiv e x) rfl rfl]
  rw [Lax366625.HornNumbers.hornNumber, Lax366625.HornNumbers.hornNumber, hsum]
  exact if_congr (and_congr (hornSatisfiable_iso (reductSumInlEquiv e)) (varOrder_equiv e)) rfl rfl

end Iso

/-- **The number written by unit propagation**, as a counting problem on
`Language.satOut`-structures: the function counterpart of
`DescriptiveComplexity.HORNSAT`. -/
noncomputable def HornNumber : Lax366625.CountingProblems.CountingProblem Lax366625.HornNumbers.satOut where
  Count := fun A inst => @Lax366625.HornNumbers.hornNumber A inst
  iso_invariant := fun e => hornNumber_iso e

end Lax366625Proofs.DescriptiveComplexity


