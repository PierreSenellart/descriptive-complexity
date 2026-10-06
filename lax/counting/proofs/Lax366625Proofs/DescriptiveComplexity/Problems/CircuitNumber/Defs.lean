/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.Cvp.Defs
import Lax366625Proofs.DescriptiveComplexity.Counting
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
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

namespace Lax366625.NumberedCircuits
end Lax366625.NumberedCircuits

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.NumberedCircuits (LowerOut OutBit OutOrder circuitNumber circuitOfNum numCircuitStructure outRank)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.CircuitValue (GateVal)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.NumberedCircuits (ncBelow ncIsAnd ncIsFalse ncIsNot ncIsOr ncIsTrue ncLeft ncOut ncRight numCircuit)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax535992.CircuitValue (circuit)
end FirstOrder.Language

/-!
# The number written by a circuit: definition

The function counterpart of the circuit value problem
(`DescriptiveComplexity.CVP`). An instance is a Boolean circuit with *several*
output gates and a comparison `below` between them; the outputs, read in that
order, are the binary digits of a natural number, and
`DescriptiveComplexity.CircuitNumber` is the problem of computing it.

* `FirstOrder.Language.numCircuit`: the vocabulary of circuits
  (`FirstOrder.Language.circuit`) with one more binary symbol, `below`.
* A circuit over it is a circuit in the sense of `DescriptiveComplexity.CVP`,
  by forgetting `below` (`DescriptiveComplexity.circuitOfNum`): its gates are
  evaluated by `DescriptiveComplexity.GateVal`.
* `DescriptiveComplexity.circuitNumber`: an output gate `g` deriving the value
  `1` contributes `2 ^ r`, where `r` is the number of output gates strictly
  below `g` (`DescriptiveComplexity.outRank`). This is the number whose binary
  digits are the values of the output gates, the lowest holding the least
  significant digit, when `below` linearly orders the output gates
  (`DescriptiveComplexity.OutOrder`); an instance whose `below` does not
  writes `0`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The underlying circuit -/

/-- An isomorphism of circuits writing a number is an isomorphism of the
underlying circuits. -/
def numCircuitEquiv {A B : Type} [Lax366625.NumberedCircuits.numCircuit.Structure A]
    [Lax366625.NumberedCircuits.numCircuit.Structure B] (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) :
    A ≃[Lax535992.CircuitValue.circuit] B :=
  ⟨e.toEquiv, fun {_} f _ => isEmptyElim f,
    fun {_} r x => e.map_rel' (Lax366625.NumberedCircuits.circuitOfNum.onRelation r) x⟩

/-! ### The number -/

section Semantics

variable {A : Type} [Lax366625.NumberedCircuits.numCircuit.Structure A]

end Semantics

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Lax366625.NumberedCircuits.numCircuit.Structure A] [Lax366625.NumberedCircuits.numCircuit.Structure B]

theorem outBit_equiv (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) (g : A) : Lax366625.NumberedCircuits.OutBit (e g) ↔ Lax366625.NumberedCircuits.OutBit g :=
  and_congr (relMap_equiv₁ e Lax366625.NumberedCircuits.ncOut g).symm
    ⟨fun h => (congrArg (Lax535992.CircuitValue.GateVal true) (e.toEquiv.symm_apply_apply g)).mp
        (gateVal_map (numCircuitEquiv e).symm h),
      fun h => gateVal_map (numCircuitEquiv e) h⟩

theorem lowerOut_equiv (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) (g h : A) :
    Lax366625.NumberedCircuits.LowerOut (e g) (e h) ↔ Lax366625.NumberedCircuits.LowerOut g h :=
  and_congr (relMap_equiv₁ e Lax366625.NumberedCircuits.ncOut h).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e Lax366625.NumberedCircuits.ncBelow h g).symm)

theorem outRank_equiv (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) (g : A) : Lax366625.NumberedCircuits.outRank (e g) = Lax366625.NumberedCircuits.outRank g :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun h => (lowerOut_equiv e g h).symm)).symm

theorem outOrder_equiv (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) : Lax366625.NumberedCircuits.OutOrder A ↔ Lax366625.NumberedCircuits.OutOrder B := by
  have h1 : ∀ p, (RelMap Lax366625.NumberedCircuits.ncOut ![e p] : Prop) ↔ RelMap Lax366625.NumberedCircuits.ncOut ![p] :=
    fun p => (relMap_equiv₁ e Lax366625.NumberedCircuits.ncOut p).symm
  have h2 : ∀ p q, (RelMap Lax366625.NumberedCircuits.ncBelow ![e p, e q] : Prop) ↔ RelMap Lax366625.NumberedCircuits.ncBelow ![p, q] :=
    fun p q => (relMap_equiv₂ e Lax366625.NumberedCircuits.ncBelow p q).symm
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
theorem circuitNumber_iso (e : A ≃[Lax366625.NumberedCircuits.numCircuit] B) :
    Lax366625.NumberedCircuits.circuitNumber A = Lax366625.NumberedCircuits.circuitNumber B := by
  classical
  have hsum : (∑ᶠ g : A, if Lax366625.NumberedCircuits.OutBit g then 2 ^ Lax366625.NumberedCircuits.outRank g else 0) =
      ∑ᶠ g : B, if Lax366625.NumberedCircuits.OutBit g then 2 ^ Lax366625.NumberedCircuits.outRank g else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun g => ?_
    change _ = if Lax366625.NumberedCircuits.OutBit (e g) then 2 ^ Lax366625.NumberedCircuits.outRank (e g) else 0
    rw [outRank_equiv e g, if_congr (outBit_equiv e g) rfl rfl]
  rw [Lax366625.NumberedCircuits.circuitNumber, Lax366625.NumberedCircuits.circuitNumber, hsum]
  exact if_congr (outOrder_equiv e) rfl rfl

end Iso

/-- **The number written by a circuit**, as a counting problem on
`Language.numCircuit`-structures: the function counterpart of
`DescriptiveComplexity.CVP`. -/
noncomputable def CircuitNumber : Lax366625.CountingProblems.CountingProblem Lax366625.NumberedCircuits.numCircuit where
  Count := fun A inst => @Lax366625.NumberedCircuits.circuitNumber A inst
  iso_invariant := fun e => circuitNumber_iso e

end Lax366625Proofs.DescriptiveComplexity


