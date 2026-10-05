/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Defs
import DescriptiveComplexity.Counting
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite

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
  below `g` (`DescriptiveComplexity.outRank`). When `below` linearly orders the
  output gates, this is the number whose binary digits are their values, the
  lowest gate holding the least significant digit; nothing is required of
  `below` otherwise, and the definition is read as it stands.
-/

namespace FirstOrder

namespace Language

/-- The relational language of Boolean circuits writing a number: the symbols
of `FirstOrder.Language.circuit`, and a comparison of the output gates. -/
fo_language numCircuit with nc where
  /-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  isTrue : 1
  /-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  isFalse : 1
  /-- `isAnd g`: the element `g` is a conjunction gate. -/
  isAnd : 1
  /-- `isOr g`: the element `g` is a disjunction gate. -/
  isOr : 1
  /-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  isNot : 1
  /-- `out g`: the element `g` is an output gate, holding one digit. -/
  out : 1
  /-- `left g x`: the gate `g` takes `x` as its first argument. -/
  left : 2
  /-- `right g x`: the gate `g` takes `x` as its second argument. -/
  right : 2
  /-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
  below : 2

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The underlying circuit -/

/-- Forgetting the comparison of the outputs: the vocabulary of circuits, read
in the vocabulary of circuits writing a number. -/
def circuitOfNum : Language.circuit →ᴸ Language.numCircuit where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R =>
    match n, R with
    | _, .isTrue => ncIsTrue
    | _, .isFalse => ncIsFalse
    | _, .isAnd => ncIsAnd
    | _, .isOr => ncIsOr
    | _, .isNot => ncIsNot
    | _, .out => ncOut
    | _, .left => ncLeft
    | _, .right => ncRight

/-- A circuit writing a number is a circuit. -/
instance numCircuitStructure (A : Type) [Language.numCircuit.Structure A] :
    Language.circuit.Structure A :=
  circuitOfNum.reduct A

/-- An isomorphism of circuits writing a number is an isomorphism of the
underlying circuits. -/
def numCircuitEquiv {A B : Type} [Language.numCircuit.Structure A]
    [Language.numCircuit.Structure B] (e : A ≃[Language.numCircuit] B) :
    A ≃[Language.circuit] B :=
  ⟨e.toEquiv, fun {_} f _ => isEmptyElim f,
    fun {_} r x => e.map_rel' (circuitOfNum.onRelation r) x⟩

/-! ### The number -/

section Semantics

variable {A : Type} [Language.numCircuit.Structure A]

/-- The output gate `g` holds the digit `1`. -/
def OutBit (g : A) : Prop :=
  RelMap ncOut ![g] ∧ GateVal true g

/-- `h` is an output gate strictly below `g`. -/
def LowerOut (g h : A) : Prop :=
  RelMap ncOut ![h] ∧ h ≠ g ∧ RelMap ncBelow ![h, g]

/-- The rank of a gate among the outputs: the number of output gates strictly
below it. -/
noncomputable def outRank (g : A) : ℕ :=
  Nat.card {h : A // LowerOut g h}

variable (A) in
open Classical in
/-- **The number written by a circuit**: each output gate deriving the value
`1` contributes two to the power of its rank among the outputs. -/
noncomputable def circuitNumber : ℕ :=
  ∑ᶠ g : A, if OutBit g then 2 ^ outRank g else 0

end Semantics

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Language.numCircuit.Structure A] [Language.numCircuit.Structure B]

theorem outBit_equiv (e : A ≃[Language.numCircuit] B) (g : A) : OutBit (e g) ↔ OutBit g :=
  and_congr (relMap_equiv₁ e ncOut g).symm
    ⟨fun h => (congrArg (GateVal true) (e.toEquiv.symm_apply_apply g)).mp
        (gateVal_map (numCircuitEquiv e).symm h),
      fun h => gateVal_map (numCircuitEquiv e) h⟩

theorem lowerOut_equiv (e : A ≃[Language.numCircuit] B) (g h : A) :
    LowerOut (e g) (e h) ↔ LowerOut g h :=
  and_congr (relMap_equiv₁ e ncOut h).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e ncBelow h g).symm)

theorem outRank_equiv (e : A ≃[Language.numCircuit] B) (g : A) : outRank (e g) = outRank g :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun h => (lowerOut_equiv e g h).symm)).symm

/-- The number written is isomorphism-invariant. -/
theorem circuitNumber_iso (e : A ≃[Language.numCircuit] B) :
    circuitNumber A = circuitNumber B := by
  classical
  rw [circuitNumber, circuitNumber, ← finsum_comp_equiv e.toEquiv]
  refine finsum_congr fun g => ?_
  change _ = if OutBit (e g) then 2 ^ outRank (e g) else 0
  rw [outRank_equiv e g, if_congr (outBit_equiv e g) rfl rfl]

end Iso

/-- **The number written by a circuit**, as a counting problem on
`Language.numCircuit`-structures: the function counterpart of
`DescriptiveComplexity.CVP`. -/
noncomputable def CircuitNumber : CountingProblem Language.numCircuit where
  Count := fun A inst => @circuitNumber A inst
  iso_invariant := fun e => circuitNumber_iso e

theorem circuitNumber_apply (A : Type) [Language.numCircuit.Structure A] :
    CircuitNumber A = circuitNumber A :=
  rfl

end DescriptiveComplexity
