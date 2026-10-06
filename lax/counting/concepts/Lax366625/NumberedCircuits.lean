import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Syntax
import Lax535992.CircuitValue
import Lax366625.CountingProblems

/-!
---
title: The number written by a Boolean circuit
type: definition
---
An instance is a Boolean circuit as for the circuit value problem, whose
output gates each hold one binary digit, together with a binary relation
comparing the output gates. When that relation is a linear order on the
output gates, the number written by the circuit is $\sum 2^{r(g)}$ over the
output gates $g$ that derive the value $1$, $r(g)$ being the number of output
gates below $g$; otherwise it is $0$.
-/

namespace Lax366625.NumberedCircuits

open Lax535992.CircuitValue

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive numCircuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : numCircuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : numCircuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : numCircuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : numCircuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : numCircuitRel 1
/-- `out g`: the element `g` is an output gate, holding one digit. -/
  | out : numCircuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : numCircuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : numCircuitRel 2
/-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
  | below : numCircuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits writing a number: the symbols
of circuits, and a comparison of the output gates. -/
def numCircuit : FirstOrder.Language :=
  ⟨fun _ => Empty, numCircuitRel⟩

instance instIsRelationalNumCircuit : FirstOrder.Language.IsRelational numCircuit := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev ncIsTrue : numCircuit.Relations 1 :=
  .isTrue

/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
abbrev ncIsFalse : numCircuit.Relations 1 :=
  .isFalse

/-- `isAnd g`: the element `g` is a conjunction gate. -/
abbrev ncIsAnd : numCircuit.Relations 1 :=
  .isAnd

/-- `isOr g`: the element `g` is a disjunction gate. -/
abbrev ncIsOr : numCircuit.Relations 1 :=
  .isOr

/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
abbrev ncIsNot : numCircuit.Relations 1 :=
  .isNot

/-- `out g`: the element `g` is an output gate, holding one digit. -/
abbrev ncOut : numCircuit.Relations 1 :=
  .out

/-- `left g x`: the gate `g` takes `x` as its first argument. -/
abbrev ncLeft : numCircuit.Relations 2 :=
  .left

/-- `right g x`: the gate `g` takes `x` as its second argument. -/
abbrev ncRight : numCircuit.Relations 2 :=
  .right

/-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
abbrev ncBelow : numCircuit.Relations 2 :=
  .below

open FirstOrder

open Language Structure

/-- Forgetting the comparison of the outputs: the vocabulary of circuits, read
in the vocabulary of circuits writing a number. -/
def circuitOfNum : circuit →ᴸ numCircuit where
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
instance numCircuitStructure (A : Type) [numCircuit.Structure A] :
    circuit.Structure A :=
  circuitOfNum.reduct A

section Semantics

variable {A : Type} [numCircuit.Structure A]

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
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output gates. -/
def OutOrder : Prop :=
  (∀ p : A, RelMap ncOut ![p] → RelMap ncBelow ![p, p]) ∧
    (∀ p q r : A, RelMap ncOut ![p] → RelMap ncOut ![q] → RelMap ncOut ![r] →
      RelMap ncBelow ![p, q] → RelMap ncBelow ![q, r] → RelMap ncBelow ![p, r]) ∧
    (∀ p q : A, RelMap ncOut ![p] → RelMap ncOut ![q] →
      RelMap ncBelow ![p, q] → RelMap ncBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap ncOut ![p] → RelMap ncOut ![q] →
      RelMap ncBelow ![p, q] ∨ RelMap ncBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by a circuit**: each output gate deriving the value
`1` contributes two to the power of its rank among the outputs; `0` unless the
outputs are linearly ordered. -/
noncomputable def circuitNumber : ℕ :=
  if OutOrder A then ∑ᶠ g : A, if OutBit g then 2 ^ outRank g else 0 else 0

end Semantics

open Lax366625.CountingProblems

/-- **The number written by a circuit**, as a counting problem. -/
noncomputable def CircuitNumber : CountingProblem numCircuit :=
  CountingProblem.ofFun fun A _ => circuitNumber A

end Lax366625.NumberedCircuits
