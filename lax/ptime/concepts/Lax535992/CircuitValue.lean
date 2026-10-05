import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: The circuit value problem
type: definition
---
An instance is a Boolean circuit given as a structure: its elements are
gates, each possibly marked as a constant true, a constant false, a
conjunction, a disjunction or a negation, some gates are marked as outputs,
and two binary relations wire a gate to its left and right arguments, a
negation reading its left argument. The values of the gates are derived
inductively, on two rails: a constant has its value; a conjunction is true
when a left and a right argument are true, and false when some argument is
false; a disjunction dually; a negation is true when its argument is false
and false when it is true. The derivation is a least fixed point, so a gate
on a cycle, or with missing arguments, derives no value. The instance is a
yes-instance of CVP when some output gate derives the value true; CVP is the
decision problem of the structures isomorphic to such an instance.
-/

namespace Lax535992.CircuitValue

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive circuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : circuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : circuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : circuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : circuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : circuitRel 1
/-- `out g`: the element `g` is an output gate. -/
  | out : circuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : circuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : circuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits: one unary predicate per gate
kind, one marking the output, and two binary predicates wiring a gate to its
arguments. -/
def circuit : FirstOrder.Language :=
  ⟨fun _ => Empty, circuitRel⟩

instance instIsRelationalCircuit : FirstOrder.Language.IsRelational circuit := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev circIsTrue : circuit.Relations 1 :=
  .isTrue

/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
abbrev circIsFalse : circuit.Relations 1 :=
  .isFalse

/-- `isAnd g`: the element `g` is a conjunction gate. -/
abbrev circIsAnd : circuit.Relations 1 :=
  .isAnd

/-- `isOr g`: the element `g` is a disjunction gate. -/
abbrev circIsOr : circuit.Relations 1 :=
  .isOr

/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
abbrev circIsNot : circuit.Relations 1 :=
  .isNot

/-- `out g`: the element `g` is an output gate. -/
abbrev circOut : circuit.Relations 1 :=
  .out

/-- `left g x`: the gate `g` takes `x` as its first argument. -/
abbrev circLeft : circuit.Relations 2 :=
  .left

/-- `right g x`: the gate `g` takes `x` as its second argument. -/
abbrev circRight : circuit.Relations 2 :=
  .right

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [circuit.Structure A]

/-- **The value derivable at a gate**, as one inductive family indexed by the
value being derived: `GateVal true g` says that `g` evaluates to `1`,
`GateVal false g` that it evaluates to `0`. Being an inductive predicate, it is
the *least* pair of rails closed under the gate rules, so a gate whose
arguments derive nothing – including one on a cycle – derives nothing.

The rules are the usual ones read in both polarities: a conjunction is true
when both arguments are, false as soon as one is; a disjunction dually; a
negation swaps the rails. -/
inductive GateVal : Bool → A → Prop
  /-- A constant `1` input derives `true`. -/
  | constTrue {g : A} (h : RelMap circIsTrue ![g]) : GateVal true g
  /-- A constant `0` input derives `false`. -/
  | constFalse {g : A} (h : RelMap circIsFalse ![g]) : GateVal false g
  /-- A conjunction with both arguments true derives `true`. -/
  | andTrue {g l r : A} (hg : RelMap circIsAnd ![g]) (hl : RelMap circLeft ![g, l])
      (hr : RelMap circRight ![g, r]) (vl : GateVal true l) (vr : GateVal true r) :
      GateVal true g
  /-- A conjunction with a false first argument derives `false`. -/
  | andFalseLeft {g l : A} (hg : RelMap circIsAnd ![g]) (hl : RelMap circLeft ![g, l])
      (vl : GateVal false l) : GateVal false g
  /-- A conjunction with a false second argument derives `false`. -/
  | andFalseRight {g r : A} (hg : RelMap circIsAnd ![g]) (hr : RelMap circRight ![g, r])
      (vr : GateVal false r) : GateVal false g
  /-- A disjunction with a true first argument derives `true`. -/
  | orTrueLeft {g l : A} (hg : RelMap circIsOr ![g]) (hl : RelMap circLeft ![g, l])
      (vl : GateVal true l) : GateVal true g
  /-- A disjunction with a true second argument derives `true`. -/
  | orTrueRight {g r : A} (hg : RelMap circIsOr ![g]) (hr : RelMap circRight ![g, r])
      (vr : GateVal true r) : GateVal true g
  /-- A disjunction with both arguments false derives `false`. -/
  | orFalse {g l r : A} (hg : RelMap circIsOr ![g]) (hl : RelMap circLeft ![g, l])
      (hr : RelMap circRight ![g, r]) (vl : GateVal false l) (vr : GateVal false r) :
      GateVal false g
  /-- A negation with a false argument derives `true`. -/
  | notTrue {g i : A} (hg : RelMap circIsNot ![g]) (hi : RelMap circLeft ![g, i])
      (vi : GateVal false i) : GateVal true g
  /-- A negation with a true argument derives `false`. -/
  | notFalse {g i : A} (hg : RelMap circIsNot ![g]) (hi : RelMap circLeft ![g, i])
      (vi : GateVal true i) : GateVal false g

variable (A) in
/-- A `Language.circuit`-structure is a yes-instance when some output gate
derives the value `1`. -/
def CircuitAccepts : Prop :=
  ∃ g : A, RelMap circOut ![g] ∧ GateVal true g

end Semantics

/-- CVP, the circuit value problem: does some output gate evaluate to `1`? -/
def CVP : DecisionProblem circuit := DecisionProblem.ofPred fun A _ => CircuitAccepts A

end Lax535992.CircuitValue
