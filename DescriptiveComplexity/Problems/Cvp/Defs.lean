/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Interpretation

/-!
# The circuit value problem: definition

CVP asks whether a Boolean circuit, given with the values of its input gates,
evaluates its designated output gate to true. It is the canonical
`PTIME`-complete problem of the textbooks ([Ladner 1975][ladner1975circuit]),
and the natural companion of HORN-SAT one level below Cook–Levin: where
HORN-SAT is the syntactic image of the Horn fragment, CVP is the syntactic
image of *evaluation*.

## The vocabulary

`FirstOrder.Language.circuit` marks each element with its kind – a constant
input (`circIsTrue`, `circIsFalse`), a gate (`circIsAnd`, `circIsOr`,
`circIsNot`), the output (`circOut`) – and wires gates to their arguments with
two binary relations `circLeft` and `circRight`, a negation using `circLeft`
alone. Fan-in is therefore two, as in the standard statement; unbounded fan-in
would put an iterated conjunction in the *semantics*, where this library
prefers to keep it in a reduction that walks an order.

## The semantics, and why nothing is assumed about the instance

The value of a gate is defined by the **least** dual-rail derivation
(`DescriptiveComplexity.GateVal`, one inductive family indexed by the value
being derived): `GateVal true g` and `GateVal false g` say that the value `1`,
respectively `0`, is *derivable* at `g` from the constant inputs by the gate
rules. A yes-instance is one whose output gate derives `true`
(`DescriptiveComplexity.CircuitAccepts`).

Three degeneracies are then harmless, and none needs a well-formedness
hypothesis:

* **junk** – an element marked with no kind at all derives nothing, so it can
  neither make the output true nor prevent it;
* **cycles** – a gate on a cycle simply derives no value, the derivation being
  a least fixed point rather than a recursion, so the problem stays a total
  predicate on arbitrary finite structures with no acyclicity condition to
  carry (and, unlike acyclicity, no condition that is not first-order);
* **malformed gates** – an element marked both `circIsAnd` and `circIsOr`, or
  wired to two left arguments, may derive both values; that makes it a
  yes-instance of nothing in particular, not an ill-defined one.

On a well-formed acyclic circuit the derivable value is the value, which is all
the reduction of `DescriptiveComplexity.Problems.Cvp.Hardness` needs, since the
circuit it builds is well-formed and acyclic by construction.

Folding no condition into the yes-instances is the same choice as for 3SAT's
width bound and HORN-SAT's Horn condition made in reverse, and for the same
reason: it keeps CVP a decision problem on arbitrary `Language.circuit`
structures, so that it lives in the same catalog and composes with the same
reductions.
-/

/- The language of Boolean circuits lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.sat`. -/
namespace FirstOrder

namespace Language

/-- The relational language of Boolean circuits: one unary predicate per gate
kind, one marking the output, and two binary predicates wiring a gate to its
arguments. -/
fo_language circuit with circ where
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
  /-- `out g`: the element `g` is an output gate. -/
  out : 1
  /-- `left g x`: the gate `g` takes `x` as its first argument. -/
  left : 2
  /-- `right g x`: the gate `g` takes `x` as its second argument. -/
  right : 2

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [Language.circuit.Structure A]

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

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Language.circuit.Structure A] [Language.circuit.Structure B]

/-- Derivable values transport along an isomorphism: one induction on the
derivation, each rule rebuilt at the image. -/
private theorem gateVal_map (e : A ≃[Language.circuit] B) {b : Bool} {g : A}
    (h : GateVal b g) : GateVal b (e g) := by
  induction h with
  | constTrue hg => exact .constTrue ((relMap_equiv₁ e circIsTrue _).mp hg)
  | constFalse hg => exact .constFalse ((relMap_equiv₁ e circIsFalse _).mp hg)
  | andTrue hg hl hr _ _ ihl ihr =>
    exact .andTrue ((relMap_equiv₁ e circIsAnd _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hl) ((relMap_equiv₂ e circRight _ _).mp hr) ihl ihr
  | andFalseLeft hg hl _ ihl =>
    exact .andFalseLeft ((relMap_equiv₁ e circIsAnd _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hl) ihl
  | andFalseRight hg hr _ ihr =>
    exact .andFalseRight ((relMap_equiv₁ e circIsAnd _).mp hg)
      ((relMap_equiv₂ e circRight _ _).mp hr) ihr
  | orTrueLeft hg hl _ ihl =>
    exact .orTrueLeft ((relMap_equiv₁ e circIsOr _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hl) ihl
  | orTrueRight hg hr _ ihr =>
    exact .orTrueRight ((relMap_equiv₁ e circIsOr _).mp hg)
      ((relMap_equiv₂ e circRight _ _).mp hr) ihr
  | orFalse hg hl hr _ _ ihl ihr =>
    exact .orFalse ((relMap_equiv₁ e circIsOr _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hl) ((relMap_equiv₂ e circRight _ _).mp hr) ihl ihr
  | notTrue hg hi _ ihi =>
    exact .notTrue ((relMap_equiv₁ e circIsNot _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hi) ihi
  | notFalse hg hi _ ihi =>
    exact .notFalse ((relMap_equiv₁ e circIsNot _).mp hg)
      ((relMap_equiv₂ e circLeft _ _).mp hi) ihi

private theorem circuitAccepts_of_iso (e : A ≃[Language.circuit] B)
    (h : CircuitAccepts A) : CircuitAccepts B := by
  obtain ⟨g, hout, hval⟩ := h
  exact ⟨e g, (relMap_equiv₁ e circOut g).mp hout, gateVal_map e hval⟩

/-- Acceptance is isomorphism-invariant. -/
theorem circuitAccepts_iso (e : A ≃[Language.circuit] B) :
    CircuitAccepts A ↔ CircuitAccepts B :=
  ⟨circuitAccepts_of_iso e, circuitAccepts_of_iso e.symm⟩

end Iso

/-- **CVP**, the circuit value problem, as a problem on
`Language.circuit`-structures: does the output gate derive the value `1`? -/
def CVP : DecisionProblem Language.circuit where
  Holds := fun A inst => @CircuitAccepts A inst
  iso_invariant := fun e => circuitAccepts_iso e

end DescriptiveComplexity
