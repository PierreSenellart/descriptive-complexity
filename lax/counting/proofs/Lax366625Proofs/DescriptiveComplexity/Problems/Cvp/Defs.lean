/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Vocabulary
import Lax366625Proofs.DescriptiveComplexity.Interpretation
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

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.CircuitValue (CircuitAccepts GateVal)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax535992.CircuitValue (circIsAnd circIsFalse circIsNot circIsOr circIsTrue circLeft circOut circRight circuit)
end FirstOrder.Language

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

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [Lax535992.CircuitValue.circuit.Structure A]

end Semantics

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Lax535992.CircuitValue.circuit.Structure A] [Lax535992.CircuitValue.circuit.Structure B]

/-- Derivable values transport along an isomorphism: one induction on the
derivation, each rule rebuilt at the image. -/
theorem gateVal_map (e : A ≃[Lax535992.CircuitValue.circuit] B) {b : Bool} {g : A}
    (h : Lax535992.CircuitValue.GateVal b g) : Lax535992.CircuitValue.GateVal b (e g) := by
  induction h with
  | constTrue hg => exact .constTrue ((relMap_equiv₁ e Lax535992.CircuitValue.circIsTrue _).mp hg)
  | constFalse hg => exact .constFalse ((relMap_equiv₁ e Lax535992.CircuitValue.circIsFalse _).mp hg)
  | andTrue hg hl hr _ _ ihl ihr =>
    exact .andTrue ((relMap_equiv₁ e Lax535992.CircuitValue.circIsAnd _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hl) ((relMap_equiv₂ e Lax535992.CircuitValue.circRight _ _).mp hr) ihl ihr
  | andFalseLeft hg hl _ ihl =>
    exact .andFalseLeft ((relMap_equiv₁ e Lax535992.CircuitValue.circIsAnd _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hl) ihl
  | andFalseRight hg hr _ ihr =>
    exact .andFalseRight ((relMap_equiv₁ e Lax535992.CircuitValue.circIsAnd _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circRight _ _).mp hr) ihr
  | orTrueLeft hg hl _ ihl =>
    exact .orTrueLeft ((relMap_equiv₁ e Lax535992.CircuitValue.circIsOr _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hl) ihl
  | orTrueRight hg hr _ ihr =>
    exact .orTrueRight ((relMap_equiv₁ e Lax535992.CircuitValue.circIsOr _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circRight _ _).mp hr) ihr
  | orFalse hg hl hr _ _ ihl ihr =>
    exact .orFalse ((relMap_equiv₁ e Lax535992.CircuitValue.circIsOr _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hl) ((relMap_equiv₂ e Lax535992.CircuitValue.circRight _ _).mp hr) ihl ihr
  | notTrue hg hi _ ihi =>
    exact .notTrue ((relMap_equiv₁ e Lax535992.CircuitValue.circIsNot _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hi) ihi
  | notFalse hg hi _ ihi =>
    exact .notFalse ((relMap_equiv₁ e Lax535992.CircuitValue.circIsNot _).mp hg)
      ((relMap_equiv₂ e Lax535992.CircuitValue.circLeft _ _).mp hi) ihi

end Iso

end Lax366625Proofs.DescriptiveComplexity


