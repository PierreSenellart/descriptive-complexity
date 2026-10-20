import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Even
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: PARITY, the parity of a marked subset
type: definition
---
An instance is a finite set with a marked subset: a structure over the
vocabulary with one unary relation. It is a yes-instance of PARITY when the
number of marked elements is even; PARITY is the decision problem of the
structures isomorphic to such an instance. This is the problem of the
classical lower bounds for bounded-depth circuits, as opposed to EVEN, which
asks for the parity of the whole universe.
-/

namespace Lax945089.Parity

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedSetRel : ℕ → Type where
/-- `mark x`: the element `x` belongs to the marked subset. -/
  | mark : markedSetRel 1
  deriving DecidableEq

/-- The relational vocabulary of a *marked subset*: a finite set with a
distinguished subset of it. -/
def markedSet : FirstOrder.Language :=
  ⟨fun _ => Empty, markedSetRel⟩

instance instIsRelationalMarkedSet : FirstOrder.Language.IsRelational markedSet := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `mark x`: the element `x` belongs to the marked subset. -/
abbrev markedSetMark : markedSet.Relations 1 :=
  .mark

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [markedSet.Structure A]

/-- The marked subset of a structure. -/
def Marked : Set A :=
  {x : A | RelMap markedSetMark ![x]}

end Problem

/-- PARITY: is the marked subset of even size? -/
def PARITY : DecisionProblem markedSet :=
  DecisionProblem.ofPred fun A _ => Even (Marked A).ncard

end Lax945089.Parity
