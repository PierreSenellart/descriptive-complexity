import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Sat

/-!
---
title: Satisfiability of Horn formulas
type: definition
---
An instance is a CNF instance of the NP core. It is Horn when every clause
has at most one positive literal, and it is a yes-instance of HORN-SAT when
it is Horn and satisfiable. HORN-SAT is the decision problem of the
structures isomorphic to such an instance. Instances that are not Horn are
no-instances: the Horn condition is part of the problem, not a promise.
-/

namespace Lax535992.HornSat

open Lax904597.Problems Lax485149.Problems

open Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a CNF instance has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y

/-- A CNF instance is a yes-instance of HORN-SAT if every clause
has at most one positive literal and the CNF is satisfiable. -/
def HornSatisfiable : Prop :=
  AtMostOnePositive A ∧ Satisfiable A

end HornSat

/-- HORN-SAT: is the CNF instance Horn and satisfiable? -/
def HORNSAT : DecisionProblem sat := DecisionProblem.ofPred fun A _ => HornSatisfiable A

end Lax535992.HornSat
