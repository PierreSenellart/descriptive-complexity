import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Lax366625.CountingSat
import Lax904597.Sat
import Lax366625.CountingProblems

/-!
---
title: #DNF
type: definition
---
An instance of the CNF vocabulary of the NP core is read as a DNF formula,
its clauses being the terms. A model is a set of variables that makes every
literal of some term true. #DNF counts the models.
-/

namespace Lax859101.CountingDnf

open Lax366625.CountingSat Lax904597.Sat

open FirstOrder

open Language Structure

section Models

variable (A : Type) [sat.Structure A]

/-- The set `ν` of true variables is a model of the DNF formula: it makes every
literal of some term true, and consists of variables of the formula. -/
def DnfModel (ν : A → Prop) : Prop :=
  (∃ c : A, RelMap satIsClause ![c] ∧
    ∀ x : A, (RelMap satPosIn ![c, x] → ν x) ∧ (RelMap satNegIn ![c, x] → ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

end Models

open Lax366625.CountingProblems

/-- **#DNF**, as a counting problem. -/
noncomputable def SharpDNF : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // DnfModel A ν}

end Lax859101.CountingDnf
