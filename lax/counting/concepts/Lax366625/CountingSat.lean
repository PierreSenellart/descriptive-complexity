import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Lax904597.Sat
import Lax366625.CountingProblems

/-!
---
title: #SAT, counting the models of a CNF formula
type: definition
---
An instance is a CNF instance of the NP core. Its variables are the elements
occurring in some clause, and a model is a set of variables such that every
clause contains a true literal. #SAT counts the models: its value on an
instance is the number of models, the elements that are not variables being
always false.
-/

namespace Lax366625.CountingSat

open Lax904597.Sat

open FirstOrder

open Language Structure

section Sat

variable (A : Type) [sat.Structure A]

/-- The element `x` is a variable of the CNF formula: it occurs, positively or
negatively, in some clause. The decision problem does not need the notion –
an element in no clause is harmless – but everything that *counts* assignments
does, and so does any reduction that must not give such an element a truth
value to choose. -/
def SatOccurs (x : A) : Prop :=
  ∃ c : A, RelMap satIsClause ![c] ∧ (RelMap satPosIn ![c, x] ∨ RelMap satNegIn ![c, x])

end Sat

open FirstOrder

open Language Structure

section Models

variable (A : Type) [sat.Structure A]

/-- The set `ν` of true variables is a model of the CNF formula: every clause
contains a true literal, and `ν` consists of variables of the formula. -/
def SatModel (ν : A → Prop) : Prop :=
  (∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

end Models

open Lax366625.CountingProblems

/-- **#SAT**: the number of models of a CNF formula. -/
noncomputable def SharpSAT : CountingProblem sat :=
  CountingProblem.ofFun fun A _ => Nat.card {ν : A → Prop // SatModel A ν}

end Lax366625.CountingSat
