import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Lemmas
import Lax366625.CountingSat
import Lax799700.OneInSat
import Lax904597.Sat
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems
import Lax366625.CountingSat
import Lax799700.ThreeSat

/-!
---
title: Counting the models of 3-CNF and 1-in-CNF formulas
type: definition
---
The instances are the CNF instances of the NP core. #3SAT counts the models
of an instance whose clauses have at most three literals each, and is $0$ on
the others. #1-in-SAT counts the 1-in-models: the sets of variables such
that every clause contains exactly one true literal.
-/

namespace Lax280166.CountingSatVariants

open Lax366625.CountingSat Lax799700.OneInSat Lax904597.Sat

open FirstOrder

open Language Structure

/-- The set `ν` of true variables is an exactly-one model of the CNF formula:
every clause has exactly one true literal, and `ν` consists of variables of
the formula. -/
def OneInModel (A : Type) [sat.Structure A] (ν : A → Prop) : Prop :=
  OneInProper ν ∧ ∀ x : A, ν x → SatOccurs A x

open Lax366625.CountingProblems Lax366625.CountingSat Lax799700.ThreeSat

/-- **#3SAT**, as a counting problem. -/
noncomputable def SharpThreeSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν}

/-- **#1-in-SAT**, as a counting problem. -/
noncomputable def SharpOneInSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // OneInModel A ν}

end Lax280166.CountingSatVariants
