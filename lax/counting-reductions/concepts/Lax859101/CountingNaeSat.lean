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
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Set.Finite.Lemmas
import Lax366625.CountingSat
import Lax799700.NaeSat
import Lax799700.SetFamily
import Lax904597.Sat
import Lax366625.CountingProblems

/-!
---
title: #NAE-SAT and #Set Splitting
type: definition
---
A not-all-equal model of a CNF instance is a set of variables such that
every clause has a true literal and a false one; #NAE-SAT counts them. On a
set system, a splitting color class is a set of ground elements meeting
every set of the family and its complement; #Set Splitting counts them.
-/

namespace Lax859101.CountingNaeSat

open Lax366625.CountingSat Lax799700.NaeSat Lax799700.SetFamily Lax904597.Sat

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [sat.Structure A]

/-- A **not-all-equal model**: a not-all-equal proper set of variables of the
formula. -/
def NAEModel (ν : A → Prop) : Prop :=
  NAEProper ν ∧ ∀ x : A, ν x → SatOccurs A x

end Problem

section Split

variable (A : Type) [setSystem.Structure A]

/-- A **splitting color class**: a set of ground elements meeting every set of
the family and its complement. -/
def SplitColoring (S : A → Prop) : Prop :=
  (∀ x : A, S x → SSElem x) ∧ ∀ f : A, SSFam f →
    (∃ x : A, SSElem x ∧ SSMem x f ∧ S x) ∧ ∃ x : A, SSElem x ∧ SSMem x f ∧ ¬S x

end Split

open Lax366625.CountingProblems

/-- **#NAE-SAT**, as a counting problem. -/
noncomputable def SharpNAESAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // NAEModel A ν}

/-- **#Set Splitting**, as a counting problem. -/
noncomputable def SharpSetSplitting : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // SplitColoring A S}

end Lax859101.CountingNaeSat
