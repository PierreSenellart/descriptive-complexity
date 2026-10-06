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
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Prod
import Lax799700.Knapsack
import Lax799700.ZeroOneIP
import Lax904597.Machines
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting knapsack and 0-1 integer programming solutions
type: definition
---
The weights are written in binary as in the NP catalog. #Knapsack counts the
sets of items whose total weight is exactly the target, and #0-1 Integer
Programming counts the $0$-$1$ vectors satisfying every constraint of the
system with equality.
-/

namespace Lax280166.CountingKnapsacks

open Lax799700.Knapsack Lax799700.ZeroOneIP Lax904597.Machines

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [binWeights.Structure A]

/-- The set `S` of items is a solution: the instance is finite, its order is
linear, and the weights of `S` sum exactly to the target. -/
def KnapsackSol (S : A → Prop) : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧ (∀ i, S i → BWItem i) ∧
    (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

open FirstOrder

open Language Structure

variable (A : Type) [zeroOneIP.Structure A]

/-- The set `x` of columns is a solution: the instance is finite, its order is
linear, and every equation holds. -/
def ZeroOneSol (x : A → Prop) : Prop :=
  Finite A ∧ IsLinOrd (IPLe (A := A)) ∧ (∀ j, x j → IPCol j) ∧
    ∀ r, IPRow r → (∑ᶠ j ∈ {j | x j}, IPCoefVal r j) = IPRhsVal r

end Solutions

open Lax366625.CountingProblems

/-- **#Knapsack**, as a counting problem. -/
noncomputable def SharpKnapsack : CountingProblem Lax799700.Knapsack.binWeights :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // KnapsackSol A S}

/-- **#0-1 Integer Programming**, as a counting problem. -/
noncomputable def SharpZeroOneIP : CountingProblem Lax799700.ZeroOneIP.zeroOneIP :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {x : A → Prop // ZeroOneSol A x}

end Lax280166.CountingKnapsacks
