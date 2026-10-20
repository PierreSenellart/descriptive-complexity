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
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.ModelTheory.Graph
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Lax799700.Common
import Lax904597.Sat
import Lax366625.CountingProblems
import Lax366625.CountingSat

/-!
---
title: #2SAT, #HORN-SAT, and #Monotone-2SAT
type: definition
---
The restricted versions of #SAT count the models of a CNF instance in a
class of formulas, and are $0$ on the other instances: #2SAT on the formulas
with at most two literals per clause, #HORN-SAT on the formulas with at most
one positive literal per clause, and #Monotone-2SAT on the formulas with at
most two literals per clause and no negative literal.
-/

namespace Lax859101.CountingRestrictedSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y

end HornSat

open FirstOrder

open Language Structure

section TwoSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most two literal
occurrences: among any three occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostTwo : Prop :=
  ∀ (c : A) (x : Fin 3 → A) (s : Fin 3 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

end TwoSat

open FirstOrder

open Language Structure

section Sentences

variable {α : Type}

variable {A : Type} [sat.Structure A]

/-- No clause has a negative literal. -/
def NoNegative (A : Type) [sat.Structure A] : Prop :=
  ∀ c x : A, RelMap satIsClause ![c] → ¬RelMap satNegIn ![c, x]

end Sentences

open Lax366625.CountingProblems Lax366625.CountingSat

/-- **#2SAT**, as a counting problem. -/
noncomputable def SharpTwoSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν}

/-- **#HORN-SAT**, as a counting problem. -/
noncomputable def SharpHornSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν}

/-- **#Monotone-2SAT**, as a counting problem. -/
noncomputable def SharpMonotoneTwoSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν}

end Lax859101.CountingRestrictedSat
