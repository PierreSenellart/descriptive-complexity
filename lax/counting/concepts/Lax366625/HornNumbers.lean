import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Lax535992.HornSat
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax366625.CountingProblems

/-!
---
title: The number written by unit propagation
type: definition
---
An instance is a CNF instance of the NP core together with a mark on the
output variables and a binary relation comparing them. A variable is forced
when unit propagation derives it: when it is the positive literal of a
clause all of whose negative literals are forced earlier. When the instance
is a satisfiable Horn formula and the comparison is a linear order on the
output variables, the number written is $\sum 2^{r(x)}$ over the forced
output variables $x$, $r(x)$ being the number of output variables below
$x$; otherwise it is $0$.
-/

namespace Lax366625.HornNumbers

open Lax535992.HornSat Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section LeastModel

variable {A : Type} [sat.Structure A]

/-- The stages of unit propagation: `ForcedIn n x` says that `x` is the
positive literal of a clause whose negative literals are all forced in fewer
than `n` rounds. -/
def ForcedIn : ℕ → A → Prop
  | 0, _ => False
  | n + 1, x => ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → ForcedIn n y

/-- A variable is *forced* when some stage forces it. On a Horn formula this
is the least model of the implications. -/
def Forced (x : A) : Prop := ∃ n, ForcedIn n x

end LeastModel

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digitOrderRel : ℕ → Type where
/-- `out x`: the element `x` holds one digit. -/
  | out : digitOrderRel 1
/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  | below : digitOrderRel 2
  deriving DecidableEq

/-- The symbols reading a number off a set of marked elements. -/
def digitOrder : FirstOrder.Language :=
  ⟨fun _ => Empty, digitOrderRel⟩

instance instIsRelationalDigitOrder : FirstOrder.Language.IsRelational digitOrder := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `out x`: the element `x` holds one digit. -/
abbrev dgoOut : digitOrder.Relations 1 :=
  .out

/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
abbrev dgoBelow : digitOrder.Relations 2 :=
  .below

/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := sat.sum digitOrder

open FirstOrder

open Language Structure

/-- “Is an output variable”. -/
abbrev hnOut : satOut.Relations 1 := Sum.inr dgoOut

/-- The comparison of the output variables. -/
abbrev hnBelow : satOut.Relations 2 := Sum.inr dgoBelow

/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [satOut.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satOut).reduct A

section Semantics

variable {A : Type} [satOut.Structure A]

/-- The output variable `x` is forced. -/
def ForcedDigit (x : A) : Prop :=
  RelMap hnOut ![x] ∧ Forced x

/-- `y` is an output variable strictly below `x`. -/
def LowerVar (x y : A) : Prop :=
  RelMap hnOut ![y] ∧ y ≠ x ∧ RelMap hnBelow ![y, x]

/-- The rank of a variable among the outputs: the number of output variables
strictly below it. -/
noncomputable def varRank (x : A) : ℕ :=
  Nat.card {y : A // LowerVar x y}

variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output variables. -/
def VarOrder : Prop :=
  (∀ p : A, RelMap hnOut ![p] → RelMap hnBelow ![p, p]) ∧
    (∀ p q r : A, RelMap hnOut ![p] → RelMap hnOut ![q] → RelMap hnOut ![r] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, r] → RelMap hnBelow ![p, r]) ∧
    (∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] ∨ RelMap hnBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by unit propagation**: each forced output variable
contributes two to the power of its rank among the outputs. Instances that are
not satisfiable Horn formulas, or whose outputs are not linearly ordered,
write `0`. -/
noncomputable def hornNumber : ℕ :=
  if HornSatisfiable A ∧ VarOrder A then ∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0
  else 0

end Semantics

open Lax366625.CountingProblems

/-- **The number written by unit propagation**, as a counting problem. -/
noncomputable def HornNumber : CountingProblem satOut :=
  CountingProblem.ofFun fun A _ => hornNumber A

end Lax366625.HornNumbers
