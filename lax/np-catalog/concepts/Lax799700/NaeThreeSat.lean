import Mathlib.Data.Set.Finite.Lemmas
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
import Mathlib.Data.Set.Card
import Lax799700.NaeSat
import Lax799700.ThreeSat
import Lax904597.Sat
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Not-all-equal 3SAT
type: theorem
---
NAE-3SAT is the width-three restriction of NAE-SAT: a CNF structure is a
yes-instance when every clause has at most three literal occurrences, the
promise 3SAT uses, and some assignment gives every clause both a true and
a false literal. Both reductions are the interpretations of the SAT and
3SAT pair applied unchanged: membership through the identity-like
reduction to NAE-SAT, hardness through the clause-splitting ordered
reduction from NAE-SAT, whose chain of pieces also works for the
not-all-equal reading. Its value in the catalog is as a reduction source,
for Max Cut and for job sequencing.

-/

namespace Lax799700.NaeThreeSat

open Lax799700.NaeSat Lax799700.ThreeSat Lax904597.Sat

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [sat.Structure A]

/-- A `Language.sat`-structure is a yes-instance of NAE-3SAT if every clause
has at most three literal occurrences and some assignment gives every clause
both a true and a false literal. -/
def NAEThreeSatisfiable : Prop :=
  WidthAtMostThree A ∧ NAESatisfiable A

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `NAEThreeSatisfiable` is isomorphism-invariant. -/
axiom naeThreeSatisfiable_iso : ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
  (A ≃[Lax904597.Sat.sat] B) → (NAEThreeSatisfiable A ↔ NAEThreeSatisfiable B)

/-- The problem NAE3SAT: does the structure satisfy `NAEThreeSatisfiable`? -/
def NAE3SAT : DecisionProblem Lax904597.Sat.sat :=
  DecisionProblem.ofPred NAEThreeSatisfiable

/-- The yes-instances of NAE3SAT are exactly the structures satisfying `NAEThreeSatisfiable`. -/
axiom nae3Sat_iff : ∀ (A : Type) [Lax904597.Sat.sat.Structure A], NAE3SAT A ↔ NAEThreeSatisfiable A

/-- NAE3SAT is NP-complete. -/
axiom nae3Sat_NP_complete : NP.Complete NAE3SAT

end Lax799700.NaeThreeSat
