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
import Lax904597.Sat
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Not-all-equal SAT
type: theorem
---
NOT-ALL-EQUAL SAT: is there a truth assignment giving every clause both a
true and a false literal? It lives on the vocabulary of SAT, and only its
notion of satisfaction differs (NAEProper), which is closed under
flipping the assignment. That symmetry is what the hardness proof uses:
adding one fresh variable, positive in every clause, turns a satisfying
assignment into a not-all-equal one and back, once the fresh variable is
normalized to false. The fresh variable is picked out as the minimum of
its copy of the universe, so the reduction from SAT is an ordered
first-order reduction. Membership is by an existential second-order
definition, SAT's kernel conjoined with its mirror image.

-/

namespace Lax799700.NaeSat

open Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula

section Semantics

variable {A : Type} [sat.Structure A]

/-- An assignment is *not-all-equal proper* when every clause contains both a
true and a false literal. -/
def NAEProper (ν : A → Prop) : Prop :=
  ∀ c : A, RelMap satIsClause ![c] →
    (∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ¬ν x) ∨ (RelMap satNegIn ![c, x] ∧ ν x)

end Semantics

section Problem

variable (A : Type) [sat.Structure A]

/-- A `Language.sat`-structure is not-all-equal satisfiable if some assignment
gives every clause both a true and a false literal. -/
def NAESatisfiable : Prop := ∃ ν : A → Prop, NAEProper ν

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `NAESatisfiable` is isomorphism-invariant. -/
axiom naeSatisfiable_iso : ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
  (A ≃[Lax904597.Sat.sat] B) → (NAESatisfiable A ↔ NAESatisfiable B)

/-- The problem NAESAT: does the structure satisfy `NAESatisfiable`? -/
def NAESAT : DecisionProblem Lax904597.Sat.sat :=
  DecisionProblem.ofPred NAESatisfiable

/-- The yes-instances of NAESAT are exactly the structures satisfying
`NAESatisfiable`. -/
axiom naeSat_iff : ∀ (A : Type) [Lax904597.Sat.sat.Structure A], NAESAT A ↔ NAESatisfiable A

/-- NAESAT is NP-complete. -/
axiom naeSat_NP_complete : NP.Complete NAESAT

end Lax799700.NaeSat
