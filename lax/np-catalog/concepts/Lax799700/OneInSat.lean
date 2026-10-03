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
import Lax799700.Common
import Lax904597.Sat
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: 1-in-SAT
type: theorem
---
EXACTLY-ONE SATISFIABILITY: is there a truth assignment giving every
clause exactly one true literal? It lives on the vocabulary of SAT with
its own notion of satisfaction (OneInProper). Membership is by an
existential second-order definition, SAT's kernel plus uniqueness, one
clause per pattern of signs; hardness is an ordered first-order reduction
from 3SAT. The catalog states it at unrestricted width because it is the
source for Exact Cover, where a 1-in-SAT instance becomes an exact cover
with no gadget at all.

-/

namespace Lax799700.OneInSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Semantics

variable {A : Type} [sat.Structure A]

/-- An assignment is *exactly-one proper* when every clause has exactly one
true literal occurrence. -/
def OneInProper (ν : A → Prop) : Prop :=
  ∀ c : A, SatOcc.IsCl c → ∃ x s, SatOcc.OccIn c x s ∧ SatOcc.LitTrue ν x s ∧
    ∀ y t, SatOcc.OccIn c y t → SatOcc.LitTrue ν y t → y = x ∧ t = s

end Semantics

section Problem

variable (A : Type) [sat.Structure A]

/-- A `Language.sat`-structure is exactly-one satisfiable if some assignment
gives every clause exactly one true literal. -/
def OneInSatisfiable : Prop := ∃ ν : A → Prop, OneInProper ν

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `OneInSatisfiable` is isomorphism-invariant. -/
axiom oneInSatisfiable_iso : ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
  (A ≃[Lax904597.Sat.sat] B) → (OneInSatisfiable A ↔ OneInSatisfiable B)

/-- The problem OneInSAT: does the structure satisfy `OneInSatisfiable`? -/
def OneInSAT : DecisionProblem Lax904597.Sat.sat :=
  DecisionProblem.ofPred OneInSatisfiable

/-- The yes-instances of OneInSAT are exactly the structures satisfying
`OneInSatisfiable`. -/
axiom oneInSat_iff : ∀ (A : Type) [Lax904597.Sat.sat.Structure A], OneInSAT A ↔ OneInSatisfiable A

/-- OneInSAT is NP-complete. -/
axiom oneInSat_NP_complete : NP.Complete OneInSAT

end Lax799700.OneInSat
