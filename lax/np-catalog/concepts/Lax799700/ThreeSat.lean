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
title: 3SAT
type: theorem
---
3SAT on the vocabulary of SAT: a CNF structure is a yes-instance when
every clause has at most three literal occurrences (WidthAtMostThree) and
the CNF is satisfiable (ThreeSatisfiable). The width bound is part of the
yes-instances rather than of the vocabulary, which is what makes 3SAT a
decision problem on arbitrary CNF structures; it is expressed without
counting, as “among any four literal occurrences of a clause, two
coincide”.

Membership in NP is by the identity-like first-order reduction to SAT;
hardness is the classical clause splitting, an ordered first-order
reduction from SAT in which the chain of fresh variables of a clause
follows the order on its occurrences.

-/

namespace Lax799700.ThreeSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section ThreeSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most three literal
occurrences: among any four occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostThree : Prop :=
  ∀ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

/-- A `Language.sat`-structure is a yes-instance of 3SAT if every clause has
at most three literal occurrences and the CNF is satisfiable. -/
def ThreeSatisfiable : Prop :=
  WidthAtMostThree A ∧ Satisfiable A

end ThreeSat

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `ThreeSatisfiable` is isomorphism-invariant. -/
axiom threeSatisfiable_iso : ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
  (A ≃[Lax904597.Sat.sat] B) → (ThreeSatisfiable A ↔ ThreeSatisfiable B)

/-- The problem ThreeSAT: does the structure satisfy `ThreeSatisfiable`? -/
def ThreeSAT : DecisionProblem Lax904597.Sat.sat :=
  DecisionProblem.ofPred ThreeSatisfiable

/-- The yes-instances of ThreeSAT are exactly the structures satisfying
`ThreeSatisfiable`. -/
axiom threeSat_iff : ∀ (A : Type) [Lax904597.Sat.sat.Structure A], ThreeSAT A ↔ ThreeSatisfiable A

/-- ThreeSAT is NP-complete. -/
axiom threeSat_NP_complete : NP.Complete ThreeSAT

end Lax799700.ThreeSat
