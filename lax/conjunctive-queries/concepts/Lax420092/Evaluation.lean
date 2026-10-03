import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.SetTheory.Cardinal.Finite
import Lax420092.QueryDatabases
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Boolean conjunctive query evaluation
type: definition
---
A conjunctive query with given variables and atoms over the elements of an
instance is satisfied in a database, a binary relation on some universe
with a denotation of the instance's elements, when some valuation of the
elements into the universe agrees with the denotation on the non-variables
and sends every atom to an edge of the database. The homomorphism form
takes the instance's own universe as database, every non-variable denoting
itself. The query of an evaluation instance holds in its database when the
homomorphism condition is met with the database edges as facts, the
classical semantics of Boolean conjunctive queries under set semantics.
CQEval is the decision problem of the structures isomorphic to an instance
whose query holds.
-/

namespace Lax420092.Evaluation

open Lax420092.QueryDatabases

open FirstOrder

open Language Structure BoundedFormula

section GenericCore

variable {A B : Type}

/-- The conjunctive query with variables `VarP` and atoms `AtomP` (over
instance elements `A`) is satisfied in the database `F` on universe `U`,
where `ι` fixes the denotation of the non-variables: some valuation extends
`ι` and maps every atom to a database edge. -/
def SatisfiedIn (VarP : A → Prop) (AtomP : A → A → Prop) {U : Type}
    (F : U → U → Prop) (ι : A → U) : Prop :=
  ∃ v : A → U, (∀ x, ¬VarP x → v x = ι x) ∧ ∀ x y, AtomP x y → F (v x) (v y)

/-- The homomorphism condition: satisfaction in a database carried by the
instance's own universe, with every non-variable denoting itself. This single
notion underlies both problems below. -/
def CQHom (VarP : A → Prop) (AtomP FactP : A → A → Prop) : Prop :=
  SatisfiedIn VarP AtomP FactP id

end GenericCore

/-- The query of an evaluation instance holds in its database: there is a
valuation of the elements, fixing the non-variables, that maps every query
atom to a genuine database edge. This is the classical semantics of Boolean
conjunctive queries, phrased as a homomorphism into the database half of the
instance. -/
def QueryHolds (A : Type) [queryDb.Structure A] : Prop :=
  CQHom (QVar (A := A)) (QAtom (A := A)) (DbEdge (A := A))

open Lax904597.Problems Lax799700.Problems

/-- BCQ evaluation: does the query of the instance hold in its database? -/
def CQEval : DecisionProblem queryDb :=
  DecisionProblem.ofPred QueryHolds

end Lax420092.Evaluation
