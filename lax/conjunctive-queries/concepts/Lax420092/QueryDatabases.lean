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

/-!
---
title: Conjunctive queries and graph databases as structures
type: definition
---
An instance of Boolean conjunctive query evaluation is a finite structure
over a vocabulary with a unary relation marking the query's variables and
two binary relations: the atoms of the query, over variables and constants,
and the facts of the database, over constants. The schema is a single
binary relation, that of graph databases; a database edge is a fact both of
whose endpoints are constants, facts touching a variable being junk the
semantics ignores.
-/

namespace Lax420092.QueryDatabases

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryDbRel : ℕ → Type where
/-- `isVar x`: the element `x` is a variable of the query. -/
  | isVar : queryDbRel 1
/-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
  | atom : queryDbRel 2
/-- `fact a b`: the database contains the fact `E(a, b)`. -/
  | fact : queryDbRel 2
  deriving DecidableEq

/-- The relational language of BCQ evaluation instances: a query and a
database over a shared universe, with a unary predicate singling out the
query variables and binary predicates for query atoms and database facts. -/
def queryDb : FirstOrder.Language :=
  ⟨fun _ => Empty, queryDbRel⟩

instance instIsRelationalQueryDb : FirstOrder.Language.IsRelational queryDb := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isVar x`: the element `x` is a variable of the query. -/
abbrev qdbIsVar : queryDb.Relations 1 :=
  .isVar

/-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
abbrev qdbAtom : queryDb.Relations 2 :=
  .atom

/-- `fact a b`: the database contains the fact `E(a, b)`. -/
abbrev qdbFact : queryDb.Relations 2 :=
  .fact

open FirstOrder

open Language Structure BoundedFormula

section EvalShorthands

variable {A : Type} [queryDb.Structure A]

/-- `x` is a variable of the query. -/
def QVar (x : A) : Prop := RelMap qdbIsVar ![x]

/-- `E(x, y)` is an atom of the query. -/
def QAtom (x y : A) : Prop := RelMap qdbAtom ![x, y]

/-- `E(a, b)` is a fact of the database (raw: no constraint on `a`, `b`). -/
def DbFact (x y : A) : Prop := RelMap qdbFact ![x, y]

/-- A genuine database edge: a fact both of whose endpoints are database
elements (i.e., not query variables). Facts violating this are representation
junk and are ignored by the semantics. -/
def DbEdge (x y : A) : Prop := DbFact x y ∧ ¬QVar x ∧ ¬QVar y

end EvalShorthands

end Lax420092.QueryDatabases
