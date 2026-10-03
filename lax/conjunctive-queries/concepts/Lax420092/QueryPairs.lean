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
import Lax904597.Classes
import Lax799700.Problems
import Lax420092.Evaluation

/-!
---
title: Pairs of conjunctive queries and containment
type: definition
---
An instance of containment is a pair of Boolean conjunctive queries over a
shared universe: unary relations mark the variables of the left and of the
right query, binary relations record their atoms, and the other elements
are shared constants. The left query is contained in the right one when
every database, over any universe and any denotation of the constants, that
satisfies the left query satisfies the right one. CQContainment is the
decision problem of the structures isomorphic to a pair whose left query is
contained in the right one.
-/

namespace Lax420092.QueryPairs

open Lax420092.Evaluation

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryPairRel : ℕ → Type where
/-- `leftVar x`: the element `x` is a variable of the left query. -/
  | leftVar : queryPairRel 1
/-- `rightVar x`: the element `x` is a variable of the right query. -/
  | rightVar : queryPairRel 1
/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
  | leftAtom : queryPairRel 2
/-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
  | rightAtom : queryPairRel 2
  deriving DecidableEq

/-- The relational language of pairs of conjunctive queries over a shared
universe of variables and constants. -/
def queryPair : FirstOrder.Language :=
  ⟨fun _ => Empty, queryPairRel⟩

instance instIsRelationalQueryPair : FirstOrder.Language.IsRelational queryPair := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `leftVar x`: the element `x` is a variable of the left query. -/
abbrev qpLeftVar : queryPair.Relations 1 :=
  .leftVar

/-- `rightVar x`: the element `x` is a variable of the right query. -/
abbrev qpRightVar : queryPair.Relations 1 :=
  .rightVar

/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
abbrev qpLeftAtom : queryPair.Relations 2 :=
  .leftAtom

/-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
abbrev qpRightAtom : queryPair.Relations 2 :=
  .rightAtom

open FirstOrder

open Language Structure BoundedFormula

section PairShorthands

variable {A : Type} [queryPair.Structure A]

/-- `x` is a variable of the left query. -/
def LVar (x : A) : Prop := RelMap qpLeftVar ![x]

/-- `x` is a variable of the right query. -/
def RVar (x : A) : Prop := RelMap qpRightVar ![x]

/-- `E(x, y)` is an atom of the left query. -/
def LAtom (x y : A) : Prop := RelMap qpLeftAtom ![x, y]

/-- `E(x, y)` is an atom of the right query. -/
def RAtom (x y : A) : Prop := RelMap qpRightAtom ![x, y]

/-- `x` is a variable of either query; the non-`PairVar` elements are the
shared constants, whose denotation every database fixes. -/
def PairVar (x : A) : Prop := LVar x ∨ RVar x

end PairShorthands

/-- The left query is contained in the right one: every database (over any
universe, with any interpretation of the constants) satisfying the left query
satisfies the right query. -/
def QueryContained (A : Type) [queryPair.Structure A] : Prop :=
  ∀ (U : Type) (F : U → U → Prop) (ι : A → U),
    SatisfiedIn (PairVar (A := A)) (LAtom (A := A)) F ι →
      SatisfiedIn (PairVar (A := A)) (RAtom (A := A)) F ι

open Lax904597.Problems Lax799700.Problems

/-- BCQ containment: is the left query contained in the right one? -/
def CQContainment : DecisionProblem queryPair :=
  DecisionProblem.ofPred QueryContained

end Lax420092.QueryPairs
