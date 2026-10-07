import Lax366625.CountingClasses
import Lax366625.CountingProblems
import Lax366625.QuantitativeLogic
import Lax366625.WitnessCounting
import Lax799700.Common
import Lax859101.OneCallReductions
import Lax904597.Machines
import Lax904597.SecondOrder
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lax794877.PossibleWorlds
import Lax794877.WeightedWorlds
import Lax794877.Queries
import Lax794877.ExampleDatabase

/-!
---
title: The probability of h₀ is #P-hard
type: theorem
---
Counting the possible worlds of $h_0$ is one-call #P-complete, after Dalvi
and Suciu, by a parsimonious reduction from #PP2DNF: the left vertices of a
bipartite graph become uncertain $R$-facts, its edges certain $S$-facts, and
its right vertices uncertain $T$-facts, so that a world is a set of vertices
and $h_0$ holds in it when some edge has both ends chosen. The numerator of
the probability of $h_0$ with weights in the instance is one-call
#P-complete too, already when every weight is $1$, by an ordered
parsimonious reduction from the uniform case.
-/

namespace Lax794877.H0Complete

open Lax904597.SecondOrder
open FirstOrder
open Language Structure
open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder
open FirstOrder.Language
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic
open Lax859101.OneCallReductions Lax904597.Machines
open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- Counting the possible worlds of h₀ is one-call #P-complete. -/
axiom possibleWorlds_h0_sharpP_oneCallComplete :
  OneCallComplete SharpP (PossibleWorlds h0)

/-- The numerator of the probability of h₀ is one-call #P-complete. -/
axiom weightedWorlds_h0_sharpP_oneCallComplete :
  OneCallComplete SharpP (WeightedWorlds h0)

end Lax794877.H0Complete
