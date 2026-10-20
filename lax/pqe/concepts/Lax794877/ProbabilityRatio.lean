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
title: The probability of a query is a ratio of two #P numbers
type: theorem
---
On a weighted instance whose positions are linearly ordered, with every
uncertain fact of positive total weight, the probability of a sentence
$\varphi$ is the number of weighted worlds of $\varphi$ divided by that of
the sentence that always holds: a ratio of two numbers of #P, for every
first-order query. On an instance whose positions are not linearly ordered,
the count is $0$.
-/

namespace Lax794877.ProbabilityRatio

open Lax904597.SecondOrder
open FirstOrder
open Language Structure
open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder
open FirstOrder.Language
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic
open Lax859101.OneCallReductions Lax904597.Machines
open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- The probability of a query is the ratio of two weighted world counts. -/
axiom worldProb_eq_ratio :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
      {A : Type} [(weightedLang L).Structure A] [Finite A],
    IsLinOrd (WLe L A) → ∀ (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x),
    worldProb φ hpos = (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ)

/-- On an instance whose positions are not linearly ordered, the count is `0`. -/
axiom weightedWorlds_of_not_isLinOrd :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      (A : Type) [(weightedLang L).Structure A],
    ¬IsLinOrd (WLe L A) → WeightedWorlds φ A = 0

end Lax794877.ProbabilityRatio
