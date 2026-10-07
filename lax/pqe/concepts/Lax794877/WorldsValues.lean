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
title: The values of the world counts
type: lemma
---
The number of possible worlds of an instance in which a sentence holds, and
the number of weighted witnesses of the worlds in which it holds, are
invariant under isomorphism of instances, so they are the values of the two
counting problems.
-/

namespace Lax794877.WorldsValues

open Lax904597.SecondOrder
open FirstOrder
open Language Structure
open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder
open FirstOrder.Language
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic
open Lax859101.OneCallReductions Lax904597.Machines
open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- The number of possible worlds satisfying a sentence is isomorphism-invariant. -/
axiom possibleWorlds_count_iso :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      {A B : Type}
    [(L.sum L).Structure A] [(L.sum L).Structure B], (A ≃[L.sum L] B) →
    Nat.card {ρ : (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A
        (worldStructure ρ) φ} =
    Nat.card {ρ : (worldBlock L).Assignment B // IsWorld ρ ∧ @Sentence.Realize L B
        (worldStructure ρ) φ}

/-- The value of counting possible worlds is the number it counts. -/
axiom possibleWorlds_eq :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      (A : Type) [(L.sum L).Structure A],
    PossibleWorlds φ A = Nat.card {ρ :
        (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ}

/-- The number of weighted witnesses is isomorphism-invariant. -/
axiom weightedWorlds_count_iso :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      {A B : Type}
    [(weightedLang L).Structure A] [(weightedLang L).Structure B], (A ≃[weightedLang L] B) →
    Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ} =
    Nat.card {σ : (weightBlock L).Assignment B // IsLinOrd (WLe L B) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → B), WeightCond σ p x) ∧
      @Sentence.Realize L B (worldStructure (worldOf σ)) φ}

/-- The value of counting weighted possible worlds is the number it counts. -/
axiom weightedWorlds_eq :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      (A : Type) [(weightedLang L).Structure A],
    WeightedWorlds φ A = Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ}

end Lax794877.WorldsValues
