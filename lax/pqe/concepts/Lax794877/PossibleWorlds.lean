import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Lax904597.SecondOrder
import Lax366625.CountingProblems

/-!
---
title: Possible worlds
type: definition
---
An instance over a schema $L$ is a structure over two copies of $L$: the
certain facts and the uncertain ones. A possible world keeps every certain
fact and some of the uncertain ones, and is read as an $L$-structure. For a
sentence $\varphi$ of the schema, counting possible worlds is the counting
problem whose value on an instance is the number of its possible worlds in
which $\varphi$ holds; with every uncertain fact present with probability
$1/2$, this number divided by the number of worlds is the probability of
$\varphi$.
-/

namespace Lax794877.PossibleWorlds

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- The block guessing a world: one relation variable per relation symbol of
the schema, of the same arity. -/
def worldBlock [Finite (Σ n, L.Relations n)] : SOBlock where
  ι := Σ n, L.Relations n
  arity := fun p => p.1

section Worlds

variable {L} [Finite (Σ n, L.Relations n)] {A : Type}

/-- The structure over the schema that a family of relations is. -/
@[reducible]
def worldStructure [L.IsRelational] (ρ : (worldBlock L).Assignment A) : L.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {n} R x => ρ ⟨n, R⟩ x

/-- The family of relations `ρ` is a **possible world** of the instance: it
contains every certain fact, and only certain or uncertain facts. -/
def IsWorld [(L.sum L).Structure A] (ρ : (worldBlock L).Assignment A) : Prop :=
  ∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A),
    (RelMap (L := L.sum L) (M := A) (Sum.inl p.2) x → ρ p x) ∧
      (ρ p x → RelMap (L := L.sum L) (M := A) (Sum.inl p.2) x ∨
        RelMap (L := L.sum L) (M := A) (Sum.inr p.2) x)

/-- A fact that is uncertain and not certain: the facts a world is free to
keep or to drop. -/
def IsOpenFact [(L.sum L).Structure A] (q : Σ p : Σ n, L.Relations n, Fin p.1 → A) : Prop :=
  RelMap (L := L.sum L) (M := A) (Sum.inr q.1.2) q.2 ∧
    ¬RelMap (L := L.sum L) (M := A) (Sum.inl q.1.2) q.2

end Worlds

open Lax366625.CountingProblems

/-- **Counting possible worlds**: the number of possible worlds of the instance
in which the sentence `φ` of the schema holds. -/
noncomputable def PossibleWorlds {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence) : CountingProblem (L.sum L) :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ρ : (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A
        (worldStructure ρ) φ}

end Lax794877.PossibleWorlds
