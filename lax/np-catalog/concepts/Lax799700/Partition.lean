import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Syntax
import Lax799700.Knapsack
import Lax904597.Machines
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Partition
type: theorem
---
PARTITION: can a family of numbers be split into two parts of equal sum?
It lives on the vocabulary of Knapsack with the target symbol unused:
what a part must match is the weight of the items it leaves out. That is
what makes Partition a different problem rather than a special case of
Knapsack: the number to reach, half the total, is not part of the
instance, so an interpretation cannot compute it, and the classical
padding by two extra items is not first-order definable. Hardness comes
instead by an ordered first-order reduction from NAE-SAT, whose
not-all-equal condition is the two-sided constraint a balanced split
imposes. Membership is by an existential second-order definition.

-/

namespace Lax799700.Partition

open Lax799700.Knapsack Lax904597.Machines

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [binWeights.Structure A]

/-- A binary-weighted instance is a yes-instance of Partition when its order is
a linear order and some set of items weighs exactly as much as the items it
leaves out. -/
def HasEqualSplit : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧
    ∃ S : A → Prop, (∀ i, S i → BWItem i) ∧
      (∑ᶠ i ∈ {i | S i}, BWWeight i) = ∑ᶠ i ∈ {i | BWItem i ∧ ¬S i}, BWWeight i

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasEqualSplit` is isomorphism-invariant. -/
axiom hasEqualSplit_iso : ∀ {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B],
  (A ≃[Lax799700.Knapsack.binWeights] B) → (HasEqualSplit A ↔ HasEqualSplit B)

/-- The problem Partition: does the structure satisfy `HasEqualSplit`? -/
def Partition : DecisionProblem Lax799700.Knapsack.binWeights :=
  DecisionProblem.ofPred HasEqualSplit

/-- The yes-instances of Partition are exactly the structures satisfying `HasEqualSplit`. -/
axiom partition_iff : ∀ (A : Type) [Lax799700.Knapsack.binWeights.Structure A], Partition A ↔ HasEqualSplit A

/-- Partition is NP-complete. -/
axiom partition_NP_complete : NP.Complete Partition

end Lax799700.Partition
