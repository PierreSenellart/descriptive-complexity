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
import Lax799700.Common
import Lax904597.Machines
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Knapsack, in binary
type: theorem
---
KNAPSACK, in the subset-sum form of Karp: given weights and a target, is
there a set of items whose weights sum to the target? Numbers are
written in binary, as the last four problems of Karp's list require:
under the unary encoding they are solvable in polynomial time by dynamic
programming, so the representation is part of the statement. The
vocabulary carries the items, the bit positions, the bits of each
weight, the bits of the target, and a linear order fixing the place
values; being a linear order is folded into the yes-instances. The
decoding (binNum) sums $2^{\mathrm{rank}}$ over a set of positions, and
is defined for an arbitrary relation so that invariance is a plain
transport. Membership is by an existential second-order definition that
walks the order on items to verify the arithmetic; hardness is an
ordered first-order reduction from Exact Cover.

-/

namespace Lax799700.Knapsack

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive binWeightsRel : ℕ → Type where
/-- `item i`: `i` is an item. -/
  | item : binWeightsRel 1
/-- `posn p`: `p` is a bit position. -/
  | posn : binWeightsRel 1
/-- `bit i p`: the weight of `i` has bit 1 at position `p`. -/
  | bit : binWeightsRel 2
/-- `tgt p`: the target has bit 1 at position `p`. -/
  | tgt : binWeightsRel 1
/-- `le a b`: the linear order carrying the place values. -/
  | le : binWeightsRel 2
  deriving DecidableEq

/-- The relational language of binary-weighted instances: items and bit
positions, the bits of each item's weight and of the target, and a linear
order. -/
def binWeights : FirstOrder.Language :=
  ⟨fun _ => Empty, binWeightsRel⟩

instance instIsRelationalBinWeights : FirstOrder.Language.IsRelational binWeights := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `item i`: `i` is an item. -/
abbrev bwItem : binWeights.Relations 1 :=
  .item

/-- `posn p`: `p` is a bit position. -/
abbrev bwPosn : binWeights.Relations 1 :=
  .posn

/-- `bit i p`: the weight of `i` has bit 1 at position `p`. -/
abbrev bwBit : binWeights.Relations 2 :=
  .bit

/-- `tgt p`: the target has bit 1 at position `p`. -/
abbrev bwTgt : binWeights.Relations 1 :=
  .tgt

/-- `le a b`: the linear order carrying the place values. -/
abbrev bwLe : binWeights.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [binWeights.Structure A]

/-- `item i`: `i` is an item.  -/
def BWItem {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwItem ![a0]

/-- `posn p`: `p` is a bit position.  -/
def BWPosn {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwPosn ![a0]

/-- `bit i p`: the weight of `i` has bit 1 at position `p`.  -/
def BWBit {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwBit ![a0, a1]

/-- `tgt p`: the target has bit 1 at position `p`.  -/
def BWTgt {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwTgt ![a0]

/-- `le a b`: the linear order carrying the place values.  -/
def BWLe {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwLe ![a0, a1]

/-- The weight of an item, decoded. -/
noncomputable def BWWeight (i : A) : ℕ := binNum BWLe BWPosn (BWBit i)

end Shorthands

/-- The target of a binary-weighted instance, decoded. -/
noncomputable def BWTarget (A : Type) [binWeights.Structure A] : ℕ :=
  binNum (BWLe (A := A)) BWPosn BWTgt

section Problem

variable (A : Type) [binWeights.Structure A]

/-- A binary-weighted instance is a yes-instance of Knapsack when its order is
a linear order and some set of items has weights summing exactly to the
target. (Karp's KNAPSACK is this subset-sum question.) -/
def HasSubsetSum : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧
    ∃ S : A → Prop, (∀ i, S i → BWItem i) ∧
      (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSubsetSum` is isomorphism-invariant. -/
axiom hasSubsetSum_iso : ∀ {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B],
  (A ≃[Lax799700.Knapsack.binWeights] B) → (HasSubsetSum A ↔ HasSubsetSum B)

/-- The problem Knapsack: does the structure satisfy `HasSubsetSum`? -/
def Knapsack : DecisionProblem Lax799700.Knapsack.binWeights :=
  DecisionProblem.ofPred HasSubsetSum

/-- The yes-instances of Knapsack are exactly the structures satisfying
`HasSubsetSum`. -/
axiom knapsack_iff : ∀ (A : Type) [Lax799700.Knapsack.binWeights.Structure A], Knapsack A ↔ HasSubsetSum A

/-- Knapsack is NP-complete. -/
axiom knapsack_NP_complete : NP.Complete Knapsack

end Lax799700.Knapsack
