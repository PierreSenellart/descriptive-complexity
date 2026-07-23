/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel
import DescriptiveComplexity.Interpretation
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Binary-weighted instances, and Karp's Knapsack

This file opens **representation (C)** of the design notes, the one the last
four problems of Karp's list need: numbers that must be *exponential* in the
size of the instance, hence written in binary. Under the unary representation
of `DescriptiveComplexity.Numbers.Unary` these problems are solvable in polynomial
time by dynamic programming, so they are simply not NP-hard there – the
representation is not a detail of the encoding but part of the statement.

## The vocabulary

`FirstOrder.Language.binWeights` carries

* `item` and `posn`, the items and the bit positions;
* `bit i p`, “the weight of the item `i` has bit 1 at the position `p`”;
* `tgt p`, the bits of the target;
* `le`, a linear order – on the positions it fixes the place values, and on
  the items it is what the `Σ₁` definition walks along when it verifies the
  arithmetic.

Being a linear order is not automatic for a relation symbol, so it is folded
into the yes-instances (`DescriptiveComplexity.IsLinOrd`), exactly as 3SAT folds its
width bound in.

## The decoding

`DescriptiveComplexity.bitRank` is the rank of a position – how many positions lie
strictly below it – and `DescriptiveComplexity.binNum` decodes a set of positions as
`∑ 2 ^ rank`. Both are defined for an *arbitrary* relation `Le`, with no
well-formedness assumption, which keeps them total and makes
isomorphism-invariance a plain transport statement; when `Le` is a linear
order they agree with `DescriptiveComplexity.binValue` of the numbers layer.

The sum ranges over a set rather than a `Finset`, via `finsum`, so that no
finiteness assumption is needed to *state* the value; on an infinite universe
it is `0`, which no yes-instance ever looks at since finiteness is part of the
problem.
-/

/- The language of binary-weighted instances lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` and
`Language.order`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of binary-weighted instances. -/
inductive binWeightsRel : ℕ → Type
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
protected def binWeights : Language :=
  ⟨fun _ => Empty, binWeightsRel⟩
  deriving IsRelational

/-- The item symbol. -/
abbrev bwItem : Language.binWeights.Relations 1 := .item

/-- The position symbol. -/
abbrev bwPosn : Language.binWeights.Relations 1 := .posn

/-- The bit symbol. -/
abbrev bwBit : Language.binWeights.Relations 2 := .bit

/-- The target symbol. -/
abbrev bwTgt : Language.binWeights.Relations 1 := .tgt

/-- The order symbol. -/
abbrev bwLe : Language.binWeights.Relations 2 := .le

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.binWeights.Structure A]

/-- Being an item. -/
def BWItem (a : A) : Prop := RelMap bwItem ![a]

/-- Being a bit position. -/
def BWPosn (a : A) : Prop := RelMap bwPosn ![a]

/-- The bit of an item's weight at a position. -/
def BWBit (i p : A) : Prop := RelMap bwBit ![i, p]

/-- The bits of the target. -/
def BWTgt (p : A) : Prop := RelMap bwTgt ![p]

/-- The order carrying the place values. -/
def BWLe (a b : A) : Prop := RelMap bwLe ![a, b]

/-- The weight of an item, decoded. -/
noncomputable def BWWeight (i : A) : ℕ := binNum BWLe BWPosn (BWBit i)

end Shorthands

/-- The target of a binary-weighted instance, decoded. -/
noncomputable def BWTarget (A : Type) [Language.binWeights.Structure A] : ℕ :=
  binNum (BWLe (A := A)) BWPosn BWTgt

/-! ### The problem -/

section Problem

variable (A : Type) [Language.binWeights.Structure A]

/-- A binary-weighted instance is a yes-instance of Knapsack when its order is
a linear order and some set of items has weights summing exactly to the
target. (Karp's KNAPSACK is this subset-sum question.) -/
def HasSubsetSum : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧
    ∃ S : A → Prop, (∀ i, S i → BWItem i) ∧
      (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

end Problem

section Iso

variable {A B : Type} [Language.binWeights.Structure A] [Language.binWeights.Structure B]

private theorem hasSubsetSum_of_iso (e : A ≃[Language.binWeights] B)
    (h : HasSubsetSum A) : HasSubsetSum B := by
  obtain ⟨hfin, hlin, S, hSi, hsum⟩ := h
  have hle : ∀ a a' : A, BWLe a a' ↔ BWLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e bwLe a a'
  have hposn : ∀ a : A, BWPosn a ↔ BWPosn (e a) := fun a => relMap_equiv₁ e bwPosn a
  have hitem : ∀ a : A, BWItem a ↔ BWItem (e a) := fun a => relMap_equiv₁ e bwItem a
  have htgt : ∀ a : A, BWTgt a ↔ BWTgt (e a) := fun a => relMap_equiv₁ e bwTgt a
  have hbit : ∀ a a' : A, BWBit a a' ↔ BWBit (e a) (e a') := fun a a' =>
    relMap_equiv₂ e bwBit a a'
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => S (e.toEquiv.symm b), fun b hb => ?_, ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hitem _).mp (hSi _ hb)
  · have hw : ∀ a : A, BWWeight a = BWWeight (e a) := fun a =>
      binNum_equiv e.toEquiv hle hposn (hbit a)
    have htarget : BWTarget A = BWTarget B := binNum_equiv e.toEquiv hle hposn htgt
    rw [← htarget, ← hsum]
    refine (finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a).symm
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha

/-- Being a yes-instance of Knapsack is isomorphism-invariant. -/
theorem hasSubsetSum_iso (e : A ≃[Language.binWeights] B) :
    HasSubsetSum A ↔ HasSubsetSum B :=
  ⟨hasSubsetSum_of_iso e, hasSubsetSum_of_iso e.symm⟩

end Iso

/-- KNAPSACK, as a problem on binary-weighted instances: is there a set of
items whose weights sum exactly to the target? The weights are written in
*binary*, which is what makes the problem NP-hard rather than
polynomial-time. -/
def Knapsack : DecisionProblem Language.binWeights where
  Holds := fun A inst => @HasSubsetSum A inst
  iso_invariant := fun e => hasSubsetSum_iso e

end DescriptiveComplexity
