/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity

/-!
# First-order interpretations and FO reductions

Complexity theory is essentially absent from Mathlib because formalizing a
machine model of computation (and resource bounds on it) is hard. However, many
classical NP-hardness reductions do not need the full power of polynomial-time
computation: the reduction is *first-order expressible* — the output structure
can be described by fixed first-order formulas evaluated in the input
structure. Such FO reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so
exhibiting an FO reduction is (much) stronger than exhibiting a Karp
reduction, while being completely machine-model-free and therefore easy to
formalize on top of Mathlib's `ModelTheory` library.

This file defines:

* `FirstOrder.DecisionProblem L`: a "problem" over the vocabulary `L`, i.e. a
  property of `L`-structures;
* `FirstOrder.FOInterpretation L L' Tag dim`: a tagged, `dim`-dimensional
  first-order interpretation of a relational language `L'` in a language `L`,
  mapping every `L`-structure `A` to an `L'`-structure `I.Map A` with universe
  `Tag × (Fin dim → A)`;
* `FirstOrder.FOInterpretation.IsQuantifierFree`: interpretations all of whose
  defining formulas are quantifier-free (an even weaker reduction notion);
* `FirstOrder.FOReduction P Q`: an FO reduction from problem `P` to problem
  `Q`, i.e. an interpretation mapping yes-instances of `P` exactly to
  yes-instances of `Q`.

## Design notes

The textbook notion of FO reduction maps a structure `A` to a structure with
universe a definable subset of `A^k`, using a linear order on `A` to encode
constantly many "sorts" of elements. To stay order-free and subset-free we
instead tag tuples with elements of a finite type `Tag`, and use the full
universe `Tag × A^dim`: junk elements are harmless in practice because the
defining formulas can exclude them from all relations. Every tagged
interpretation can be converted into a textbook `k`-ary FO reduction on
ordered structures (using the order to encode constantly many tags), so the
notion formalized here is a genuine form of FO reducibility.

The universe of `I.Map A` is `Tag × (Fin dim → A)`, which is finite whenever
`A` and `Tag` are (`FOInterpretation.map_finite`): FO reductions map finite
structures to finite structures, as required for reductions between decision
problems on finite structures.
-/

namespace FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

/-- A property of `L`-structures: a "problem" in the sense of descriptive
complexity, whose yes-instances are the `L`-structures satisfying it. -/
def DecisionProblem : Type 1 :=
  ∀ (A : Type) [L.Structure A], Prop

/-- A *tagged `dim`-dimensional first-order interpretation* of the relational
language `L'` in the language `L`. It maps an `L`-structure `A` to the
`L'`-structure with universe `Tag × A^dim` in which an `n`-ary relation symbol
`R` holds of tagged tuples `(t₁, ā₁), …, (tₙ, āₙ)` iff the first-order
`L`-formula `relFormula R (t₁, …, tₙ)` — whose free variable `(i, j)` stands
for the `j`-th coordinate `āᵢ j` of the `i`-th argument — holds in `A`. -/
structure FOInterpretation (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L'} {Tag : Type} {dim : ℕ}

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples.

This is a plain `def` (not an `abbrev`) so that the `L'.Structure` instance on
it can be found by instance search, while `rcases`-style destructuring still
sees through it. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

theorem relMap_map [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.Map A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2 :=
  Iff.rfl

omit [L.Structure A] in
/-- FO interpretations map finite structures to finite structures. -/
theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  inferInstanceAs (Finite (Tag × (Fin dim → A)))

/-- An interpretation is quantifier-free if all its defining formulas are.
Quantifier-free reductions are the weakest reduction notion in common use in
descriptive complexity; SAT remains NP-complete under them. -/
def IsQuantifierFree : Prop :=
  ∀ {n : ℕ} (R : L'.Relations n) (t : Fin n → Tag), (I.relFormula R t).IsQF

end FOInterpretation

variable {L L'}

/-- A first-order reduction from the problem `P` (on `L`-structures) to the
problem `Q` (on `L'`-structures): a first-order interpretation mapping
yes-instances of `P` exactly to yes-instances of `Q`.

Since FO interpretations are computable in AC⁰ ⊆ PTIME on (encodings of)
finite structures, an `FOReduction P Q` is in particular a Karp reduction from
`P` to `Q`: any NP-hardness argument for `P` transfers to `Q`, without any
formalized machine model. -/
structure FOReduction [L'.IsRelational] (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation. -/
  toInterpretation : FOInterpretation L L' Tag dim
  /-- Yes-instances map exactly to yes-instances. -/
  correct : ∀ (A : Type) [L.Structure A], P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ " Q:51 => FOReduction P Q

end FirstOrder
