import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order
import Lax904597.Problems

/-!
---
title: First-order interpretations and first-order reductions
type: definition
---
A *tagged $d$-dimensional first-order interpretation* of a relational
vocabulary $L'$ in a vocabulary $L$ maps an $L$-structure with universe $A$
to the $L'$-structure with universe $\mathrm{Tag} \times A^d$, in which an
$n$-ary symbol $R$ holds of the tagged tuples $(t_1, \bar a_1), \dots,
(t_n, \bar a_n)$ exactly when the first-order $L$-formula chosen for $R$ and
the tags $t_1, \dots, t_n$ holds in $A$ of the coordinates $\bar a_1, \dots,
\bar a_n$. The tags play the role of the constantly many sorts that textbook
reductions carve out of an ordered universe.

A *first-order reduction* from a problem $P$ to a problem $Q$ is such an
interpretation mapping yes-instances of $P$ exactly to yes-instances of $Q$,
on every finite nonempty structure. An *ordered* first-order reduction is
one over the expansion of $L$ by a linear order, correct for every linear
order put on the input; since $P$ does not depend on the order, this is an
order-invariant reduction. Both are computable in $\mathrm{AC}^0$ on
encodings of finite structures, hence in particular polynomial-time
many-one reductions.
-/

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

/-- A first-order reduction from the problem `P` on `L`-structures to the
problem `Q` on `L'`-structures: an interpretation mapping yes-instances of
`P` exactly to yes-instances of `Q`, on the finite nonempty structures. -/
structure FOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags: the copies of `A^dim` the interpretation uses. -/
  Tag : Type
  /-- Finitely many tags, so that finite structures map to finite ones. -/
  [tagFinite : Finite Tag]
  /-- At least one tag, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the interpretation. -/
  dim : ℕ
  /-- The interpretation. -/
  toInterpretation : FOInterpretation L L' Tag dim
  /-- Yes-instances map exactly to yes-instances. -/
  correct : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

end Ordered

/-- An ordered first-order reduction from `P` to `Q`: an interpretation over
the ordered expansion of `L` that maps yes-instances of `P` exactly to
yes-instances of `Q`, on every finite nonempty structure and for every linear
order on it. -/
structure OrderedFOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags: the copies of `A^dim` the interpretation uses. -/
  Tag : Type
  /-- Finitely many tags, so that finite structures map to finite ones. -/
  [tagFinite : Finite Tag]
  /-- At least one tag, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the interpretation. -/
  dim : ℕ
  /-- The interpretation, over the ordered expansion of `L`. -/
  toInterpretation : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

end Lax904597.Interpretations
