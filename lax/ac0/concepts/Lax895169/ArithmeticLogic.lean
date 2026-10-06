import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax895169.BitPredicate

/-!
---
title: AC⁰ as first-order logic with arithmetic
type: definition
---
The arithmetic vocabulary has a binary symbol $\le$ and two ternary symbols
for addition and multiplication. Every finite linear order interprets it
canonically through the ranks of its elements: $\le$ is the order,
$\mathrm{plus}(x, y, z)$ holds when the ranks satisfy
$r(x) + r(y) = r(z)$ and $\mathrm{times}(x, y, z)$ when
$r(x) \cdot r(y) = r(z)$. The two are graphs, hence truncated: a sum or a
product that is not the rank of an element is related to nothing.

A decision problem $P$ over a relational vocabulary $L$ is AC⁰ definable
when there is a first-order sentence $\varphi$ over $L$ and the arithmetic
vocabulary such that, for every nonempty finite $L$-structure $A$ and every
linear order on $A$, $A$ is a yes-instance of $P$ if and only if
$\varphi$ holds in $A$ with the canonical arithmetic of that order. This is
the logic FO($\le, +, \times$), which defines the problems of uniform AC⁰
by theorems of Barrington, Immerman and Straubing; no circuit model is
introduced here.
-/

namespace Lax895169.ArithmeticLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the arithmetic vocabulary. -/
inductive arithRel : ℕ → Type
  /-- `le x y`: the rank of `x` is at most the rank of `y`, i.e., `x ≤ y`. -/
  | le : arithRel 2
  /-- `plus x y z`: the ranks satisfy `orank x + orank y = orank z`. -/
  | plus : arithRel 3
  /-- `times x y z`: the ranks satisfy `orank x * orank y = orank z`. -/
  | times : arithRel 3
  deriving DecidableEq

/-- The relational vocabulary of the numeric predicates: a linear order and the
graphs of addition and multiplication of ranks. Interpreted canonically on every
finite linear order by `arithStructure`. -/
def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩

instance instIsRelationalArith : IsRelational arith := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)

end Structures

open FirstOrder

open Language

/-- A decision problem is **AC⁰ definable** if a single sentence over the
arithmetic expansion of its vocabulary decides it on nonempty finite ordered
structures. The equivalence is required for *every* linear order, so the notion
is order-invariant: the sentence sees `≤`, `+` and `×`, the problem does not.
There is no order-free variant: the numeric predicates are computed from the
order, so without one there is nothing for them to mean. -/
def AC0Definable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : (L.sum arith).Sentence,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

end Lax895169.ArithmeticLogic
