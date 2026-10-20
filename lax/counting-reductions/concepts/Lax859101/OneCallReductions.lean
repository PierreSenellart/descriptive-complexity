import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Lax366625.CountingProblems
import Lax904597.Relativized
import Lax366625.CountingClasses

/-!
---
title: Post-processing terms and one-call reductions
type: definition
---
A polynomial term over $L$ denotes a number computed from an ordered
$L$-structure: a numeral, the number of elements of a definable relation, a
sum, or a product. A post-processing term also uses the answer of an oracle,
powers of two with a polynomial exponent, and the operations $+$, $\times$,
truncated subtraction, division, and remainder of natural numbers.

A one-call reduction from $C$ to $D$ is a relativized ordered first-order
interpretation $I$, nonempty on nonempty structures, and a post-processing
term $t$ such that $C(A) = t(A, D(I(A)))$ for every nonempty finite
structure $A$ and every linear order on it: a restricted form of the metric
reductions of Krentel, in the statement of Faliszewski and Hemaspaandra. A
counting problem is in the one-call closure of a class when it reduces with
one call to a member of the class, one-call hard when every member reduces
to it with one call, and one-call complete when both hold. The closure,
rather than the class, is the right notion: as Toda and Watanabe showed, #P
is presumably not closed under such reductions.
-/

namespace Lax859101.OneCallReductions

open Lax366625.CountingProblems Lax904597.Relativized

open FirstOrder

open Language Structure

/-- Terms denoting numbers polynomial in the size of the instance: numerals,
definable cardinalities, sums and products. -/
inductive PolyTerm (L : Language.{0, 0}) : Type 1
  /-- A numeral. -/
  | num (k : ℕ) : PolyTerm L
  /-- The number of tagged tuples satisfying their tag's domain formula, i.e.,
  the size of the universe of a relativized interpretation. -/
  | card {Tag : Type} [Finite Tag] {dim : ℕ}
      (J : RelFOInterpretation (L.sum Language.order) Language.empty Tag dim) : PolyTerm L
  /-- A sum. -/
  | add (p q : PolyTerm L) : PolyTerm L
  /-- A product. -/
  | mul (p q : PolyTerm L) : PolyTerm L

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a polynomial term at an ordered structure. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] : PolyTerm L → ℕ
  | num k => k
  | card J => Nat.card (J.MapRel A)
  | add p q => p.eval A + q.eval A
  | mul p q => p.eval A * q.eval A

end PolyTerm

/-- The arithmetic applied to the answer of an oracle call: polynomial terms,
powers of two with a polynomial exponent, and the operations `+`, `*`,
truncated `-`, `/` and `%` of the natural numbers. -/
inductive PostTerm (L : Language.{0, 0}) : Type 1
  /-- The answer of the oracle. -/
  | oracle : PostTerm L
  /-- A polynomial term. -/
  | poly (p : PolyTerm L) : PostTerm L
  /-- Two to the power of a polynomial term. -/
  | pow2 (p : PolyTerm L) : PostTerm L
  /-- A sum. -/
  | add (s t : PostTerm L) : PostTerm L
  /-- A product. -/
  | mul (s t : PostTerm L) : PostTerm L
  /-- A truncated difference. -/
  | sub (s t : PostTerm L) : PostTerm L
  /-- A quotient. -/
  | div (s t : PostTerm L) : PostTerm L
  /-- A remainder. -/
  | mod (s t : PostTerm L) : PostTerm L

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a post-processing term at an ordered structure, given the
answer `c` of the oracle. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) : PostTerm L → ℕ
  | oracle => c
  | poly p => p.eval A
  | pow2 p => 2 ^ p.eval A
  | add s t => s.eval A c + t.eval A c
  | mul s t => s.eval A c * t.eval A c
  | sub s t => s.eval A c - t.eval A c
  | div s t => s.eval A c / t.eval A c
  | mod s t => s.eval A c % t.eval A c

end PostTerm

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- A one-call counting reduction: a relativized ordered interpretation and a
post-processing term recovering the count of the source from the count of the
interpreted instance. -/
structure OneCallReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- The arithmetic applied to the answer of the oracle. -/
  post : PostTerm L
  /-- The count of the source is the post-processed count of the interpreted
  instance, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = post.eval A (D (toRelInterpretation.MapRel A))

open Lax366625.CountingProblems Lax366625.CountingClasses

/-- A counting problem is in the **one-call closure** of a class when it reduces
with one call to a problem of the class. -/
def OneCallMem (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    Prop :=
  ∃ (L'' : Language.{0, 0}) (_ : L''.IsRelational) (D : CountingProblem L''),
    K.Mem D ∧ Nonempty (OneCallReduction C D)

/-- A counting problem is **one-call hard** for a class when every problem of the
class reduces to it with one call. -/
def OneCallHard (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    K.Mem D → Nonempty (OneCallReduction D C)

/-- A counting problem is **one-call complete** for a class when it is in the
one-call closure of the class and one-call hard for it. -/
def OneCallComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  OneCallMem K C ∧ OneCallHard K C

end Lax859101.OneCallReductions
