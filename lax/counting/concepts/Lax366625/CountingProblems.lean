import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Lax904597.Interpretations
import Lax904597.Problems
import Lax904597.Relativized
import Mathlib.Order.Lattice.Nat

/-!
---
title: Counting problems and parsimonious reductions
type: definition
---
A counting problem over a relational vocabulary $L$ attaches a natural
number $C(A)$ to every $L$-structure $A$, the same on isomorphic structures.
Its support is the decision problem whose yes-instances are the structures
with a positive count. A problem can be given by any number attached to
structures: its value on $A$ is the least of the numbers attached to the
structures isomorphic to $A$, which is the number itself when that is
invariant.

A parsimonious reduction from $C$ to $D$, a notion due to Simon, is a
first-order interpretation under which the counts agree: $C(A) = D(I(A))$
for every nonempty finite $A$. In an ordered parsimonious reduction the interpretation reads the
ordered expansion and the equation holds for every linear order on $A$; in
a relativized one, the interpreted universe is a definable subset of the
tagged tuples, nonempty on nonempty structures.
-/

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

instance instCoeFun : CoeFun (CountingProblem L) fun _ => ∀ (A : Type) [L.Structure A], ℕ :=
  ⟨Count⟩

/-- The counting problem given by a number attached to every structure: the
least value it takes on the structures isomorphic to a given one, which is
invariant by construction. When the number is itself invariant, this is the
number. -/
noncomputable def ofFun (f : ∀ (A : Type) [L.Structure A], ℕ) : CountingProblem L where
  Count := fun A _ =>
    sInf {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n}
  iso_invariant := fun e =>
    congrArg sInf (Set.ext fun _ =>
      ⟨fun ⟨B, i, g, h⟩ => ⟨B, i, e.comp g, h⟩, fun ⟨B, i, g, h⟩ => ⟨B, i, e.symm.comp g, h⟩⟩)

/-- The decision problem underneath a counting problem: is the count
positive? -/
def support (C : CountingProblem L) : DecisionProblem L where
  Holds := fun A inst => 0 < @Count L _ C A inst
  iso_invariant := fun e => by rw [C.iso_invariant e]

end CountingProblem

variable {L} {L' : Language.{0, 0}}

/-- A *parsimonious* first-order reduction from the counting problem `C` to the
counting problem `D`: a first-order interpretation under which the two counts
agree. -/
structure ParsimoniousReduction [L.IsRelational] [L'.IsRelational] (C : CountingProblem L)
    (D : CountingProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation. -/
  toInterpretation : FOInterpretation L L' Tag dim
  /-- The counts agree, on the finite nonempty structures. -/
  correct : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    C A = D (toInterpretation.Map A)

/-- An *ordered* parsimonious reduction: a first-order interpretation over the
ordered expansion of the source vocabulary under which the two counts agree,
for every linear order of the (finite) input structure. -/
structure OrderedParsimoniousReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation, over the ordered expansion. -/
  toInterpretation : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The counts agree, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = D (toInterpretation.Map A)

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- An ordered parsimonious reduction through a **relativized**
interpretation: the two counts agree, the target structure being carried by
the definable subset of `Tag × A^dim` that the domain formula carves out. -/
structure RelOrderedParsimoniousReduction [L.IsRelational] [L'.IsRelational]
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
  /-- The counts agree, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = D (toRelInterpretation.MapRel A)

end Lax366625.CountingProblems
