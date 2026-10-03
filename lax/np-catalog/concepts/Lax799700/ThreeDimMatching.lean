import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: 3-dimensional matching
type: theorem
---
3-DIMENSIONAL MATCHING: given three marked classes and a set of triples,
one element from each class, is there a set of triples covering every
marked element exactly once? The vocabulary carries three unary marks and
one ternary relation, and a yes-instance admits a matching
(IsMatchingOn), a sub-relation of the triples that covers each marked
element exactly once; nothing asks the three classes to be disjoint or
to exhaust the universe. Membership is by an existential second-order
definition, hardness by an ordered first-order reduction from SAT.

-/

namespace Lax799700.ThreeDimMatching

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tripleSysRel : ℕ → Type where
/-- `xEl a`: `a` belongs to the first class. -/
  | xEl : tripleSysRel 1
/-- `yEl a`: `a` belongs to the second class. -/
  | yEl : tripleSysRel 1
/-- `zEl a`: `a` belongs to the third class. -/
  | zEl : tripleSysRel 1
/-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
  | trip : tripleSysRel 3
  deriving DecidableEq

/-- The relational language of triple systems: three marked classes and a
ternary relation. -/
def tripleSys : FirstOrder.Language :=
  ⟨fun _ => Empty, tripleSysRel⟩

instance instIsRelationalTripleSys : FirstOrder.Language.IsRelational tripleSys := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `xEl a`: `a` belongs to the first class. -/
abbrev tsXEl : tripleSys.Relations 1 :=
  .xEl

/-- `yEl a`: `a` belongs to the second class. -/
abbrev tsYEl : tripleSys.Relations 1 :=
  .yEl

/-- `zEl a`: `a` belongs to the third class. -/
abbrev tsZEl : tripleSys.Relations 1 :=
  .zEl

/-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
abbrev tsTrip : tripleSys.Relations 3 :=
  .trip

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [tripleSys.Structure A]

/-- `xEl a`: `a` belongs to the first class.  -/
def TSXEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsXEl ![a0]

/-- `yEl a`: `a` belongs to the second class.  -/
def TSYEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsYEl ![a0]

/-- `zEl a`: `a` belongs to the third class.  -/
def TSZEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsZEl ![a0]

/-- `trip a b c`: `(a, b, c)` is one of the available triples.  -/
def TSTrip {A : Type} [tripleSys.Structure A] (a0 : A) (a1 : A) (a2 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsTrip ![a0, a1, a2]

end Shorthands

section Matching

variable {A : Type}

/-- A **matching**: a set of triples, taken from `T` and lying in the three
classes, covering every marked element exactly once. -/
def IsMatchingOn (X Y Z : A → Prop) (T : A → A → A → Prop) (M : A → A → A → Prop) : Prop :=
  (∀ x y z, M x y z → T x y z ∧ X x ∧ Y y ∧ Z z) ∧
    (∀ x, X x → ∃ y z, M x y z) ∧ (∀ y, Y y → ∃ x z, M x y z) ∧
    (∀ z, Z z → ∃ x y, M x y z) ∧
    (∀ x y z y' z', M x y z → M x y' z' → y = y' ∧ z = z') ∧
    (∀ x y z x' z', M x y z → M x' y z' → x = x' ∧ z = z') ∧
    ∀ x y z x' y', M x y z → M x' y' z → x = x' ∧ y = y'

end Matching

section Problem

variable (A : Type) [tripleSys.Structure A]

/-- A triple system is a yes-instance when some subset of its triples covers
each marked element exactly once. -/
def HasThreeDimMatching : Prop :=
  Finite A ∧ ∃ M : A → A → A → Prop,
    IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip M

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasThreeDimMatching` is isomorphism-invariant. -/
axiom hasThreeDimMatching_iso : ∀ {A B : Type} [Lax799700.ThreeDimMatching.tripleSys.Structure A] [Lax799700.ThreeDimMatching.tripleSys.Structure B],
  (A ≃[Lax799700.ThreeDimMatching.tripleSys] B) → (HasThreeDimMatching A ↔ HasThreeDimMatching B)

/-- The problem ThreeDimMatching: does the structure satisfy `HasThreeDimMatching`? -/
def ThreeDimMatching : DecisionProblem Lax799700.ThreeDimMatching.tripleSys :=
  DecisionProblem.ofPred HasThreeDimMatching

/-- The yes-instances of ThreeDimMatching are exactly the structures satisfying `HasThreeDimMatching`. -/
axiom threeDimMatching_iff : ∀ (A : Type) [Lax799700.ThreeDimMatching.tripleSys.Structure A], ThreeDimMatching A ↔ HasThreeDimMatching A

/-- ThreeDimMatching is NP-complete. -/
axiom threeDimMatching_NP_complete : NP.Complete ThreeDimMatching

end Lax799700.ThreeDimMatching
