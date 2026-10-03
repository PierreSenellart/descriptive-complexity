import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax904597.Problems
import Lax904597.SecondOrder

/-!
---
title: Existential second-order logic with value invention
type: definition
---
Existential second-order logic with value invention, $\exists$SO[new], is
existential second-order logic whose relation variables range over the
universe of the structure extended by finitely many invented values, in the
style of the object-creating query languages of Abiteboul, Hull and Vianu
(1995), chapter 18. An
instance $A$ and a number $m$ of invented values give the extended structure
on the disjoint union of $A$ and $m$ new elements, over the vocabulary of $A$
together with one unary predicate marking the original elements: the symbols
of $A$ hold on original elements exactly where they hold in $A$, and invented
values are related to nothing. A decision problem is $\exists$SO[new]-definable
when, for one existential second-order block and one first-order kernel, a
nonempty finite structure is a yes-instance exactly when for some number of
invented values the block's relation variables can be assigned relations over
the extended universe satisfying the kernel in the extended structure. The
number of invented values is unbounded, which is what takes the notion beyond
existential second-order logic; a witness is still a finite object.
-/

namespace Lax624099.ValueInvention

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language marking the original elements inside an
extended universe. -/
inductive oldRel : ℕ → Type
  /-- `old x`: the element `x` comes from the original structure, i.e., it is
  not an invented value. -/
  | old : oldRel 1
  deriving DecidableEq

/-- The one-symbol relational language marking, inside a universe extended
with invented values, the elements of the original structure. -/
def oldMark : Language :=
  ⟨fun _ => Empty, oldRel⟩

instance instIsRelationalOldMark : IsRelational oldMark :=
  fun _ => ⟨fun f => Empty.elim f⟩

open FirstOrder

open Language Structure

/-- The vocabulary of extended structures: the base vocabulary together with
the unary predicate `old` marking the elements of the original structure. -/
abbrev newLang (L : Language.{0, 0}) : Language := L.sum oldMark

section Extended

/-- The original elements of a universe extended by invented values. The
invented values are an arbitrary type, so that the same predicate reads an
extension by a *set* of them and not only by an initial segment. -/
def IsOld {A N : Type} : A ⊕ N → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The base structure carried by the extended universe: a relation symbol
holds of a tuple exactly when all its entries are original elements and it
holds of them in `A`. Invented values are related to nothing. -/
@[reducible]
def extBase (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ) :
    L.Structure (A ⊕ Fin m) where
  funMap f := isEmptyElim f
  RelMap {_k} r x := ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y

/-- The interpretation of the marking predicate on the extended universe. -/
@[reducible]
def oldMarkStructure (A : Type) (m : ℕ) : oldMark.Structure (A ⊕ Fin m) where
  RelMap | .old => fun x => IsOld (x 0)

/-- **The extended structure**: the instance `A` together with `m` invented
values, over the vocabulary `DescriptiveComplexity.newLang L`. -/
instance extStructure (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A]
    (m : ℕ) : (newLang L).Structure (A ⊕ Fin m) :=
  @sumStructure L oldMark (A ⊕ Fin m) (extBase L A m) (oldMarkStructure A m)

end Extended

section Definability

variable {L : Language.{0, 0}}

/-- **Definability in `∃SO[new]`**, existential second-order logic with value
invention: on nonempty finite structures, `P A` holds exactly when, for *some*
number `m` of invented values, the relation variables of the block `B` can be
assigned relations over the extended universe `A ⊕ Fin m` satisfying the
first-order kernel `φ` in the extended structure.

The number `m` of invented values is unbounded, which is precisely what takes
the notion beyond `Σ₁` (`DescriptiveComplexity.SigmaSODefinable`, where the
certificate lives over `A` itself): a witness is a finite object, but no
function of `|A|` bounds its size. -/
def SigmaSONewDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ B : SOBlock, ∃ φ : (soLang (newLang L) [B]).Sentence,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true

end Definability

end Lax624099.ValueInvention
