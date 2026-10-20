/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.Ordered
import Lax895169Proofs.DescriptiveComplexity.OrderWalk
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169Proofs.Foreign.FirstOrder.Language
end Lax895169Proofs.Foreign.FirstOrder.Language

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.ArithmeticLogic (arithStructure)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax895169Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax895169.ArithmeticLogic (arith arithRel)
end FirstOrder.Language

/-!
# The numeric predicates: the arithmetic expansion of a vocabulary

The vocabulary of the bottom class of the ordered world. A finite linearly
ordered universe *is* an initial segment of `ℕ`, by the rank of an element
(`DescriptiveComplexity.orank`, the number of its strict predecessors), and this
file makes the arithmetic of that segment available to formulas: the language
`FirstOrder.Language.arith` has a binary `≤` and two **ternary** symbols
`plus` and `times`, interpreted on a finite linear order by

* `plus x y z` – `orank x + orank y = orank z`,
* `times x y z` – `orank x * orank y = orank z`.

Relations, not functions, and therefore *truncated*: a sum or product that does
not fit in the universe simply has no witness, and “`x + y` overflows” is the
first-order `¬∃z, plus x y z` (`DescriptiveComplexity.no_plus_iff_card_le`).

## Why relations of the *order*, and not a new sort of data

The numeric predicates are not extra input relations that an instance happens
to carry: they are **functions of the linear order**, computed by `orank`. Three
consequences, all of them design constraints rather than remarks.

* The canonical structure needs `[LinearOrder A] [Finite A]`, where Mathlib's
  `FirstOrder.Language.orderStructure` needs only `[LE A]`. It is still an
  `instance`; it simply does not fire on an infinite type, which is correct –
  the arithmetic of an infinite universe is not what this vocabulary means.
* There is no order-free reading of this vocabulary at all. Every logic built
  on it is intrinsically a logic of ordered structures, and the class
  `DescriptiveComplexity.AC0Definable` accordingly has no `…Free` variant,
  unlike ∃SO, `SO(LFP)` or `SO(PFP)`.
* Because the interpretation is canonical, an *interpretation* of one
  vocabulary in another does not get the numeric predicates for free: it must
  define the arithmetic of the interpreted universe, which is why the arithmetic
  analogue of `DescriptiveComplexity.FOInterpretation.ordExtend` is real work
  and not plumbing.

## The transport from the ordered expansion

`DescriptiveComplexity.sumOrderToArith` is the language map
`L.sum Language.order →ᴸ L.sum Language.arith` sending `≤` to `≤`, with its
`FirstOrder.Language.LHom.IsExpansionOn` instance, so that every FO(≤) sentence
and every FO(≤) gadget formula of this library can be read as an arithmetic one
(`DescriptiveComplexity.FODefinable.ac0Definable` is the consumer).

It is stated at the level of the *sum* rather than as a map
`Language.order →ᴸ Language.arith` lifted by `LHom.sumMap`, deliberately:
`Language.order.Structure` is not an instance in Mathlib (it would fire on every
`LE`), so the generic `sumMap` instance would have to be fed a `letI`-supplied
structure at every use site, whereas the sum-level map has both structures
available by instance search.

## What is here, and what needs it

Besides the vocabulary and its semantics: the formula builders (`aLeF`, `aLtF`,
`aPlusF`, `aTimesF`, `aMaxF`, `aMinF`) with their realization lemmas, the
overflow characterization, and one worked sentence –
`DescriptiveComplexity.evenCardSentence`, which says that the universe has an
even number of elements, by reading the parity of the rank of its greatest
element. That sentence is what separates FO(≤) from AC⁰
(`DescriptiveComplexity.Problems.Even`), and it is the smallest example of the
one thing the numeric predicates buy over a bare order: access to the *size* of
the universe, one bit at a time.
-/

namespace FirstOrder

namespace Language

open Lax895169Proofs.Foreign.FirstOrder.Language in
/-- The order symbol of the arithmetic vocabulary. -/
abbrev _root_.Lax895169Proofs.Foreign.FirstOrder.Language.arithLe : Lax895169.ArithmeticLogic.arith.Relations 2 := .le

export Lax895169Proofs.Foreign.FirstOrder.Language (arithLe)

open Lax895169Proofs.Foreign.FirstOrder.Language in
/-- The addition symbol of the arithmetic vocabulary. -/
abbrev _root_.Lax895169Proofs.Foreign.FirstOrder.Language.arithPlus : Lax895169.ArithmeticLogic.arith.Relations 3 := .plus

export Lax895169Proofs.Foreign.FirstOrder.Language (arithPlus)

open Lax895169Proofs.Foreign.FirstOrder.Language in
/-- The multiplication symbol of the arithmetic vocabulary. -/
abbrev _root_.Lax895169Proofs.Foreign.FirstOrder.Language.arithTimes : Lax895169.ArithmeticLogic.arith.Relations 3 := .times

export Lax895169Proofs.Foreign.FirstOrder.Language (arithTimes)

end Language

end FirstOrder

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The canonical interpretation on a finite linear order -/

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

variable {A}

omit [Finite A] in
@[simp]
theorem relMap_arithLe (x : Fin 2 → A) :
    RelMap (L := Lax895169.ArithmeticLogic.arith) Lax895169Proofs.Foreign.FirstOrder.Language.arithLe x ↔ x 0 ≤ x 1 := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_arithPlus (x : Fin 3 → A) :
    RelMap (L := Lax895169.ArithmeticLogic.arith) Lax895169Proofs.Foreign.FirstOrder.Language.arithPlus x ↔ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) :=
  Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_arithTimes (x : Fin 3 → A) :
    RelMap (L := Lax895169.ArithmeticLogic.arith) Lax895169Proofs.Foreign.FirstOrder.Language.arithTimes x ↔ Lax895169.BitPredicate.orank (x 0) * Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) :=
  Iff.rfl

end Structures

/-! ### The symbols of the arithmetic expansion of a vocabulary -/

section Symbols

variable (L : Language.{0, 0})

/-- The order symbol, in the arithmetic expansion of `L`. -/
abbrev aLeSym : (L.sum Lax895169.ArithmeticLogic.arith).Relations 2 := Sum.inr Lax895169Proofs.Foreign.FirstOrder.Language.arithLe

/-- The addition symbol, in the arithmetic expansion of `L`. -/
abbrev aPlusSym : (L.sum Lax895169.ArithmeticLogic.arith).Relations 3 := Sum.inr Lax895169Proofs.Foreign.FirstOrder.Language.arithPlus

/-- The multiplication symbol, in the arithmetic expansion of `L`. -/
abbrev aTimesSym : (L.sum Lax895169.ArithmeticLogic.arith).Relations 3 := Sum.inr Lax895169Proofs.Foreign.FirstOrder.Language.arithTimes

end Symbols

/-! ### The numeric predicates of the arithmetic expansion -/

section ExpansionSemantics

variable {L : Language.{0, 0}} {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
@[simp]
theorem relMap_aLeSym (x : Fin 2 → A) :
    RelMap (aLeSym L) x ↔ x 0 ≤ x 1 := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_aPlusSym (x : Fin 3 → A) :
    RelMap (aPlusSym L) x ↔ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_aTimesSym (x : Fin 3 → A) :
    RelMap (aTimesSym L) x ↔ Lax895169.BitPredicate.orank (x 0) * Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) := Iff.rfl

end ExpansionSemantics

/-! ### The transport of an ordered formula into the arithmetic expansion -/

section Transport

variable (L : Language.{0, 0}) [L.IsRelational]

/-- **The arithmetic expansion extends the ordered one**: the language map
sending the order symbol of `Language.order` to the order symbol of
`Language.arith`, and every input symbol to itself. -/
def sumOrderToArith : L.sum Language.order →ᴸ L.sum Lax895169.ArithmeticLogic.arith where
  onRelation := fun {_} R =>
    match R with
    | Sum.inl r => Sum.inl r
    | Sum.inr .le => aLeSym L

variable {L}

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A]

/-- The transport is an expansion: both vocabularies read `≤` as the order and
the input symbols as themselves. -/
instance sumOrderToArith_isExpansionOn : (sumOrderToArith L).IsExpansionOn A where
  map_onRelation := fun {_} R x => by
    cases R with
    | inl r => rfl
    | inr r => cases r with | le => rfl

end Transport

/-! ### Formula builders -/

section Formulas

variable {L : Language.{0, 0}} {α : Type}

/-- `x ≤ y`, as a formula over the arithmetic expansion. -/
noncomputable def aLeF (x y : α) : (L.sum Lax895169.ArithmeticLogic.arith).Formula α :=
  Relations.formula₂ (aLeSym L) (Term.var x) (Term.var y)

/-- `x + y = z`, as a formula over the arithmetic expansion. -/
noncomputable def aPlusF (x y z : α) : (L.sum Lax895169.ArithmeticLogic.arith).Formula α :=
  Relations.formula (aPlusSym L) ![Term.var x, Term.var y, Term.var z]

/-- `x * y = z`, as a formula over the arithmetic expansion. -/
noncomputable def aTimesF (x y z : α) : (L.sum Lax895169.ArithmeticLogic.arith).Formula α :=
  Relations.formula (aTimesSym L) ![Term.var x, Term.var y, Term.var z]

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] {v : α → A}

omit [Finite A] in
@[simp]
theorem realize_aLeF (x y : α) : (aLeF (L := L) x y).Realize v ↔ v x ≤ v y := by
  rw [aLeF, Formula.realize_rel₂]
  exact Iff.rfl

omit [Finite A] in
@[simp]
theorem realize_aPlusF (x y z : α) :
    (aPlusF (L := L) x y z).Realize v ↔ Lax895169.BitPredicate.orank (v x) + Lax895169.BitPredicate.orank (v y) = Lax895169.BitPredicate.orank (v z) := by
  rw [aPlusF, Formula.realize_rel]
  exact Iff.rfl

omit [Finite A] in
@[simp]
theorem realize_aTimesF (x y z : α) :
    (aTimesF (L := L) x y z).Realize v ↔ Lax895169.BitPredicate.orank (v x) * Lax895169.BitPredicate.orank (v y) = Lax895169.BitPredicate.orank (v z) := by
  rw [aTimesF, Formula.realize_rel]
  exact Iff.rfl

end Formulas

/-! ### Ranks, minima and covers

The order facts every walk over the ranks needs, stated once here because both
routes to a complexity bound use them: the induction of
`DescriptiveComplexity.ArithmeticFixedPoint` and the head programs of
`DescriptiveComplexity.HeadArith`. -/

section Ranks

variable {A : Type} [LinearOrder A] [Finite A]

/-- An element of rank `0` is least. -/
theorem isMin_of_orank_eq_zero {z : A} (h : Lax895169.BitPredicate.orank z = 0) (a : A) : z ≤ a := by
  by_contra hlt
  exact absurd (orank_lt_orank (lt_of_not_ge hlt)) (by omega)

/-- The rank of an element with an immediate predecessor is one more. -/
theorem orank_eq_succ_of_pred {y' y : A} (h1 : y' < y) (h2 : ∀ a : A, ¬(y' < a ∧ a < y)) :
    Lax895169.BitPredicate.orank y = Lax895169.BitPredicate.orank y' + 1 :=
  orank_covBy ⟨h1, fun a ha hb => h2 a ⟨ha, hb⟩⟩

/-- **A rank one higher is a cover**: the converse of
`DescriptiveComplexity.orank_covBy`, which is what lets a walk step a head by
choosing the element of the next rank. -/
theorem covBy_of_orank_succ {w z : A} (h : Lax895169.BitPredicate.orank z = Lax895169.BitPredicate.orank w + 1) : w ⋖ z := by
  refine ⟨lt_of_le_of_ne (orank_le_iff.mp (by omega)) (fun he => by rw [he] at h; omega), ?_⟩
  intro e h1 h2
  have := orank_lt_orank h1
  have := orank_lt_orank h2
  omega

/-- An element of positive rank has an immediate predecessor, of the rank
below. -/
theorem exists_pred_of_orank_succ {z : A} {k : ℕ} (h : Lax895169.BitPredicate.orank z = k + 1) :
    ∃ z' : A, Lax895169.BitPredicate.orank z' = k ∧ z' < z ∧ ∀ a : A, ¬(z' < a ∧ a < z) := by
  have hk : k < Nat.card A := by
    have := orank_lt_card z
    omega
  obtain ⟨z', hz'⟩ := exists_orank_eq (A := A) hk
  have hcov : z' ⋖ z := covBy_of_orank_succ (by omega)
  exact ⟨z', hz', hcov.lt, fun a ha => hcov.2 ha.1 ha.2⟩

end Ranks

/-! ### Truncation, and the size of the universe -/

section Truncation

end Truncation

/-! ### A sentence for the parity of the universe -/

section EvenCard

end EvenCard

end Lax895169Proofs.DescriptiveComplexity


