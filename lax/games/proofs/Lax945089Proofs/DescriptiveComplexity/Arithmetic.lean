/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Ordered
import Lax945089Proofs.DescriptiveComplexity.OrderWalk
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax945089Proofs.Foreign.FirstOrder.Language
end Lax945089Proofs.Foreign.FirstOrder.Language

namespace Lax945089Proofs.DescriptiveComplexity
export Lax895169.ArithmeticLogic (arithStructure)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax945089Proofs.DescriptiveComplexity

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

open Lax945089Proofs.Foreign.FirstOrder.Language in
/-- The order symbol of the arithmetic vocabulary. -/
abbrev _root_.Lax945089Proofs.Foreign.FirstOrder.Language.arithLe : Lax895169.ArithmeticLogic.arith.Relations 2 := .le

export Lax945089Proofs.Foreign.FirstOrder.Language (arithLe)

open Lax945089Proofs.Foreign.FirstOrder.Language in
/-- The addition symbol of the arithmetic vocabulary. -/
abbrev _root_.Lax945089Proofs.Foreign.FirstOrder.Language.arithPlus : Lax895169.ArithmeticLogic.arith.Relations 3 := .plus

export Lax945089Proofs.Foreign.FirstOrder.Language (arithPlus)

end Language

end FirstOrder

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The canonical interpretation on a finite linear order -/

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

variable {A}

omit [Finite A] in
@[simp]
theorem relMap_arithLe (x : Fin 2 → A) :
    RelMap (L := Lax895169.ArithmeticLogic.arith) Lax945089Proofs.Foreign.FirstOrder.Language.arithLe x ↔ x 0 ≤ x 1 := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_arithPlus (x : Fin 3 → A) :
    RelMap (L := Lax895169.ArithmeticLogic.arith) Lax945089Proofs.Foreign.FirstOrder.Language.arithPlus x ↔ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) :=
  Iff.rfl

end Structures

/-! ### The symbols of the arithmetic expansion of a vocabulary -/

section Symbols

variable (L : Language.{0, 0})

/-- The order symbol, in the arithmetic expansion of `L`. -/
abbrev aLeSym : (L.sum Lax895169.ArithmeticLogic.arith).Relations 2 := Sum.inr Lax945089Proofs.Foreign.FirstOrder.Language.arithLe

/-- The addition symbol, in the arithmetic expansion of `L`. -/
abbrev aPlusSym : (L.sum Lax895169.ArithmeticLogic.arith).Relations 3 := Sum.inr Lax945089Proofs.Foreign.FirstOrder.Language.arithPlus

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

end ExpansionSemantics

/-! ### The transport of an ordered formula into the arithmetic expansion -/

section Transport

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

/-- The variable `x` holds a maximum. -/
noncomputable def aMaxF (x : α) : (L.sum Lax895169.ArithmeticLogic.arith).Formula α :=
  (aLeF (Sum.inr 0) (Sum.inl x)).iAlls (Fin 1)

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
theorem realize_aMaxF (x : α) : (aMaxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [aMaxF]
  simp only [Formula.realize_iAlls, realize_aLeF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

end Formulas

/-! ### Ranks, minima and covers

The order facts every walk over the ranks needs, stated once here because both
routes to a complexity bound use them: the induction of
`DescriptiveComplexity.ArithmeticFixedPoint` and the head programs of
`DescriptiveComplexity.HeadArith`. -/

section Ranks

end Ranks

/-! ### Truncation, and the size of the universe -/

section Truncation

variable {A : Type} [LinearOrder A] [Finite A]

variable [Nonempty A]

/-- **The parity of the universe is a numeric predicate.** The greatest element
has rank `Nat.card A - 1`, so the universe has an even number of elements
exactly when no element doubles to the greatest one. The order alone cannot say
this (`DescriptiveComplexity.even_not_foDefinable`); addition can. -/
theorem even_card_iff_forall_isTop :
    Even (Nat.card A) ↔
      ∀ z : A, (∀ a : A, a ≤ z) → ¬∃ h : A, Lax895169.BitPredicate.orank h + Lax895169.BitPredicate.orank h = Lax895169.BitPredicate.orank z := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain ⟨m, hm⟩ : ∃ z : A, ∀ a : A, a ≤ z := by
    obtain ⟨z, hz⟩ := exists_orank_eq (A := A) (m := Nat.card A - 1) (by omega)
    exact ⟨z, fun a => orank_le_iff.mp (by have := orank_lt_card a; omega)⟩
  constructor
  · rintro hev z hz ⟨h, hh⟩
    rw [orank_isTop hz] at hh
    obtain ⟨k, hk⟩ := hev
    omega
  · intro h
    by_contra hodd
    have hev : Even (Nat.card A - 1) := by
      rcases Nat.even_or_odd (Nat.card A) with he | ho
      · exact absurd he hodd
      · obtain ⟨k, hk⟩ := ho
        exact ⟨k, by omega⟩
    obtain ⟨k, hk⟩ := hev
    obtain ⟨w, hw⟩ := exists_orank_eq (m := k) (A := A) (by omega)
    exact h m hm ⟨w, by rw [orank_isTop hm, hw, hk]⟩

end Truncation

/-! ### A sentence for the parity of the universe -/

section EvenCard

variable (L : Language.{0, 0})

/-- **The universe has an even number of elements**, as a sentence of the
arithmetic expansion: no maximum is the double of anything. The two quantifiers
are the whole sentence – nothing about the input vocabulary is read, so this is
a statement about the *size* of the instance, which is exactly what a bare order
cannot express and the numeric predicates can. -/
noncomputable def evenCardSentence : (L.sum Lax895169.ArithmeticLogic.arith).Sentence :=
  ((aMaxF (Sum.inr 0)).imp
      (∼((aPlusF (Sum.inr 0) (Sum.inr 0) (Sum.inl (Sum.inr 0))).iExs (Fin 1)))).iAlls (Fin 1)

variable {L}

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

@[simp]
theorem realize_evenCardSentence : A ⊨ evenCardSentence L ↔ Even (Nat.card A) := by
  rw [even_card_iff_forall_isTop (A := A)]
  simp only [Sentence.Realize, evenCardSentence, Formula.realize_iAlls, Formula.realize_imp,
    realize_aMaxF, Formula.realize_not, Formula.realize_iExs, realize_aPlusF, Sum.elim_inl,
    Sum.elim_inr]
  constructor
  · rintro h z hz ⟨w, hw⟩
    exact h (fun _ => z) hz ⟨fun _ => w, hw⟩
  · rintro h i hi ⟨w, hw⟩
    exact h (i 0) hi ⟨w 0, hw⟩

end EvenCard

end Lax945089Proofs.DescriptiveComplexity


