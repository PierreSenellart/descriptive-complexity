/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.OrderWalk

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

/- The language of arithmetic lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.order` and the vocabularies of the problem
catalog – a project-local `Language` namespace would shadow Mathlib's under
`open Language`. -/
namespace FirstOrder

namespace Language

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
finite linear order by `DescriptiveComplexity.arithStructure`. -/
protected def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩
  deriving IsRelational

/-- The order symbol of the arithmetic vocabulary. -/
abbrev arithLe : Language.arith.Relations 2 := .le

/-- The addition symbol of the arithmetic vocabulary. -/
abbrev arithPlus : Language.arith.Relations 3 := .plus

/-- The multiplication symbol of the arithmetic vocabulary. -/
abbrev arithTimes : Language.arith.Relations 3 := .times

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The canonical interpretation on a finite linear order -/

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : Language.arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)

variable {A}

omit [Finite A] in
@[simp]
theorem relMap_arithLe (x : Fin 2 → A) :
    RelMap (L := Language.arith) arithLe x ↔ x 0 ≤ x 1 := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_arithPlus (x : Fin 3 → A) :
    RelMap (L := Language.arith) arithPlus x ↔ orank (x 0) + orank (x 1) = orank (x 2) :=
  Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_arithTimes (x : Fin 3 → A) :
    RelMap (L := Language.arith) arithTimes x ↔ orank (x 0) * orank (x 1) = orank (x 2) :=
  Iff.rfl

end Structures

/-! ### The symbols of the arithmetic expansion of a vocabulary -/

section Symbols

variable (L : Language.{0, 0})

/-- The order symbol, in the arithmetic expansion of `L`. -/
abbrev aLeSym : (L.sum Language.arith).Relations 2 := Sum.inr arithLe

/-- The addition symbol, in the arithmetic expansion of `L`. -/
abbrev aPlusSym : (L.sum Language.arith).Relations 3 := Sum.inr arithPlus

/-- The multiplication symbol, in the arithmetic expansion of `L`. -/
abbrev aTimesSym : (L.sum Language.arith).Relations 3 := Sum.inr arithTimes

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
    RelMap (aPlusSym L) x ↔ orank (x 0) + orank (x 1) = orank (x 2) := Iff.rfl

omit [Finite A] in
@[simp]
theorem relMap_aTimesSym (x : Fin 3 → A) :
    RelMap (aTimesSym L) x ↔ orank (x 0) * orank (x 1) = orank (x 2) := Iff.rfl

end ExpansionSemantics

/-! ### The transport of an ordered formula into the arithmetic expansion -/

section Transport

variable (L : Language.{0, 0}) [L.IsRelational]

/-- **The arithmetic expansion extends the ordered one**: the language map
sending the order symbol of `Language.order` to the order symbol of
`Language.arith`, and every input symbol to itself. -/
def sumOrderToArith : L.sum Language.order →ᴸ L.sum Language.arith where
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

/-- `t₁ ≤ t₂`, as a formula over the arithmetic expansion. -/
noncomputable def aLeF (t₁ t₂ : (L.sum Language.arith).Term α) :
    (L.sum Language.arith).Formula α :=
  Relations.formula₂ (aLeSym L) t₁ t₂

/-- `t₁ < t₂`, as a formula over the arithmetic expansion. -/
noncomputable def aLtF (t₁ t₂ : (L.sum Language.arith).Term α) :
    (L.sum Language.arith).Formula α :=
  aLeF t₁ t₂ ⊓ ∼(aLeF t₂ t₁)

/-- `t₁ + t₂ = t₃`, as a formula over the arithmetic expansion. -/
noncomputable def aPlusF (t₁ t₂ t₃ : (L.sum Language.arith).Term α) :
    (L.sum Language.arith).Formula α :=
  Relations.formula (aPlusSym L) ![t₁, t₂, t₃]

/-- `t₁ * t₂ = t₃`, as a formula over the arithmetic expansion. -/
noncomputable def aTimesF (t₁ t₂ t₃ : (L.sum Language.arith).Term α) :
    (L.sum Language.arith).Formula α :=
  Relations.formula (aTimesSym L) ![t₁, t₂, t₃]

/-- The variable `x` holds a minimum. -/
noncomputable def aMinF (x : α) : (L.sum Language.arith).Formula α :=
  (aLeF (Term.var (Sum.inl x)) (Term.var (Sum.inr 0))).iAlls (Fin 1)

/-- The variable `x` holds a maximum. -/
noncomputable def aMaxF (x : α) : (L.sum Language.arith).Formula α :=
  (aLeF (Term.var (Sum.inr 0)) (Term.var (Sum.inl x))).iAlls (Fin 1)

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] {v : α → A}

omit [Finite A] in
@[simp]
theorem realize_aLeF (t₁ t₂ : (L.sum Language.arith).Term α) :
    (aLeF t₁ t₂).Realize v ↔ t₁.realize v ≤ t₂.realize v := by
  rw [aLeF, Formula.realize_rel₂]
  exact Iff.rfl

omit [Finite A] in
@[simp]
theorem realize_aLtF (t₁ t₂ : (L.sum Language.arith).Term α) :
    (aLtF t₁ t₂).Realize v ↔ t₁.realize v < t₂.realize v := by
  rw [aLtF, Formula.realize_inf, Formula.realize_not, realize_aLeF, realize_aLeF]
  exact lt_iff_le_not_ge.symm

omit [Finite A] in
@[simp]
theorem realize_aPlusF (t₁ t₂ t₃ : (L.sum Language.arith).Term α) :
    (aPlusF t₁ t₂ t₃).Realize v ↔
      orank (t₁.realize v) + orank (t₂.realize v) = orank (t₃.realize v) := by
  rw [aPlusF, Formula.realize_rel]
  exact Iff.rfl

omit [Finite A] in
@[simp]
theorem realize_aTimesF (t₁ t₂ t₃ : (L.sum Language.arith).Term α) :
    (aTimesF t₁ t₂ t₃).Realize v ↔
      orank (t₁.realize v) * orank (t₂.realize v) = orank (t₃.realize v) := by
  rw [aTimesF, Formula.realize_rel]
  exact Iff.rfl

omit [Finite A] in
@[simp]
theorem realize_aMinF (x : α) : (aMinF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [aMinF]
  simp only [Formula.realize_iAlls, realize_aLeF, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

omit [Finite A] in
@[simp]
theorem realize_aMaxF (x : α) : (aMaxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [aMaxF]
  simp only [Formula.realize_iAlls, realize_aLeF, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

end Formulas

/-! ### Ranks, minima and covers

The order facts every walk over the ranks needs, stated once here because both
routes to a complexity bound use them: the induction of
`DescriptiveComplexity.ArithmeticFixedPoint` and the head programs of
`DescriptiveComplexity.HeadArith`. -/

section Ranks

variable {A : Type} [LinearOrder A] [Finite A]

/-- An element of rank `0` is least. -/
theorem isMin_of_orank_eq_zero {z : A} (h : orank z = 0) (a : A) : z ≤ a := by
  by_contra hlt
  exact absurd (orank_lt_orank (lt_of_not_ge hlt)) (by omega)

/-- The rank of an element with an immediate predecessor is one more. -/
theorem orank_eq_succ_of_pred {y' y : A} (h1 : y' < y) (h2 : ∀ a : A, ¬(y' < a ∧ a < y)) :
    orank y = orank y' + 1 :=
  orank_covBy ⟨h1, fun a ha hb => h2 a ⟨ha, hb⟩⟩

/-- **A rank one higher is a cover**: the converse of
`DescriptiveComplexity.orank_covBy`, which is what lets a walk step a head by
choosing the element of the next rank. -/
theorem covBy_of_orank_succ {w z : A} (h : orank z = orank w + 1) : w ⋖ z := by
  refine ⟨lt_of_le_of_ne (orank_le_iff.mp (by omega)) (fun he => by rw [he] at h; omega), ?_⟩
  intro e h1 h2
  have := orank_lt_orank h1
  have := orank_lt_orank h2
  omega

/-- An element of positive rank has an immediate predecessor, of the rank
below. -/
theorem exists_pred_of_orank_succ {z : A} {k : ℕ} (h : orank z = k + 1) :
    ∃ z' : A, orank z' = k ∧ z' < z ∧ ∀ a : A, ¬(z' < a ∧ a < z) := by
  have hk : k < Nat.card A := by
    have := orank_lt_card z
    omega
  obtain ⟨z', hz'⟩ := exists_orank_eq (A := A) hk
  have hcov : z' ⋖ z := covBy_of_orank_succ (by omega)
  exact ⟨z', hz', hcov.lt, fun a ha => hcov.2 ha.1 ha.2⟩

end Ranks

/-! ### Truncation, and the size of the universe -/

section Truncation

variable {A : Type} [LinearOrder A] [Finite A]

/-- **Addition is truncated at the size of the universe**: a sum has a witness
exactly when it is small enough to be a rank. This is what makes “`x + y`
overflows” a first-order statement. -/
theorem no_plus_iff_card_le (x y : A) :
    (¬∃ z : A, orank x + orank y = orank z) ↔ Nat.card A ≤ orank x + orank y := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨z, hz⟩ := exists_orank_eq (A := A) (m := orank x + orank y) (by omega)
    exact h ⟨z, hz.symm⟩
  · rintro hle ⟨z, hz⟩
    exact absurd (orank_lt_card z) (by omega)

variable [Nonempty A]

/-- **The parity of the universe is a numeric predicate.** The greatest element
has rank `Nat.card A - 1`, so the universe has an even number of elements
exactly when no element doubles to the greatest one. The order alone cannot say
this (`DescriptiveComplexity.even_not_foDefinable`); addition can. -/
theorem even_card_iff_forall_isTop :
    Even (Nat.card A) ↔
      ∀ z : A, (∀ a : A, a ≤ z) → ¬∃ h : A, orank h + orank h = orank z := by
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
noncomputable def evenCardSentence : (L.sum Language.arith).Sentence :=
  ((aMaxF (Sum.inr 0)).imp
      (∼((aPlusF (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))
            (Term.var (Sum.inl (Sum.inr 0)))).iExs (Fin 1)))).iAlls (Fin 1)

variable {L}
variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

@[simp]
theorem realize_evenCardSentence : A ⊨ evenCardSentence L ↔ Even (Nat.card A) := by
  rw [even_card_iff_forall_isTop (A := A)]
  simp only [Sentence.Realize, evenCardSentence, Formula.realize_iAlls, Formula.realize_imp,
    realize_aMaxF, Formula.realize_not, Formula.realize_iExs, realize_aPlusF, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro h z hz ⟨w, hw⟩
    exact h (fun _ => z) hz ⟨fun _ => w, hw⟩
  · rintro h i hi ⟨w, hw⟩
    exact h (i 0) hi ⟨w 0, hw⟩

end EvenCard

end DescriptiveComplexity
