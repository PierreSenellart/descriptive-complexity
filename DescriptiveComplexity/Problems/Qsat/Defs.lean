/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.PSpace

/-!
# QSAT: quantified Boolean formulas with an unbounded prefix

The vocabulary and semantics of the canonical PSPACE-complete problem
(`DescriptiveComplexity.QSAT`, also known as TQBF or QBF): is a fully quantified
Boolean formula in prenex conjunctive normal form true? Unlike the bounded
families `DescriptiveComplexity.QBF k` of `DescriptiveComplexity.Problems.Qbf` – where the
number of alternations is fixed by the *problem* and only the matrix comes
with the instance – here the quantifier prefix is part of the instance, so a
single problem carries arbitrarily many alternations. That is exactly the step
from the polynomial hierarchy to PSPACE.

## The instance

An instance is a `FirstOrder.Language.qsat`-structure. As in
`FirstOrder.Language.sat`, its elements are propositional variables and clauses
at once, with

* `isVar x`: the element `x` is a quantified propositional variable;
* `allVar x`: the variable `x` is quantified universally (existentially
  otherwise);
* `prefixLt x y`: the variable `x` is quantified *outside* the variable `y`;
* `isClause c`, `posIn c x`, `negIn c x`: the clauses of the matrix and the
  literal occurrences, exactly as for SAT.

An instance is *well formed* (`DescriptiveComplexity.QsatWf`) when `prefixLt` is a
strict linear order on the marked variables; a malformed instance is a
no-instance. Well-formedness is a first-order condition, which is what lets the
membership proof check it inside the walk.

## The semantics

Reading a quantifier prefix means recursing along `prefixLt`, and the recursion
is over a set of *remaining* variables rather than over a syntactic list. It is
packaged as an inductive predicate `DescriptiveComplexity.QsatWins`: a *position* is a
pair `(D, τ)` of a set `D` of already-quantified variables and a valuation `τ`,
and `QsatWins D τ` says that the existential player wins the game that
quantifies the variables outside `D`, innermost-first, and ends in the matrix.
An inductive definition is used rather than a recursion so that the semantics
is available on an arbitrary (possibly infinite) structure, as
`DescriptiveComplexity.DecisionProblem` requires; on a finite well-formed structure it is
the usual game value, since the three rules are then mutually exclusive and
exhaustive (`DescriptiveComplexity.qsatWins_all_iff`,
`DescriptiveComplexity.qsatWins_ex_iff`, `DescriptiveComplexity.qsatWins_leaf_iff`, proved by
inversion alone).

The quantified variable at a position is the `prefixLt`-least one not yet in
`D` (`DescriptiveComplexity.QLeast`), so the prefix is read outermost-first and the
players move in the order the instance prescribes.
-/

/- The language of quantified CNF instances with an unbounded prefix lives in
Mathlib's `FirstOrder.Language` namespace, next to `Language.sat` and
`Language.qbf`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of fully quantified Boolean formulas with
an unbounded quantifier prefix. -/
inductive qsatRel : ℕ → Type
  /-- `isVar x`: the element `x` is a quantified propositional variable. -/
  | isVar : qsatRel 1
  /-- `allVar x`: the variable `x` is quantified universally. -/
  | allVar : qsatRel 1
  /-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
  | prefixLt : qsatRel 2
  /-- `isClause c`: the element `c` is a clause of the matrix. -/
  | isClause : qsatRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qsatRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qsatRel 2
  deriving DecidableEq

/-- The relational vocabulary of fully quantified Boolean formulas: that of
CNF instances, together with the marks and the order describing the quantifier
prefix. -/
protected def qsat : Language :=
  ⟨fun _ => Empty, qsatRel⟩
  deriving IsRelational

/-- The symbol for “is a quantified variable”. -/
abbrev qsIsVar : Language.qsat.Relations 1 := .isVar

/-- The symbol for “is universally quantified”. -/
abbrev qsAllVar : Language.qsat.Relations 1 := .allVar

/-- The symbol for “is quantified outside”. -/
abbrev qsPrefixLt : Language.qsat.Relations 2 := .prefixLt

/-- The symbol for “is a clause”. -/
abbrev qsIsClause : Language.qsat.Relations 1 := .isClause

/-- The symbol for “occurs positively in”. -/
abbrev qsPosIn : Language.qsat.Relations 2 := .posIn

/-- The symbol for “occurs negatively in”. -/
abbrev qsNegIn : Language.qsat.Relations 2 := .negIn

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Reading an instance -/

section Reading

variable {A : Type} [Language.qsat.Structure A]

/-- The element `x` is a quantified propositional variable. -/
def IsQVar (x : A) : Prop := RelMap qsIsVar ![x]

/-- The variable `x` is quantified universally. -/
def IsQAll (x : A) : Prop := RelMap qsAllVar ![x]

/-- The variable `x` is quantified outside the variable `y`. -/
def QPrec (x y : A) : Prop := RelMap qsPrefixLt ![x, y]

variable (A) in
/-- An instance is *well formed* when the quantifier prefix is a strict linear
order on the marked variables. Malformed instances are no-instances; the
condition is first-order, so the membership proof can check it. -/
structure QsatWf : Prop where
  /-- The prefix order only relates quantified variables. -/
  isVar_of_prec : ∀ x y : A, QPrec x y → IsQVar x ∧ IsQVar y
  /-- The prefix order is irreflexive. -/
  irrefl : ∀ x : A, ¬QPrec x x
  /-- The prefix order is transitive. -/
  trans : ∀ x y z : A, QPrec x y → QPrec y z → QPrec x z
  /-- The prefix order is total on the quantified variables. -/
  total : ∀ x y : A, IsQVar x → IsQVar y → x ≠ y → QPrec x y ∨ QPrec y x

/-- The matrix: every clause contains a literal on a *quantified* variable that
the valuation `τ` makes true. Elements that are not clauses impose nothing,
exactly as in `DescriptiveComplexity.Satisfiable`; an occurrence on an element that the
prefix does not quantify is not a literal, so the matrix depends on `τ` only
through its values on the variables. -/
def QsatMatrix (τ : A → Prop) : Prop :=
  ∀ c : A, RelMap qsIsClause ![c] →
    ∃ x : A, IsQVar x ∧
      ((RelMap qsPosIn ![c, x] ∧ τ x) ∨ (RelMap qsNegIn ![c, x] ∧ ¬τ x))

/-- The matrix only depends on the valuation through its values on the
quantified variables. -/
theorem qsatMatrix_congr {τ τ' : A → Prop} (h : ∀ y : A, IsQVar y → (τ y ↔ τ' y))
    (hm : QsatMatrix τ) : QsatMatrix τ' := by
  intro c hc
  obtain ⟨x, hx, hlit⟩ := hm c hc
  refine ⟨x, hx, ?_⟩
  rcases hlit with ⟨hp, hv⟩ | ⟨hn, hv⟩
  · exact Or.inl ⟨hp, (h x hx).mp hv⟩
  · exact Or.inr ⟨hn, fun hv' => hv ((h x hx).mpr hv')⟩

/-- Adding a variable to the set of already-quantified ones. -/
def qAdd (D : A → Prop) (x : A) : A → Prop := fun y => y = x ∨ D y

/-- Giving the value `b` to the variable `x` in the valuation `τ`. -/
def qUpd (τ : A → Prop) (x : A) (b : Bool) : A → Prop :=
  fun y => (y = x ∧ b = true) ∨ (y ≠ x ∧ τ y)

omit [Language.qsat.Structure A] in
@[simp]
theorem qAdd_self (D : A → Prop) (x : A) : qAdd D x x := Or.inl rfl

omit [Language.qsat.Structure A] in
@[simp]
theorem qUpd_self (τ : A → Prop) (x : A) (b : Bool) : qUpd τ x b x ↔ b = true := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨rfl, h⟩⟩
  rcases h with ⟨-, hb⟩ | ⟨hne, -⟩
  · exact hb
  · exact absurd rfl hne

omit [Language.qsat.Structure A] in
theorem qUpd_ne (τ : A → Prop) {x y : A} (b : Bool) (h : y ≠ x) : qUpd τ x b y ↔ τ y := by
  refine ⟨fun hy => ?_, fun hy => Or.inr ⟨h, hy⟩⟩
  rcases hy with ⟨he, -⟩ | ⟨-, hy⟩
  · exact absurd he h
  · exact hy

/-- The variable `x` is the one the position `D` quantifies next: it is the
`prefixLt`-least variable that `D` does not contain. -/
def QLeast (D : A → Prop) (x : A) : Prop :=
  IsQVar x ∧ ¬D x ∧ ∀ y : A, IsQVar y → ¬D y → ¬QPrec y x

/-- The next variable to quantify is unique, by totality of the prefix
order. -/
theorem QLeast.unique (hwf : QsatWf A) {D : A → Prop} {x y : A}
    (hx : QLeast D x) (hy : QLeast D y) : x = y := by
  by_contra hne
  rcases hwf.total x y hx.1 hy.1 hne with h | h
  · exact hy.2.2 x hx.1 hx.2.1 h
  · exact hx.2.2 y hy.1 hy.2.1 h

end Reading

/-! ### The game

`QsatWins D τ` is the value of the position in which the variables of `D` have
already been given their values by `τ` and the remaining ones are still to be
quantified, innermost-first along the prefix order. -/

section Game

variable {A : Type} [Language.qsat.Structure A]

/-- **The quantifier game**: the existential player wins the position `(D, τ)`.
Either every variable is already quantified and the matrix holds, or the next
variable is existential and one of its two values wins, or it is universal and
both of its values win. -/
inductive QsatWins : (A → Prop) → (A → Prop) → Prop
  /-- Every variable has been quantified: the position is won exactly when the
  matrix holds. -/
  | leaf {D τ : A → Prop} (hD : ∀ x : A, IsQVar x → D x) (hm : QsatMatrix τ) : QsatWins D τ
  /-- The next variable is existential: the existential player picks a value
  winning the rest of the game. -/
  | ex {D τ : A → Prop} {x : A} (hx : QLeast D x) (hq : ¬IsQAll x) (b : Bool)
      (h : QsatWins (qAdd D x) (qUpd τ x b)) : QsatWins D τ
  /-- The next variable is universal: both values must win the rest of the
  game. -/
  | all {D τ : A → Prop} {x : A} (hx : QLeast D x) (hq : IsQAll x)
      (h : ∀ b : Bool, QsatWins (qAdd D x) (qUpd τ x b)) : QsatWins D τ

/-- **A position only depends on the values already given**: two valuations
agreeing on the quantified part `D` win the same positions. This is what makes
`(D, τ)` a position rather than a full state: the values of `τ` outside `D` are
about to be overwritten by the quantifiers. -/
theorem qsatWins_congr {D τ : A → Prop} (h : QsatWins D τ) :
    ∀ τ' : A → Prop, (∀ y : A, D y → (τ y ↔ τ' y)) → QsatWins D τ' := by
  classical
  induction h with
  | leaf hD hm => exact fun τ' hτ => .leaf hD (qsatMatrix_congr (fun y hy => hτ y (hD y hy)) hm)
  | @ex D τ x hx hq b _ ih =>
    refine fun τ' hτ => .ex hx hq b (ih _ fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx
      exact (qUpd_self τ y b).trans (qUpd_self τ' y b).symm
    · rw [qUpd_ne τ b hyx, qUpd_ne τ' b hyx]
      exact hτ y (hy.resolve_left hyx)
  | @all D τ x hx hq _ ih =>
    refine fun τ' hτ => .all hx hq fun b => (ih b _ fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx
      exact (qUpd_self τ y b).trans (qUpd_self τ' y b).symm
    · rw [qUpd_ne τ b hyx, qUpd_ne τ' b hyx]
      exact hτ y (hy.resolve_left hyx)

/-! #### The three rules read backwards

Together with `DescriptiveComplexity.QLeast.unique` the constructors are
mutually exclusive, so each of them is an equivalence: the inductive predicate
*is* the game value, and no induction is needed to see it. -/

/-- At a position where every variable is quantified, winning is satisfying the
matrix. -/
theorem qsatWins_leaf_iff {D τ : A → Prop} (hD : ∀ x : A, IsQVar x → D x) :
    QsatWins D τ ↔ QsatMatrix τ := by
  refine ⟨fun h => ?_, fun h => .leaf hD h⟩
  cases h with
  | leaf _ hm => exact hm
  | ex hx _ _ _ => exact absurd (hD _ hx.1) hx.2.1
  | all hx _ _ => exact absurd (hD _ hx.1) hx.2.1

/-- At a position whose next variable is existential, winning is winning after
one of its two values. -/
theorem qsatWins_ex_iff (hwf : QsatWf A) {D τ : A → Prop} {x : A} (hx : QLeast D x)
    (hq : ¬IsQAll x) :
    QsatWins D τ ↔ ∃ b : Bool, QsatWins (qAdd D x) (qUpd τ x b) := by
  refine ⟨fun h => ?_, fun ⟨b, hb⟩ => .ex hx hq b hb⟩
  cases h with
  | leaf hD _ => exact absurd (hD _ hx.1) hx.2.1
  | ex hy _ b hb => exact ⟨b, (hy.unique hwf hx) ▸ hb⟩
  | all hy hq' _ => exact absurd ((hy.unique hwf hx) ▸ hq') hq

/-- At a position whose next variable is universal, winning is winning after
both of its values. -/
theorem qsatWins_all_iff (hwf : QsatWf A) {D τ : A → Prop} {x : A} (hx : QLeast D x)
    (hq : IsQAll x) :
    QsatWins D τ ↔ ∀ b : Bool, QsatWins (qAdd D x) (qUpd τ x b) := by
  refine ⟨fun h => ?_, fun h => .all hx hq h⟩
  cases h with
  | leaf hD _ => exact absurd (hD _ hx.1) hx.2.1
  | ex hy hq' _ _ => exact absurd hq ((hy.unique hwf hx) ▸ hq')
  | all hy _ h => exact (hy.unique hwf hx) ▸ h

end Game

/-! ### Isomorphism-invariance -/

section Iso

variable {A B : Type} [Language.qsat.Structure A] [Language.qsat.Structure B]

/-- The push-forward of a predicate along an isomorphism. -/
private def pushQ (e : A ≃[Language.qsat] B) (ν : A → Prop) : B → Prop :=
  fun b => ν (e.symm b)

private theorem pushQ_apply (e : A ≃[Language.qsat] B) (ν : A → Prop) (a : A) :
    pushQ e ν (e a) ↔ ν a :=
  iff_of_eq (congrArg ν (e.symm_apply_apply a))

private theorem pushQ_qAdd (e : A ≃[Language.qsat] B) (D : A → Prop) (x : A) :
    pushQ e (qAdd D x) = qAdd (pushQ e D) (e x) := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · exact Or.inl ((e.toEquiv.symm_apply_eq).mp h)
    · exact Or.inr h
  · rcases h with h | h
    · exact Or.inl ((e.toEquiv.symm_apply_eq).mpr h)
    · exact Or.inr h

private theorem pushQ_qUpd (e : A ≃[Language.qsat] B) (τ : A → Prop) (x : A) (b : Bool) :
    pushQ e (qUpd τ x b) = qUpd (pushQ e τ) (e x) b := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨he, hb⟩ | ⟨hne, hy⟩
    · exact Or.inl ⟨(e.toEquiv.symm_apply_eq).mp he, hb⟩
    · exact Or.inr ⟨fun hy' => hne ((e.toEquiv.symm_apply_eq).mpr hy'), hy⟩
  · rcases h with ⟨he, hb⟩ | ⟨hne, hy⟩
    · exact Or.inl ⟨(e.toEquiv.symm_apply_eq).mpr he, hb⟩
    · exact Or.inr ⟨fun hy' => hne ((e.toEquiv.symm_apply_eq).mp hy'), hy⟩

private theorem isQVar_push (e : A ≃[Language.qsat] B) (x : A) :
    IsQVar (e x) ↔ IsQVar x :=
  (relMap_equiv₁ e qsIsVar x).symm

private theorem isQAll_push (e : A ≃[Language.qsat] B) (x : A) :
    IsQAll (e x) ↔ IsQAll x :=
  (relMap_equiv₁ e qsAllVar x).symm

private theorem qPrec_push (e : A ≃[Language.qsat] B) (x y : A) :
    QPrec (e x) (e y) ↔ QPrec x y :=
  (relMap_equiv₂ e qsPrefixLt x y).symm

private theorem qsatMatrix_push (e : A ≃[Language.qsat] B) {τ : A → Prop}
    (h : QsatMatrix τ) : QsatMatrix (pushQ e τ) := by
  intro c hc
  obtain ⟨x, hvar, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm qsIsClause c).mp hc)
  refine ⟨e x, (isQVar_push e x).mpr hvar, ?_⟩
  rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
  · refine Or.inl ⟨?_, (pushQ_apply e τ x).mpr hv⟩
    simpa using (relMap_equiv₂ e qsPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, fun hv' => hv ((pushQ_apply e τ x).mp hv')⟩
    simpa using (relMap_equiv₂ e qsNegIn (e.symm c) x).mp hn

private theorem qLeast_push (e : A ≃[Language.qsat] B) {D : A → Prop} {x : A}
    (h : QLeast D x) : QLeast (pushQ e D) (e x) := by
  refine ⟨(isQVar_push e x).mpr h.1, fun hd => h.2.1 ((pushQ_apply e D x).mp hd), ?_⟩
  intro y hy hd hlt
  refine h.2.2 (e.symm y) ((isQVar_push e (e.symm y)).mp (by rwa [e.apply_symm_apply])) hd ?_
  have := (qPrec_push e (e.symm y) x).mp (by rwa [e.apply_symm_apply])
  exact this

private theorem qsatWins_push (e : A ≃[Language.qsat] B) {D τ : A → Prop}
    (h : QsatWins D τ) : QsatWins (pushQ e D) (pushQ e τ) := by
  induction h with
  | leaf hD hm =>
    refine .leaf (fun y hy => ?_) (qsatMatrix_push e hm)
    have := hD (e.symm y) ((isQVar_push e (e.symm y)).mp (by rwa [e.apply_symm_apply]))
    exact this
  | ex hx hq b _ ih =>
    refine .ex (qLeast_push e hx) (fun hq' => hq ((isQAll_push e _).mp hq')) b ?_
    rwa [pushQ_qAdd, pushQ_qUpd] at ih
  | all hx hq _ ih =>
    refine .all (qLeast_push e hx) ((isQAll_push e _).mpr hq) (fun b => ?_)
    have := ih b
    rwa [pushQ_qAdd, pushQ_qUpd] at this

private theorem isQVar_symm (e : A ≃[Language.qsat] B) (x : B) :
    IsQVar x ↔ IsQVar (e.symm x) := by
  rw [← isQVar_push e (e.symm x), e.apply_symm_apply]

private theorem qPrec_symm (e : A ≃[Language.qsat] B) (x y : B) :
    QPrec x y ↔ QPrec (e.symm x) (e.symm y) := by
  rw [← qPrec_push e (e.symm x) (e.symm y), e.apply_symm_apply, e.apply_symm_apply]

private theorem qsatWf_push (e : A ≃[Language.qsat] B) (h : QsatWf A) : QsatWf B where
  isVar_of_prec x y hxy :=
    let ⟨h1, h2⟩ := h.isVar_of_prec _ _ ((qPrec_symm e x y).mp hxy)
    ⟨(isQVar_symm e x).mpr h1, (isQVar_symm e y).mpr h2⟩
  irrefl x hx := h.irrefl (e.symm x) ((qPrec_symm e x x).mp hx)
  trans x y z hxy hyz := (qPrec_symm e x z).mpr
    (h.trans _ (e.symm y) _ ((qPrec_symm e x y).mp hxy) ((qPrec_symm e y z).mp hyz))
  total x y hx hy hne := by
    refine (h.total (e.symm x) (e.symm y) ((isQVar_symm e x).mp hx) ((isQVar_symm e y).mp hy)
      (fun hh => hne ?_)).imp (qPrec_symm e x y).mpr (qPrec_symm e y x).mpr
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, hh]

end Iso

/-! ### The decision problem -/

section Problem

variable {A : Type} [Language.qsat.Structure A]

variable (A) in
/-- **The yes-instances of QSAT**: a well-formed instance whose quantified
formula is true, i.e. whose initial position – nothing quantified yet, the
empty valuation – is won by the existential player. -/
def QsatHolds : Prop :=
  QsatWf A ∧ QsatWins (fun _ : A => False) (fun _ : A => False)

private theorem qsatHolds_of_iso {B : Type} [Language.qsat.Structure B]
    (e : A ≃[Language.qsat] B) (h : QsatHolds A) : QsatHolds B := by
  obtain ⟨hwf, hw⟩ := h
  refine ⟨qsatWf_push e hwf, ?_⟩
  have := qsatWins_push e hw
  have hD : pushQ e (fun _ : A => False) = (fun _ : B => False) := rfl
  rwa [hD] at this

end Problem

/-- **QSAT**, as a problem on `FirstOrder.Language.qsat`-structures: is the fully
quantified Boolean formula described by the instance true? -/
def QSAT : DecisionProblem Language.qsat where
  Holds := fun A inst => @QsatHolds A inst
  iso_invariant := fun e => ⟨qsatHolds_of_iso e, qsatHolds_of_iso e.symm⟩

end DescriptiveComplexity
