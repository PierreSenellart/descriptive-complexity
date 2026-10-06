import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: QSAT, quantified Boolean formulas
type: definition
---
An instance is a fully quantified Boolean formula given as a structure: its
elements are variables and clauses, with the positive and negative
occurrences of variables in clauses as for CNF instances, a mark on the
quantified variables, a mark on those quantified universally, and a binary
relation ordering the variables as they appear in the quantifier prefix,
outermost first. The instance is well formed when that relation is a strict
linear order on the quantified variables. The matrix holds under a
valuation when every clause contains a true literal on a quantified
variable.

Truth is defined as a game on positions made of the set of variables
already quantified and a valuation: a position is won when every variable
is quantified and the matrix holds, when the next variable of the prefix is
existential and one of its two values leads to a won position, or when it
is universal and both values do. An instance is a yes-instance of QSAT when
it is well formed and the initial position is won; QSAT is the decision
problem of the structures isomorphic to such an instance. The number of
alternations is not bounded.
-/

namespace Lax134656.Qsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive qsatRel : ℕ → Type where
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
def qsat : FirstOrder.Language :=
  ⟨fun _ => Empty, qsatRel⟩

instance instIsRelationalQsat : FirstOrder.Language.IsRelational qsat := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isVar x`: the element `x` is a quantified propositional variable. -/
abbrev qsIsVar : qsat.Relations 1 :=
  .isVar

/-- `allVar x`: the variable `x` is quantified universally. -/
abbrev qsAllVar : qsat.Relations 1 :=
  .allVar

/-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
abbrev qsPrefixLt : qsat.Relations 2 :=
  .prefixLt

/-- `isClause c`: the element `c` is a clause of the matrix. -/
abbrev qsIsClause : qsat.Relations 1 :=
  .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev qsPosIn : qsat.Relations 2 :=
  .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev qsNegIn : qsat.Relations 2 :=
  .negIn

open FirstOrder

open Language Structure

section Reading

variable {A : Type} [qsat.Structure A]

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
exactly as for satisfiability; an occurrence on an element that the
prefix does not quantify is not a literal, so the matrix depends on `τ` only
through its values on the variables. -/
def QsatMatrix (τ : A → Prop) : Prop :=
  ∀ c : A, RelMap qsIsClause ![c] →
    ∃ x : A, IsQVar x ∧
      ((RelMap qsPosIn ![c, x] ∧ τ x) ∨ (RelMap qsNegIn ![c, x] ∧ ¬τ x))

/-- Adding a variable to the set of already-quantified ones. -/
def qAdd (D : A → Prop) (x : A) : A → Prop := fun y => y = x ∨ D y

/-- Giving the value `b` to the variable `x` in the valuation `τ`. -/
def qUpd (τ : A → Prop) (x : A) (b : Bool) : A → Prop :=
  fun y => (y = x ∧ b = true) ∨ (y ≠ x ∧ τ y)

/-- The variable `x` is the one the position `D` quantifies next: it is the
`prefixLt`-least variable that `D` does not contain. -/
def QLeast (D : A → Prop) (x : A) : Prop :=
  IsQVar x ∧ ¬D x ∧ ∀ y : A, IsQVar y → ¬D y → ¬QPrec y x

end Reading

section Game

variable {A : Type} [qsat.Structure A]

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

end Game

section Problem

variable {A : Type} [qsat.Structure A]

variable (A) in
/-- **The yes-instances of QSAT**: a well-formed instance whose quantified
formula is true, i.e., whose initial position – nothing quantified yet, the
empty valuation – is won by the existential player. -/
def QsatHolds : Prop :=
  QsatWf A ∧ QsatWins (fun _ : A => False) (fun _ : A => False)

end Problem

/-- QSAT: is the fully quantified Boolean formula described by the instance
true? -/
def QSAT : DecisionProblem qsat := DecisionProblem.ofPred fun A _ => QsatHolds A

end Lax134656.Qsat
