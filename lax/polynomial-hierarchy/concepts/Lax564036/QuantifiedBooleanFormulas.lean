import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fin.Tuple.Basic
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: Quantified Boolean formulas with a bounded number of alternations
type: definition
---
An instance with $k$ quantifier blocks is a structure over the vocabulary
of CNF instances extended by $k$ unary marks, the $i$-th marking the
variables of the $i$-th block. A tuple of $k$ truth assignments, one per
block, gives a variable the value true when some block marking it assigns it
true. The matrix is read conjunctively, every clause containing a true
literal, or disjunctively, some term having all its literals true. The
assignments are quantified in the order of the blocks with alternating
quantifiers, the outermost being existential or universal.

QBF$_k$ is the problem with $k$ alternating blocks starting with an
existential one, and QBF$^\forall_k$ the problem starting with a universal
one. In both the matrix follows the innermost quantifier: conjunctive when
it is existential, disjunctive when it is universal. Each problem is the
decision problem of the structures isomorphic to a true instance.
-/

namespace Lax564036.QuantifiedBooleanFormulas

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of quantified Boolean formulas with `k`
quantifier blocks. -/
inductive qbfRel (k : ℕ) : ℕ → Type
  /-- `isClause c`: the element `c` is a clause (a term, for a disjunctive
  matrix). -/
  | isClause : qbfRel k 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qbfRel k 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qbfRel k 2
  /-- `block i x`: the variable `x` belongs to the `i`-th quantifier block. -/
  | block : Fin k → qbfRel k 1
  deriving DecidableEq

/-- The relational vocabulary of quantified Boolean formulas with `k`
quantifier blocks: that of CNF instances, together with `k` unary predicates
marking the variables of each quantifier block. -/
def qbf (k : ℕ) : Language :=
  ⟨fun _ => Empty, qbfRel k⟩

instance instIsRelationalQbf (k : ℕ) : IsRelational (qbf k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

variable {k : ℕ}

/-- The symbol for “is a clause”. -/
abbrev qbfIsClause : (qbf k).Relations 1 := .isClause

/-- The symbol for “occurs positively in”. -/
abbrev qbfPosIn : (qbf k).Relations 2 := .posIn

/-- The symbol for “occurs negatively in”. -/
abbrev qbfNegIn : (qbf k).Relations 2 := .negIn

/-- The symbol marking the variables of the `i`-th quantifier block. -/
abbrev qbfBlock (i : Fin k) : (qbf k).Relations 1 := .block i

open FirstOrder

open Language Structure

/-- Alternating quantification over `k` truth assignments on `A`: the
assignment of index `0` is quantified outermost, existentially if `pol` is
`true`, and the polarities alternate inwards. -/
def altQuant (A : Type) : ∀ (k : ℕ), ((Fin k → A → Prop) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true => ∃ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) false
  | k + 1, P, false => ∀ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) true

section Matrix

variable {k : ℕ} {A : Type} [(qbf k).Structure A]

/-- The truth value of the variable `x` under a tuple of block assignments:
`x` is true when some block marking it assigns it the value true. (In a
well-formed instance the block marks partition the variables, so exactly one
assignment is consulted.) -/
def qbfVal (νs : Fin k → A → Prop) (x : A) : Prop :=
  ∃ i : Fin k, RelMap (qbfBlock i) ![x] ∧ νs i x

/-- Conjunctive satisfaction, with the sign of every literal flipped when
`swap` is `true`: every clause then has to contain a literal that the block
assignments make *false*. -/
def CnfSatWith (swap : Bool) (νs : Fin k → A → Prop) : Prop :=
  ∀ c : A, RelMap (qbfIsClause (k := k)) ![c] →
    ∃ x : A,
      (RelMap (if swap then qbfNegIn (k := k) else qbfPosIn (k := k)) ![c, x] ∧ qbfVal νs x) ∨
      (RelMap (if swap then qbfPosIn (k := k) else qbfNegIn (k := k)) ![c, x] ∧ ¬qbfVal νs x)

/-- The conjunctive matrix: every clause contains a literal made true by the
block assignments. -/
abbrev CnfSat (νs : Fin k → A → Prop) : Prop := CnfSatWith false νs

/-- The disjunctive matrix: some term has all of its literals made true by the
block assignments. -/
def DnfSat (νs : Fin k → A → Prop) : Prop :=
  ∃ c : A, RelMap (qbfIsClause (k := k)) ![c] ∧
    ∀ x : A, (RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x) ∧
      (RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x)

/-- The matrix of a quantified Boolean formula: conjunctive when `cnf` is
`true`, disjunctive when it is `false`. -/
def QbfMatrix (cnf : Bool) (νs : Fin k → A → Prop) : Prop :=
  match cnf with
  | true => CnfSat νs
  | false => DnfSat νs

end Matrix

/-- Quantified Boolean formulas with `k` alternating quantifier blocks: the
prefix starts with an existential block when `start` is `true`, and the matrix
is conjunctive when `cnf` is `true`. -/
def QbfProblem (k : ℕ) (start cnf : Bool) : DecisionProblem (qbf k) :=
  DecisionProblem.ofPred fun A _ => altQuant A k (fun νs => QbfMatrix cnf νs) start

/-- **QBF with `k` alternating blocks**, existential first: the matrix is
conjunctive when the innermost quantifier is existential (`k` odd), disjunctive
when it is universal (`k` even). -/
def QBF (k : ℕ) : DecisionProblem (qbf k) :=
  QbfProblem k true (k % 2 == 1)

/-- The dual family, with a universal outermost block. -/
def QBFPi (k : ℕ) : DecisionProblem (qbf k) :=
  QbfProblem k false (k % 2 == 0)

end Lax564036.QuantifiedBooleanFormulas
