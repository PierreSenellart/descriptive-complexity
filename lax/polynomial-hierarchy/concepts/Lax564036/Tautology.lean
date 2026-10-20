import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Sat

/-!
---
title: Tautology of DNF formulas
type: definition
---
An instance is a structure over the vocabulary of CNF instances of the NP
core, read here as a formula in disjunctive normal form: its clauses are
terms, conjunctions of literals. It is a tautology when every assignment of
truth values to its elements satisfies all the literals of some term. TAUT
is the decision problem of the structures isomorphic to a tautology.
-/

namespace Lax564036.Tautology

open Lax904597.Problems Lax485149.Problems

open Lax904597.Sat

open FirstOrder

open Language Structure BoundedFormula

section Taut

variable (A : Type) [sat.Structure A]

/-- A CNF instance of the NP core, read as a formula in disjunctive normal form,
is a *tautology* when every assignment of truth values to its elements makes
some term true – that is, satisfies every literal of that term. (Elements that
are not variables of the formula may be assigned arbitrarily; they are harmless
since no term mentions them.) -/
def Tautology : Prop :=
  ∀ ν : A → Prop, ∃ c : A, RelMap satIsClause ![c] ∧
    ∀ x : A, (RelMap satPosIn ![c, x] → ν x) ∧ (RelMap satNegIn ![c, x] → ¬ν x)

end Taut

/-- TAUT: is the instance, read as a formula in disjunctive normal form, a
tautology? -/
def TAUT : DecisionProblem sat := DecisionProblem.ofPred fun A _ => Tautology A

end Lax564036.Tautology
