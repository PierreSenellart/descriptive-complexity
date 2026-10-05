import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax904597.Sat
import Lax485149.Problems

/-!
---
title: Satisfiability of CNF formulas of width two
type: definition
---
An instance is a CNF instance of the NP core: a structure whose elements
are clauses and variables, with the positive and negative occurrences of
variables in clauses. A literal occurrence of a clause $c$ is a pair $(x, s)$
of a variable and a sign such that $x$ occurs in $c$ with sign $s$. The
instance has width at most two when no clause has three distinct literal
occurrences, and it is a yes-instance of 2SAT when it has width at most two
and is satisfiable. 2SAT is the decision problem of the structures
isomorphic to such an instance. Instances of larger width are no-instances:
the width bound is part of the problem, not a promise.
-/

namespace Lax485149.TwoSat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax485149.Problems

namespace SatOcc

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

end SatOcc

/-- Every clause has at most two literal occurrences: among any three
occurrences of a clause, two coincide (as signed occurrences). -/
def WidthAtMostTwo (A : Type) [sat.Structure A] : Prop :=
  ∀ (c : A) (x : Fin 3 → A) (s : Fin 3 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

/-- A CNF instance is a yes-instance of 2SAT if every clause has at most two
literal occurrences and the CNF is satisfiable. -/
def TwoSatisfiable (A : Type) [sat.Structure A] : Prop :=
  WidthAtMostTwo A ∧ Satisfiable A

/-- 2SAT: is the CNF instance of width at most two and satisfiable? -/
def TwoSAT : DecisionProblem sat := DecisionProblem.ofPred fun A _ => TwoSatisfiable A

end Lax485149.TwoSat
