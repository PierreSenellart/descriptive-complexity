import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Sat
import Lax799700.ThreeSat
import Lax564036.Tautology

/-!
---
title: Tautology of 3-DNF formulas and unsatisfiability of 3-CNF formulas
type: definition
---
Over the vocabulary of CNF instances, an instance has width at most three
when no clause has four distinct literal occurrences. It is a yes-instance
of 3-DNF-TAUT when it has width at most three and, read as a formula in
disjunctive normal form, is a tautology; it is a yes-instance of 3-UNSAT
when it has width at most three and, read as a formula in conjunctive normal
form, is unsatisfiable. Each problem is the decision problem of the
structures isomorphic to such an instance. The width bound is part of both
problems, so 3-UNSAT is not the complement of 3SAT, which wide instances
also satisfy.
-/

namespace Lax564036.ThreeDnfTautology

open Lax904597.Problems Lax485149.Problems

open Lax799700.ThreeSat Lax564036.Tautology Lax904597.Sat

open FirstOrder

open Language Structure

section Problems

variable (A : Type) [sat.Structure A]

/-- An instance, read as a formula in disjunctive normal form,
is a yes-instance of 3-DNF-TAUT if every term has at most three literal
occurrences and every truth assignment satisfies all the literals of some
term. -/
def ThreeDnfTautology : Prop :=
  WidthAtMostThree A ∧ Tautology A

/-- An instance, read as a formula in conjunctive normal form,
is a yes-instance of 3-UNSAT if every clause has at most three literal
occurrences and no truth assignment satisfies the formula. This is the
CNF-side reading of `ThreeDnfTautology`; it is *not* the complement of 3SAT,
which also holds of wide instances. -/
def ThreeUnsatisfiable : Prop :=
  WidthAtMostThree A ∧ ¬Satisfiable A

end Problems

/-- 3-DNF-TAUT: is the instance a DNF tautology of width at most three? -/
def ThreeDnfTAUT : DecisionProblem sat :=
  DecisionProblem.ofPred fun A _ => ThreeDnfTautology A

/-- 3-UNSAT: is the instance an unsatisfiable CNF formula of width at most
three? -/
def ThreeUNSAT : DecisionProblem sat :=
  DecisionProblem.ofPred fun A _ => ThreeUnsatisfiable A

end Lax564036.ThreeDnfTautology
