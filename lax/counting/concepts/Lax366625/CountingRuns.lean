import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Prod
import Lax366625.MachineNumbers
import Lax904597.Machines
import Lax366625.CountingProblems
import Lax904597.SecondOrder

/-!
---
title: Counting the accepting runs of a Turing machine
type: definition
---
On a machine instance of the NP core, a walk lays a run out along the
positions: a configuration for each position, initial at the least one,
related to the next one by a step, or kept unchanged in an accepting state,
and accepting at the greatest. A halting walk moreover repeats an accepting
configuration once it has reached one, and carries the initial configuration
at the elements that are not positions, so that every run reaching an
accepting state within the bound has exactly one halting walk. Counting
accepting runs is the number of halting walks of a well-formed instance, and
$0$ for an ill-formed one.
-/

namespace Lax366625.CountingRuns

open Lax366625.MachineNumbers Lax904597.Machines

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : TMData A)

/-- **A run laid out along the positions**: a configuration for each position,
initial at the lowest, related by a step – or by a stutter in an accepting
state, for a machine that has already accepted – at each immediate successor,
and accepting at the highest. -/
def IsWalk (conf : A → Config A) : Prop :=
  (∀ p, MinPos M.Le M.Posn p → M.IsInit (conf p)) ∧
    (∀ p q, SuccPos M.Le M.Posn p q →
      M.Step (conf p) (conf q) ∨ (M.Acc (conf p).state ∧ conf q = conf p)) ∧
    ∀ p, MaxPos M.Le M.Posn p → M.Acc (conf p).state


/-- **A halting walk**: a walk that repeats an accepting configuration once it
has reached one, and carries the initial configuration at the times that are
not positions. A run from an initial configuration to the first accepting one,
within the budget, has exactly one such layout. -/
def IsHaltWalk (conf : A → Config A) : Prop :=
  TMData.IsWalk M conf ∧
    (∀ p q, SuccPos M.Le M.Posn p q → M.Acc (conf p).state → conf q = conf p) ∧
    ∀ t p₀, ¬ M.Posn t → MinPos M.Le M.Posn p₀ → conf t = conf p₀

end TMData

open Lax366625.CountingProblems

/-- **Counting accepting runs**: the number of halting walks of the machine
described by the instance, an ill-formed instance having none. -/
noncomputable def SharpNTMAccept : CountingProblem turing :=
  CountingProblem.ofFun fun A _ => 
    Nat.card {conf : A → Config A // (tmData A).WellFormed ∧ TMData.IsHaltWalk (tmData A) conf}

end Lax366625.CountingRuns
