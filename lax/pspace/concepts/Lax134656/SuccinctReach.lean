import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: SUCCINCT-REACH, reachability in a succinct transition system
type: definition
---
An instance describes a transition system succinctly. Some of its elements
are state variables, each with next-state copies given by a binary
relation, and its clauses, with positive and negative occurrences of
variables, are split into three groups: transition, source and target
clauses. A state of the system is a truth assignment to the state
variables. There is a transition from a state $S$ to a state $S'$ when some
valuation of all the variables satisfies every transition clause, agrees
with $S$ on the state variables and gives each next-state copy the value
$S'$ gives to its variable; a state is a source, respectively a target,
when some valuation agreeing with it on the state variables satisfies every
source, respectively target, clause.

An instance is a yes-instance of SUCCINCT-REACH when some target state is
reachable from some source state by a possibly empty sequence of
transitions; the problem is the decision problem of the structures
isomorphic to such an instance. The system has exponentially many states in
the size of its description.
-/

namespace Lax134656.SuccinctReach

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive transSysRel : ℕ → Type where
/-- `stateVar x`: the element `x` is a state variable. -/
  | stateVar : transSysRel 1
/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
  | next : transSysRel 2
/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
  | stepCl : transSysRel 1
/-- `srcCl c`: the element `c` is a clause of the source formula. -/
  | srcCl : transSysRel 1
/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
  | tgtCl : transSysRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : transSysRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : transSysRel 2
  deriving DecidableEq

/-- The relational vocabulary of succinctly described transition systems: the
state variables and their next-state copies, three groups of clauses, and the
two literal-occurrence predicates of CNF instances. -/
def transSys : FirstOrder.Language :=
  ⟨fun _ => Empty, transSysRel⟩

instance instIsRelationalTransSys : FirstOrder.Language.IsRelational transSys := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `stateVar x`: the element `x` is a state variable. -/
abbrev tsStateVar : transSys.Relations 1 :=
  .stateVar

/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
abbrev tsNext : transSys.Relations 2 :=
  .next

/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
abbrev tsStepCl : transSys.Relations 1 :=
  .stepCl

/-- `srcCl c`: the element `c` is a clause of the source formula. -/
abbrev tsSrcCl : transSys.Relations 1 :=
  .srcCl

/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
abbrev tsTgtCl : transSys.Relations 1 :=
  .tgtCl

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev tsPosIn : transSys.Relations 2 :=
  .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev tsNegIn : transSys.Relations 2 :=
  .negIn

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [transSys.Structure A]

/-- A valuation satisfies a group of clauses when every clause of the group
contains a literal it makes true. Elements that are not clauses of the group
impose nothing, exactly as for satisfiability. -/
def ClausesHold (ν : A → Prop) (grp : transSys.Relations 1) : Prop :=
  ∀ c : A, RelMap grp ![c] →
    ∃ x : A, (RelMap tsPosIn ![c, x] ∧ ν x) ∨ (RelMap tsNegIn ![c, x] ∧ ¬ν x)

/-- The valuation `ν` *reads* the state `S`: on every state variable it agrees
with `S`. This is the only way a clause group sees the current state. -/
def ReadsCur (ν : A → Prop) (S : A → Prop) : Prop :=
  ∀ x : A, RelMap tsStateVar ![x] → (ν x ↔ S x)

/-- The valuation `ν` *writes* the state `S'`: on the next-state copy of every
state variable it holds exactly the value `S'` gives to that variable. -/
def WritesNext (ν : A → Prop) (S' : A → Prop) : Prop :=
  ∀ x y : A, RelMap tsStateVar ![x] → RelMap tsNext ![x, y] → (ν y ↔ S' x)

/-- One transition of the system: some valuation satisfies every transition
clause while reading `S` on the state variables and writing `S'` on their
next-state copies. The valuation is existentially quantified, so the auxiliary
variables of the transition formula are free to take whatever values the
clauses need. -/
def StepRel (S S' : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsStepCl ∧ ReadsCur A ν S ∧ WritesNext A ν S'

/-- A state is a source state when some valuation reading it satisfies every
clause of the source formula. -/
def IsStart (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsSrcCl ∧ ReadsCur A ν S

/-- A state is a target state when some valuation reading it satisfies every
clause of the target formula. -/
def IsGoal (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsTgtCl ∧ ReadsCur A ν S

/-- **The yes-instances of SUCCINCT-REACH**: some target state is reachable
from some source state along the transitions described by the clauses. -/
def SuccinctReachable : Prop :=
  ∃ S S' : A → Prop, IsStart A S ∧ IsGoal A S' ∧ Relation.ReflTransGen (StepRel A) S S'

end Semantics

/-- SUCCINCT-REACH: is some target state reachable from some source state in
the succinctly described transition system? -/
def SUCCINCTREACH : DecisionProblem transSys :=
  DecisionProblem.ofPred fun A _ => SuccinctReachable A

end Lax134656.SuccinctReach
