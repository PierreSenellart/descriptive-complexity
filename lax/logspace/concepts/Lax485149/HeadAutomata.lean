import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Relation
import Lax904597.Interpretations

/-!
---
title: Two-way multihead automata on ordered structures
type: definition
---
A two-way $k$-head automaton over a vocabulary $L$ has a finite set of
control states with an initial state and accepting states, a finite family
of tests, each a quantifier-free formula over $L \cup \{\le\}$ in the $k$
head positions, and a transition table: for each state and each outcome of
the tests, a finite list of transitions, each a new state together with one
move per head. A move leaves the head where it is, sends it to the least or
to the greatest element, to the position of another head, or to the
immediate successor or predecessor of the position of another head; the last
two are disabled at the ends of the order. There is no work tape.

On a linearly ordered $L$-structure $A$, a configuration is a state and a
$k$-tuple of elements; a step applies one of the transitions listed for the
current state and the truth values of the tests at the current positions.
The automaton accepts $A$ when a configuration in an accepting state is
reachable from an initial configuration, in the initial state with every
head on the least element. It is deterministic when every entry of its
transition table lists at most one transition.
-/

namespace Lax485149.HeadAutomata

open FirstOrder

open Language Structure

/-- What a head may do in one step: stay where it is, jump to an end of the
order, copy another head, or step to the immediate successor or predecessor of
another head. All of it is definable from the order, which is what lets a
transition become a first-order formula. -/
inductive HeadMove (k : ℕ) where
  /-- Stay on the current element. -/
  | stay : HeadMove k
  /-- Jump to the least element. -/
  | toMin : HeadMove k
  /-- Jump to the greatest element. -/
  | toMax : HeadMove k
  /-- Copy the position of head `i`. -/
  | copy (i : Fin k) : HeadMove k
  /-- Move to the immediate successor of head `i` (disabled at the greatest
  element, which is how a head runs off the end). -/
  | succ (i : Fin k) : HeadMove k
  /-- Move to the immediate predecessor of head `i` (disabled at the least
  element). -/
  | pred (i : Fin k) : HeadMove k
  deriving DecidableEq

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- The semantics of a move: where head `j` may be after it, the current heads
being `x`. -/
def Holds (mv : HeadMove k) (x : Fin k → A) (j : Fin k) (y : A) : Prop :=
  match mv with
  | .stay => y = x j
  | .toMin => ∀ b : A, y ≤ b
  | .toMax => ∀ b : A, b ≤ y
  | .copy i => y = x i
  | .succ i => x i < y ∧ ∀ a : A, ¬(x i < a ∧ a < y)
  | .pred i => y < x i ∧ ∀ a : A, ¬(y < a ∧ a < x i)

end HeadMove

/-- **A two-way `k`-head automaton over `L`-structures**: a finite control, a
finite list of quantifier-free tests of the head positions, and, per state and
per outcome of those tests, a list of possible transitions – a new state and one
move per head. No work tape: all the storage is in the `k` heads. -/
structure HeadAutomaton (L : Language.{0, 0}) (k : ℕ) where
  /-- The control states. -/
  State : Type
  /-- The control is finite: that is what makes this a machine. -/
  [stateFinite : Finite State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accept : State → Bool
  /-- What the control reads at each step, indexed by a finite type. -/
  TestIx : Type
  /-- Finitely many tests: a control that could read unboundedly many facts
  would not be a finite control. -/
  [testFinite : Finite TestIx]
  /-- The tests: what the control sees of the current head positions. -/
  test : TestIx → (L.sum Language.order).Formula (Fin k)
  /-- **The tests are quantifier-free.** The control may compare its heads and
  look at the relations holding between them, and nothing else; a quantified
  test would make the model first-order logic in disguise. -/
  test_qf : ∀ i, (test i).IsQF
  /-- The transitions available in a state, at a given outcome of the tests:
  a new state and a move for each head. Nondeterminism is the length of this
  list. -/
  trans : State → (TestIx → Bool) → List (State × (Fin k → HeadMove k))

attribute [instance] HeadAutomaton.stateFinite HeadAutomaton.testFinite

namespace HeadAutomaton

variable {L : Language.{0, 0}} {k : ℕ} (M : HeadAutomaton L k) {A : Type} [L.Structure A]
  [LinearOrder A]

/-- A configuration: a control state together with the positions of the heads. -/
abbrev Config (A : Type) : Type := M.State × (Fin k → A)

open Classical in
/-- What the control reads at a configuration: the truth values of its tests. -/
noncomputable def reading (x : Fin k → A) : M.TestIx → Bool :=
  fun i => decide ((M.test i).Realize x)

/-- One step of the automaton: some transition available at the current state
and reading leads to the new state, each head moving as it prescribes. -/
def Step (a b : M.Config A) : Prop :=
  ∃ p ∈ M.trans a.1 (M.reading a.2), p.1 = b.1 ∧ ∀ j, (p.2 j).Holds a.2 j (b.2 j)

/-- The automaton accepts the structure when an accepting state is reachable
from an initial configuration – the initial state with every head on the least
element. -/
def Accepts (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  ∃ c₀ c : M.Config A, (c₀.1 = M.start ∧ ∀ j, ∀ b : A, c₀.2 j ≤ b) ∧
    Relation.ReflTransGen M.Step c₀ c ∧ M.accept c.1 = true

/-- **The automaton is deterministic**: at most one transition per state and
reading. -/
def IsDeterministic : Prop :=
  ∀ (s : M.State) (r : M.TestIx → Bool), (M.trans s r).length ≤ 1

end HeadAutomaton

end Lax485149.HeadAutomata
