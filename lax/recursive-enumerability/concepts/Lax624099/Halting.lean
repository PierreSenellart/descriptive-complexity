import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Lax904597.Machines
import Lax904597.Problems
import Lax624099.Problems

/-!
---
title: The halting problem on machines of the NP core
type: definition
---
The halting problem reads the machine data of the NP core, a finite
structure describing a nondeterministic Turing machine with its input and
its positions, without any bound. The tape is an unbounded strip of pages,
each a copy of the positions, so that a cell is a page number and a
position, and every cell has a next one; a configuration is a state, the cell
under the head and the symbol in every cell; the machine accepts when some
run from an initial configuration, with the input on page zero and blanks
elsewhere, reaches an accepting state in any number of steps. A machine
instance is a yes-instance of HALT when it is well-formed and accepts its
input in this unbounded sense; HALT is the decision problem of the
structures isomorphic to such an instance.
-/

namespace Lax624099.Halting

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Machines Lax624099.Problems

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

/-- A configuration of a machine on an unbounded tape: the current state, the
cell the head is on, and the contents of every cell. A cell is a pair of a
*page* – an integer – and a position of the instance. -/
@[ext]
structure ConfigU (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : ℤ × A
  /-- The symbol in each cell. -/
  tape : ℤ × A → A

namespace TMData

variable {A : Type} (M : TMData A)

/-- **The next cell**: one step along the order of the positions inside a page,
or the step from the last position of a page to the first position of the next
page. Since the pages are indexed by `ℤ`, every cell has a next one and a
previous one, on a well-formed machine with at least one position. -/
def SuccCell (c c' : ℤ × A) : Prop :=
  (c'.1 = c.1 ∧ SuccPos M.Le M.Posn c.2 c'.2) ∨
    (c'.1 = c.1 + 1 ∧ MaxPos M.Le M.Posn c.2 ∧ MinPos M.Le M.Posn c'.2)

/-- Being an initial configuration on an unbounded tape: a start state, the
head on the lowest position of page `0`, the input on page `0` and blanks
everywhere else. -/
def IsInitU (c : ConfigU A) : Prop :=
  M.Start c.state ∧ c.head.1 = 0 ∧ MinPos M.Le M.Posn c.head.2 ∧
    ∀ z p, M.Posn p →
      (z = 0 → M.InitTape p (c.tape (z, p))) ∧ (z ≠ 0 → M.Blank (c.tape (z, p)))

/-- **One step on an unbounded tape**: the clauses of
`DescriptiveComplexity.TMData.Step`, with `DescriptiveComplexity.TMData.SuccCell`
in place of `DescriptiveComplexity.SuccPos` for the move. -/
def StepU (c c' : ConfigU A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ x, x ≠ c.head → c'.tape x = c.tape x) ∧
    ((M.Right τ ∧ SuccCell M c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccCell M c'.head c.head))

/-- Reaching one configuration from another in exactly `n` steps. -/
def StepsInU : ℕ → ConfigU A → ConfigU A → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, StepU M c d ∧ StepsInU n d c'

/-- **Acceptance on an unbounded tape**: some run from an initial configuration
reaches an accepting state, in any number of steps whatever.

This is `DescriptiveComplexity.TMData.Accepts` with the step bound dropped and
`DescriptiveComplexity.TMData.AcceptsSpace` with the space bound dropped: the
same `∃ n`, with nothing bounding it and nothing bounding the tape. A run is
still a finite object, so acceptance is an unbounded search over finite
witnesses – the shape of `∃SO[new]`, and the reason the halting problem is in
RE and in nothing smaller. -/
def AcceptsU : Prop :=
  ∃ (c₀ c : ConfigU A) (n : ℕ), IsInitU M c₀ ∧ StepsInU M n c₀ c ∧ M.Acc c.state

end TMData

/-- The machine described by the instance is well-formed and accepts its
input on an unbounded tape. -/
def HaltsOn (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.AcceptsU (tmData A)

/-- HALT: does the machine described by the instance accept its input, in any
number of steps and with as much tape as it likes? -/
def HALT : DecisionProblem turing :=
  DecisionProblem.ofPred HaltsOn

end Lax624099.Halting
