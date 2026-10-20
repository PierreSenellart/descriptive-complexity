import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Lax564036.AlternatingMachines
import Lax904597.Machines
import Lax485149.Problems

/-!
---
title: Alternating machines in bounded space
type: definition
---
An alternating Turing machine instance of the polynomial hierarchy accepts
in bounded space when an initial configuration wins the game played on its
configurations, without a bound on the number of steps; its states are split
in two by the marks, one per player. Acceptance by alternating machines in
bounded space, the problem defining APSPACE, holds of a well-formed instance
whose states are so split and which accepts in bounded space.
-/

namespace Lax480241.AlternatingSpace

open Lax564036.AlternatingMachines Lax904597.Machines

namespace ATMData

variable {A : Type} (M : ATMData A)

/-- **Winning the alternating game**, with no bound on the length of a play: an
accepting state wins; an existential configuration wins when some successor
does; a universal one wins when it has a successor and every successor wins.

Being a least fixed point, this makes an infinite play a loss for the
existential player – the standard convention, and the one the budgeted
`ATMData.AltAcc` already has. -/
inductive AltWin (start : Bool) : Config A → Prop
  /-- An accepting state wins outright. -/
  | acc {c : Config A} : M.Acc c.state → AltWin start c
  /-- An existential configuration wins when some successor does. -/
  | ex {c c' : Config A} : ¬M.IsUniv start c.state → M.Step c c' → AltWin start c' →
      AltWin start c
  /-- A universal configuration wins when it has a successor and every
  successor wins. -/
  | all {c : Config A} : M.IsUniv start c.state → (∃ c', M.Step c c') →
      (∀ c', M.Step c c' → AltWin start c') → AltWin start c

/-- **Acceptance in bounded space**: an initial configuration wins, the choice
of that configuration belonging to the player who moves first – exactly as in
`ATMData.AltAccepts`, and for the same reason. -/
def AltAcceptsSpace (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀) (fun c₀ => ATMData.AltWin M start c₀)

variable {M}

variable (M)

/-- **The marks split the states in two.** This is all the block discipline an
unbounded alternation needs: no state carries a mark above `1`, and every state
carries exactly one of the two. `ATMData.BlocksWellFormed`
is deliberately *not* required – its ordering clause is what bounds the number
of alternations. -/
def BlocksSplit : Prop :=
  (∀ q, ∃ j, j < 2 ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j)

end ATMData

open Lax904597.Problems Lax485149.Problems

/-- **Alternating acceptance in bounded space**: the instance is a well-formed
alternating machine whose states the marks split in two, and it accepts in
bounded space. -/
def ATMAcceptSpace : DecisionProblem (turingAlt 2) :=
  DecisionProblem.ofPred fun A _ => TMData.WellFormed (atmData 2 A).toTMData ∧
    ATMData.BlocksSplit (atmData 2 A) ∧ ATMData.AltAcceptsSpace (atmData 2 A) true

end Lax480241.AlternatingSpace
