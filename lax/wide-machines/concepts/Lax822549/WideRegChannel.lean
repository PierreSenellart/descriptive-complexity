import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Lax822549.WideMachines
import Lax904597.Machines
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: Wide machines with a regular input channel
type: definition
---
The wide machine with a regular channel reads its input from a channel laid
out along the addresses: a cell reads an element of the instance when it
lies on the segment of the cells carrying an input. Wide acceptance with a
regular channel holds of a well-formed instance whose machine, so reading
its input, accepts within its $2^n$ steps.
-/

namespace Lax822549.WideRegChannel

open Lax822549.WideMachines Lax904597.Machines

open FirstOrder

open Language Structure

section Machine

variable {A : Type} [wide.Structure A]

/-- The initial tape of the register channel: the cell of `x` holds the input
symbol of `x`. -/
def wpInpReg : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMRegSeg s x ∧ WMInp x y
  | _, _ => False

variable (A) in
/-- **The wide machine an instance describes, at the register channel**: the
machine of `wideData` with its input written on the file
of the elements that carry input, instead of on the ruler of all the segments.
Every other field is the same one. -/
def wideRegData : TMData (WPoint A) :=
  { wideData A with Inp := wpInpReg }

end Machine

open Lax904597.Problems Lax485149.Problems

/-- **Wide acceptance with a regular channel.** -/
def WideRegAccept : DecisionProblem wide :=
  DecisionProblem.ofPred fun A _ => TMData.WellFormed (wideRegData A) ∧ TMData.Accepts (wideRegData A)

end Lax822549.WideRegChannel
