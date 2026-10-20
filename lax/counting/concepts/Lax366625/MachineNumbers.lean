import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Lax904597.Machines
import Lax535992.DeterministicMachines
import Lax366625.CountingProblems

/-!
---
title: The number written by a deterministic Turing machine
type: definition
---
An instance is a machine instance of the NP core, extended by two marks: the
output cells of the tape, and the symbols read as the digit $1$. The output
cells are ordered by the order of the tape, and the rank of an output cell
is the number of output cells before it. If the instance describes a
well-formed deterministic machine, the number it writes is
$\sum 2^{r(p)}$ over the output cells $p$ holding a symbol read as $1$ in
the configuration where the machine halts in an accepting state, $r(p)$
being the rank of $p$; otherwise it is $0$. The machine halts in a
configuration when that configuration is reached from an initial one within
the bound of the instance and no step leaves it.
-/

namespace Lax366625.MachineNumbers

open Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tapeOutRel : ℕ → Type where
/-- `out p`: the cell `p` is an output cell, holding one digit. -/
  | out : tapeOutRel 1
/-- `one a`: the symbol `a` is read as the digit `1`. -/
  | one : tapeOutRel 1
  deriving DecidableEq

/-- The symbols reading a number off the tape of a machine. -/
def tapeOut : FirstOrder.Language :=
  ⟨fun _ => Empty, tapeOutRel⟩

instance instIsRelationalTapeOut : FirstOrder.Language.IsRelational tapeOut := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `out p`: the cell `p` is an output cell, holding one digit. -/
abbrev tpOut : tapeOut.Relations 1 :=
  .out

/-- `one a`: the symbol `a` is read as the digit `1`. -/
abbrev tpOne : tapeOut.Relations 1 :=
  .one

/-- The relational language of machines writing a number. -/
abbrev turingOut : Language.{0, 0} := turing.sum tapeOut

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : TMData A)

/-- **The machine halts in the configuration `c`**: `c` is reached from an
initial configuration within the clock, and no step is possible from it. -/
def Halts (c : Config A) : Prop :=
  ∃ (c₀ : Config A) (n : ℕ), M.IsInit c₀ ∧ n < Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ ∀ e, ¬M.Step c e

end TMData

/-- “Is an output cell”, in the vocabulary of machines writing a number. -/
abbrev mnOut : turingOut.Relations 1 := Sum.inr tpOut

/-- “Is read as the digit `1`”, in the vocabulary of machines writing a
number. -/
abbrev mnOne : turingOut.Relations 1 := Sum.inr tpOne

/-- The order of the tape, in the vocabulary of machines writing a number. -/
abbrev mnLe : turingOut.Relations 2 := Sum.inl tmLe

/-- A machine writing a number is a machine. -/
instance turingOutStructure (A : Type) [turingOut.Structure A] :
    turing.Structure A :=
  (LHom.sumInl : turing →ᴸ turingOut).reduct A

section Semantics

variable {A : Type} [turingOut.Structure A]

/-- The output cell `p` holds the digit `1` when the machine halts, in an
accepting state. -/
def OutDigit (p : A) : Prop :=
  RelMap mnOut ![p] ∧ ∃ c : Config A, TMData.Halts (tmData A) c ∧ (tmData A).Acc c.state ∧
    RelMap mnOne ![c.tape p]

/-- `q` is an output cell strictly before `p` on the tape. -/
def LowerCell (p q : A) : Prop :=
  RelMap mnOut ![q] ∧ q ≠ p ∧ RelMap mnLe ![q, p]

/-- The rank of a cell among the output cells: the number of output cells
strictly before it on the tape. -/
noncomputable def cellRank (p : A) : ℕ :=
  Nat.card {q : A // LowerCell p q}

variable (A) in
open Classical in
/-- **The number written by a machine**: each output cell holding the digit
`1` when the machine halts and accepts contributes two to the power of its
rank among the output cells. Instances that are not well-formed deterministic
machines write `0`. -/
noncomputable def machineNumber : ℕ :=
  if (tmData A).WellFormed ∧ Lax535992.DeterministicMachines.TMData.Deterministic (tmData A) then
    ∑ᶠ p : A, if OutDigit p then 2 ^ cellRank p else 0
  else 0

end Semantics

open Lax366625.CountingProblems

/-- **The number written by a deterministic machine**, as a counting problem. -/
noncomputable def DTMNumber : CountingProblem turingOut :=
  CountingProblem.ofFun fun A _ => machineNumber A

end Lax366625.MachineNumbers
