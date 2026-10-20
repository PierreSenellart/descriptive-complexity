import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Lax904597.Machines
import Lax904597.Problems
import Lax485149.Problems
import Lax134656.SpaceBoundedMachines
import Lax535992.DeterministicMachines

/-!
---
title: Wide machines
type: definition
---
A wide machine is a Turing machine whose control is an ordinary part of its
instance and whose tape is addressed by the subsets of the instance: its
points are the subsets of the universe and its elements, the subsets being
the tape cells and the time steps, ordered as binary numbers. An instance of
size $n$ thus describes a machine with $2^n$ cells and $2^n$ steps. Wide
acceptance holds of a well-formed instance whose machine accepts within its
$2^n$ steps; wide acceptance in space holds when it accepts within its $2^n$
cells, with no bound on the number of steps, and its deterministic form when
moreover the machine is deterministic.
-/

namespace Lax822549.WideMachines

open Lax904597.Machines

open FirstOrder

open Language Structure

section Addresses

variable {α : Type}

/-- **The binary-number order on addresses**: the two subsets agree, or, at some
element where the first is out and the second in, they agree at every strictly
smaller element. Written with the strict order spelled out as
`Le y x ∧ ¬ Le x y`, which is the shape the defining sentence of the expansion
realizes to. -/
def WMSetLe (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  (∀ x, s x ↔ t x) ∨
    ∃ x, (∀ y, (Le y x ∧ ¬Le x y) → (s y ↔ t y)) ∧ ¬s x ∧ t x

/-- **The address of an element**: the initial segment it cuts, which is where
the element's input symbol is written. -/
def WMDown (Le : α → α → Prop) (s : α → Prop) (x : α) : Prop := ∀ y, s y ↔ Le y x

/-- **The cell of an element on a file**: the initial segment it cuts among the
elements the file has a register for. The wide machine's register channel and
the wide tiling's bottom row are both described at these addresses – a *file* of
cells rather than the ruler of all the segments. -/
def WMFileSeg (Le : α → α → Prop) (Has : α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∀ y, s y ↔ (Le y x ∧ Has y)

end Addresses

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide-machine instances: the control of
`FirstOrder.Language.turing`, with the positions and their order replaced by an
order on the elements – the digits of an address. -/
inductive wideRel : ℕ → Type
  /-- `wmLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wideRel 2
  /-- `wmTr τ`: `τ` is a transition. -/
  | tr : wideRel 1
  /-- `wmStart q`: `q` is a start state. -/
  | start : wideRel 1
  /-- `wmAcc q`: `q` is an accepting state. -/
  | acc : wideRel 1
  /-- `wmBlank a`: `a` is the blank symbol. -/
  | blank : wideRel 1
  /-- `wmRight τ`: the transition `τ` moves the head right. -/
  | right : wideRel 1
  /-- `wmSrc τ q`: `τ` applies in the state `q`. -/
  | src : wideRel 2
  /-- `wmRead τ a`: `τ` applies when reading the symbol `a`. -/
  | read : wideRel 2
  /-- `wmDst τ q`: `τ` moves to the state `q`. -/
  | dst : wideRel 2
  /-- `wmWrite τ a`: `τ` writes the symbol `a`. -/
  | write : wideRel 2
  /-- `wmInp x a`: the address `{y | y ≤ x}` initially holds the symbol `a`. -/
  | inp : wideRel 2
  deriving DecidableEq

/-- The relational vocabulary of wide-machine instances. -/
def wide : Language :=
  ⟨fun _ => Empty, wideRel⟩

instance instIsRelationalWide : wide.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

/-- The order on the elements of the instance. -/
abbrev wmLe : wide.Relations 2 := .wle

/-- The transition symbol. -/
abbrev wmTr : wide.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev wmStart : wide.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev wmAcc : wide.Relations 1 := .acc

/-- The blank symbol. -/
abbrev wmBlank : wide.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev wmRight : wide.Relations 1 := .right

/-- The transition-source symbol. -/
abbrev wmSrc : wide.Relations 2 := .src

/-- The transition-read symbol. -/
abbrev wmRead : wide.Relations 2 := .read

/-- The transition-destination symbol. -/
abbrev wmDst : wide.Relations 2 := .dst

/-- The transition-write symbol. -/
abbrev wmWrite : wide.Relations 2 := .write

/-- The input symbol. -/
abbrev wmInp : wide.Relations 2 := .inp

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wide.Structure A]

/-- The order on the elements of the instance. -/
def WMLe (a b : A) : Prop := RelMap wmLe ![a, b]

/-- Being a transition. -/
def WMTr (a : A) : Prop := RelMap wmTr ![a]

/-- Being a start state. -/
def WMStart (a : A) : Prop := RelMap wmStart ![a]

/-- Being an accepting state. -/
def WMAcc (a : A) : Prop := RelMap wmAcc ![a]

/-- Being the blank symbol. -/
def WMBlank (a : A) : Prop := RelMap wmBlank ![a]

/-- Moving the head right. -/
def WMRight (a : A) : Prop := RelMap wmRight ![a]

/-- The state a transition applies in. -/
def WMSrc (a b : A) : Prop := RelMap wmSrc ![a, b]

/-- The symbol a transition reads. -/
def WMRead (a b : A) : Prop := RelMap wmRead ![a, b]

/-- The state a transition moves to. -/
def WMDst (a b : A) : Prop := RelMap wmDst ![a, b]

/-- The symbol a transition writes. -/
def WMWrite (a b : A) : Prop := RelMap wmWrite ![a, b]

/-- The input at an initial-segment address. -/
def WMInp (a b : A) : Prop := RelMap wmInp ![a, b]

end Shorthands

section Machine

variable (A : Type)

/-- **The universe of a wide machine**: the addresses – the subsets of the
instance, which are its tape cells and its time steps – together with the
elements of the instance, which are its control. An `abbrev`, so that the sum
structure stays visible to `rw` and to the elaborator. -/
abbrev WPoint : Type := (A → Prop) ⊕ A

variable {A} [wide.Structure A]

/-- Being a position: the addresses are the positions, the control elements are
not. -/
def wpPosn : WPoint A → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The order on the universe: addresses first, in the binary-number order they
inherit from the instance's own order, then the control elements in that same
order. -/
def wpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WMLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WMLe x y

/-- A mark of the control, read on the universe of the machine: no address
carries it. -/
def wpMark (R : A → Prop) : WPoint A → Prop
  | Sum.inl _ => False
  | Sum.inr x => R x

/-- A binary attribute of the control, read on the universe of the machine. -/
def wpAttr (R : A → A → Prop) : WPoint A → WPoint A → Prop
  | Sum.inr x, Sum.inr y => R x y
  | _, _ => False

/-- The initial tape: the address cutting the initial segment of `x` holds the
input symbol of `x`. -/
def wpInp : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMDown WMLe s x ∧ WMInp x y
  | _, _ => False

variable (A) in
/-- **The wide machine an instance describes**: the control read off the
instance, the positions being the addresses. -/
def wideData : TMData (WPoint A) where
  Posn := wpPosn
  Le := wpLe
  Tr := wpMark WMTr
  Start := wpMark WMStart
  Acc := wpMark WMAcc
  Blank := wpMark WMBlank
  Right := wpMark WMRight
  Src := wpAttr WMSrc
  Read := wpAttr WMRead
  Dst := wpAttr WMDst
  Write := wpAttr WMWrite
  Inp := wpInp

end Machine

open FirstOrder

open Language Structure

section RegCell

variable {A : Type} [wide.Structure A]

/-- **An element the channel writes for**: one that carries an input symbol.
These are the elements the file has registers for. -/
def WMHasInp (x : A) : Prop := ∃ a : A, WMInp x a

/-- **Being the cell of an element at the register channel**, as the model reads
it off an address. -/
def WMRegSeg (s : A → Prop) (x : A) : Prop := ∀ y, s y ↔ (WMLe y x ∧ WMHasInp y)

end RegCell

open Lax904597.Problems Lax485149.Problems

/-- **Wide acceptance**: the wide machine of the instance is well formed and
accepts within its `2 ^ n` steps. -/
def WideAccept : DecisionProblem wide :=
  DecisionProblem.ofPred fun A _ => TMData.WellFormed (wideData A) ∧ TMData.Accepts (wideData A)

/-- **Wide acceptance in space**: the wide machine of the instance is well formed
and accepts within its `2 ^ n` cells. -/
def WideAcceptSpace : DecisionProblem wide :=
  DecisionProblem.ofPred fun A _ =>
    TMData.WellFormed (wideData A) ∧ Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A)

/-- **Deterministic wide acceptance in space**: the wide machine is moreover
deterministic. -/
def DWideAcceptSpace : DecisionProblem wide :=
  DecisionProblem.ofPred fun A _ =>
    TMData.WellFormed (wideData A) ∧ Lax535992.DeterministicMachines.TMData.Deterministic (wideData A) ∧
      Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A)

end Lax822549.WideMachines
