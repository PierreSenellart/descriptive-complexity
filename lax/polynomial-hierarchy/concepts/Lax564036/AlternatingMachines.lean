import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Finite
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Machines

/-!
---
title: Acceptance by alternating Turing machines with a bounded number of alternations
type: definition
---
An alternating machine instance with $k$ blocks is a machine instance of
the NP core, a finite structure describing a Turing machine with its input
and a linear order of positions bounding tape and time, together with $k$
unary marks splitting the states into blocks. The blocks alternate in
polarity, the first being existential or universal, and a state is
universal when its block is. The block structure is well formed when every
state lies in exactly one block, every transition stays in its block or
moves to the next one, and the start states lie in the first block; a run
then alternates at most $k - 1$ times.

A configuration accepts within a budget of steps when its state is
accepting, or it is existential and some successor accepts within the
remaining budget, or it is universal, has a successor, and every successor
accepts within the remaining budget. The machine accepts when the initial
configurations accept within as many steps as there are positions, some of
them if the first block is existential, all of them and at least one if it
is universal. An instance is a yes-instance of alternating machine
acceptance with $k$ blocks when the machine and its blocks are well formed
and it accepts; the problem is the decision problem of the structures
isomorphic to such an instance.
-/

namespace Lax564036.AlternatingMachines

open Lax904597.Problems Lax485149.Problems

open Lax904597.Machines

/-- An alternating Turing machine presented as relations on a universe: a
machine in the sense of `TMData`, together with marks
splitting its states into quantifier blocks. -/
structure ATMData (A : Type) extends TMData A where
  /-- `Blk j q`: the state `q` belongs to the `j`-th quantifier block. -/
  Blk : ℕ → A → Prop

/-- The polarity of the `j`-th quantifier block of a prefix starting with
polarity `start`: `true` for an existential block, `false` for a universal one.
The polarities alternate, so the parity of `j` decides. -/
def blockPol (start : Bool) (j : ℕ) : Bool :=
  if j % 2 = 0 then start else !start

/-- **Quantification with a polarity, guarded.** Existentially, the guard is
conjoined; universally it is assumed – and required to be satisfiable by
*something*: a universal player with no legal move loses rather than winning
vacuously. -/
def guardQ (pol : Bool) {α : Type} (C P : α → Prop) : Prop :=
  match pol with
  | true => ∃ a, C a ∧ P a
  | false => (∃ a, C a) ∧ ∀ a, C a → P a

namespace ATMData

variable {A : Type} (M : ATMData A)

/-- The state `q` is *universal*: it carries the mark of a block whose
polarity is universal, so the moves out of it belong to the universal
player. -/
def IsUniv (start : Bool) (q : A) : Prop := ∃ j, M.Blk j q ∧ blockPol start j = false

/-- **Alternating acceptance within a budget.** `M.AltAcc start n c` says the
configuration `c` accepts with `n` steps to spare: an accepting state accepts
outright, an existential configuration accepts when *some* successor does, and
a universal one when it has a successor and *every* successor accepts. -/
def AltAcc (start : Bool) : ℕ → Config A → Prop
  | 0, c => M.Acc c.state
  | n + 1, c => M.Acc c.state ∨
      (M.IsUniv start c.state ∧ (∃ c', M.Step c c') ∧
        ∀ c', M.Step c c' → AltAcc start n c') ∨
      (¬ M.IsUniv start c.state ∧ ∃ c', M.Step c c' ∧ AltAcc start n c')

/-- **Alternating acceptance**: an initial configuration accepts within as many
steps as there are positions – chosen by the player of block `0`, which is what
`guardQ` at the polarity `start` says: the residual freedom in the initial
configuration belongs to the same player as the first move. -/
def AltAccepts (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀)
    (fun c₀ => M.AltAcc start (Nat.card {p : A // M.Posn p} - 1) c₀)

/-- **The block structure is well formed**: every state carries exactly one of
the `k` block marks, every transition either stays in its block or moves to
the next one, and the run starts in block `0`. The second clause is what bounds
the number of alternations by `k - 1`. -/
def BlocksWellFormed (k : ℕ) : Prop :=
  (∀ q, ∃ j, j < k ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j) ∧
    (∀ τ q q' j j', M.Tr τ → M.Src τ q → M.Dst τ q' → M.Blk j q → M.Blk j' q' →
      j ≤ j' ∧ j' ≤ j + 1) ∧
    ∀ q, M.Start q → M.Blk 0 q

end ATMData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of alternating machine instances: those of machine
instances, and one unary mark per quantifier block. -/
inductive turingAltRel (k : ℕ) : ℕ → Type
  /-- A symbol of the underlying machine vocabulary. -/
  | base {n : ℕ} : turingRel n → turingAltRel k n
  /-- `blk i q`: the state `q` belongs to the `i`-th quantifier block. -/
  | blk : Fin k → turingAltRel k 1

/-- The relational vocabulary of alternating machine instances with `k`
quantifier blocks. -/
def turingAlt (k : ℕ) : Language :=
  ⟨fun _ => Empty, turingAltRel k⟩

instance instIsRelationalTuringAlt (k : ℕ) : IsRelational (turingAlt k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

variable {k : ℕ}

/-- The position symbol. -/
abbrev atmPosn : (turingAlt k).Relations 1 := .base .posn

/-- The transition symbol. -/
abbrev atmTr : (turingAlt k).Relations 1 := .base .tr

/-- The start-state symbol. -/
abbrev atmStart : (turingAlt k).Relations 1 := .base .start

/-- The accepting-state symbol. -/
abbrev atmAcc : (turingAlt k).Relations 1 := .base .acc

/-- The blank symbol. -/
abbrev atmBlank : (turingAlt k).Relations 1 := .base .blank

/-- The move-right symbol. -/
abbrev atmRight : (turingAlt k).Relations 1 := .base .right

/-- The order symbol. -/
abbrev atmLe : (turingAlt k).Relations 2 := .base .le

/-- The transition-source symbol. -/
abbrev atmSrc : (turingAlt k).Relations 2 := .base .tsrc

/-- The transition-read symbol. -/
abbrev atmRead : (turingAlt k).Relations 2 := .base .tread

/-- The transition-destination symbol. -/
abbrev atmDst : (turingAlt k).Relations 2 := .base .tdst

/-- The transition-write symbol. -/
abbrev atmWrite : (turingAlt k).Relations 2 := .base .twrite

/-- The input symbol. -/
abbrev atmInp : (turingAlt k).Relations 2 := .base .inp

/-- The mark of the `i`-th quantifier block. -/
abbrev atmBlk (i : Fin k) : (turingAlt k).Relations 1 := .blk i

open FirstOrder

open Language Structure

section Shorthands

variable {k : ℕ} {A : Type} [(turingAlt k).Structure A]

/-- Being a position. -/
def ATMPosn (a : A) : Prop := RelMap (atmPosn (k := k)) ![a]

/-- Being a transition. -/
def ATMTr (a : A) : Prop := RelMap (atmTr (k := k)) ![a]

/-- Being a start state. -/
def ATMStart (a : A) : Prop := RelMap (atmStart (k := k)) ![a]

/-- Being an accepting state. -/
def ATMAcc (a : A) : Prop := RelMap (atmAcc (k := k)) ![a]

/-- Being the blank symbol. -/
def ATMBlank (a : A) : Prop := RelMap (atmBlank (k := k)) ![a]

/-- Moving the head right. -/
def ATMRight (a : A) : Prop := RelMap (atmRight (k := k)) ![a]

/-- The order on positions. -/
def ATMLe (a b : A) : Prop := RelMap (atmLe (k := k)) ![a, b]

/-- The state a transition applies in. -/
def ATMSrc (a b : A) : Prop := RelMap (atmSrc (k := k)) ![a, b]

/-- The symbol a transition reads. -/
def ATMRead (a b : A) : Prop := RelMap (atmRead (k := k)) ![a, b]

/-- The state a transition moves to. -/
def ATMDst (a b : A) : Prop := RelMap (atmDst (k := k)) ![a, b]

/-- The symbol a transition writes. -/
def ATMWrite (a b : A) : Prop := RelMap (atmWrite (k := k)) ![a, b]

/-- The initial contents of a cell. -/
def ATMInp (a b : A) : Prop := RelMap (atmInp (k := k)) ![a, b]

/-- The block of a state, read off the marks: the marks of the vocabulary are
indexed by `Fin k`, so a block index beyond `k` marks nothing. -/
def ATMBlk (j : ℕ) (a : A) : Prop := ∃ h : j < k, RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a]

/-- The alternating machine an instance describes. -/
def atmData (k : ℕ) (A : Type) [(turingAlt k).Structure A] : ATMData A where
  Posn := ATMPosn (k := k)
  Le := ATMLe (k := k)
  Tr := ATMTr (k := k)
  Start := ATMStart (k := k)
  Acc := ATMAcc (k := k)
  Blank := ATMBlank (k := k)
  Right := ATMRight (k := k)
  Src := ATMSrc (k := k)
  Read := ATMRead (k := k)
  Dst := ATMDst (k := k)
  Write := ATMWrite (k := k)
  Inp := ATMInp (k := k)
  Blk := ATMBlk (k := k)

end Shorthands

/-- The instance describes a well-formed alternating machine, with well-formed
blocks, that accepts its input. -/
def ATMAccepts (k : ℕ) (start : Bool) (A : Type) [(turingAlt k).Structure A] : Prop :=
  (atmData k A).toTMData.WellFormed ∧ ATMData.BlocksWellFormed (atmData k A) k ∧
    ATMData.AltAccepts (atmData k A) start

/-- **Alternating machine acceptance**: does the alternating machine described
by the instance accept its input within as many steps as there are positions?
The first block is existential when `start` is `true`. -/
def ATMAccept (k : ℕ) (start : Bool) : DecisionProblem (turingAlt k) :=
  DecisionProblem.ofPred fun A _ => ATMAccepts k start A

end Lax564036.AlternatingMachines
