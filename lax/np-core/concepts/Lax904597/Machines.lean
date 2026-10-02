import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Finite
import Lax904597.Problems

/-!
---
title: Nondeterministic Turing machines as finite structures
type: definition
---
A nondeterministic Turing machine, together with its input, is presented as
a finite structure: the universe holds the positions, the transitions, the
states and the symbols, and relations record the order on positions, the
attributes of each transition (the state it applies in, the symbol it
reads, the state it moves to, the symbol it writes, the direction of the
move), the start and accepting states, the blank symbol, and the input
written on the tape.

Positions serve both as tape cells and as time steps, so the time bound is
the number of positions, by construction and with no arithmetic. A
configuration is a state, a head position and a tape; a step applies a
transition at the head, and the machine *accepts* when some run from an
initial configuration reaches an accepting state in fewer steps than there
are positions. Well-formedness – the order is linear, there is a position,
the input is functional and the blank symbol is unique – is folded into the
yes-instances, since a relation symbol is not a linear order by itself.

Machine acceptance, the decision problem so defined, is the machine side of
the Cook–Levin theorem. That it is isomorphism-invariant, which makes it a
decision problem, is the one claim of this module: the proof transports runs
along the isomorphism and belongs to the proofs of this submission, so the
bundled problem takes the invariance proof as a parameter. By proof
irrelevance the problem
does not depend on which proof is supplied, and every statement about it is
made for an arbitrary one.
-/

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A configuration: the current state, the position of the head, and the
contents of the tape. -/
@[ext]
structure Config (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : A
  /-- The symbol in each cell. -/
  tape : A → A

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Being an initial configuration: a start state, the head on the lowest
position, and an initial tape. -/
def IsInit (c : Config A) : Prop :=
  M.Start c.state ∧ MinPos M.Le M.Posn c.head ∧ ∀ p, M.InitTape p (c.tape p)

/-- One step: some transition applies in the current state to the symbol under
the head; it writes in that cell, changes state, and moves the head to the
neighboring position in the direction it names. Other cells are unchanged,
and a move off the end of the tape is impossible, so the run stops there. -/
def Step (c c' : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

/-- Reaching one configuration from another in exactly `n` steps. -/
def StepsIn : ℕ → Config A → Config A → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, M.Step c d ∧ StepsIn n d c'

/-- Acceptance: some run from an initial configuration reaches an accepting
state in fewer steps than there are positions. -/
def Accepts : Prop :=
  ∃ (c₀ c : Config A) (n : ℕ), M.IsInit c₀ ∧ n < Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ M.Acc c.state

/-- Well-formedness: the order is linear, there is a position to start on, the
input is functional, and there is exactly one blank symbol. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

instance instIsRelationalTuring : IsRelational turing := fun _ => (inferInstance : IsEmpty Empty)

/-- The position symbol. -/
abbrev tmPosn : turing.Relations 1 := .posn
/-- The transition symbol. -/
abbrev tmTr : turing.Relations 1 := .tr
/-- The start-state symbol. -/
abbrev tmStart : turing.Relations 1 := .start
/-- The accepting-state symbol. -/
abbrev tmAcc : turing.Relations 1 := .acc
/-- The blank symbol. -/
abbrev tmBlank : turing.Relations 1 := .blank
/-- The move-right symbol. -/
abbrev tmRight : turing.Relations 1 := .right
/-- The order symbol. -/
abbrev tmLe : turing.Relations 2 := .le
/-- The transition-source symbol. -/
abbrev tmSrc : turing.Relations 2 := .tsrc
/-- The transition-read symbol. -/
abbrev tmRead : turing.Relations 2 := .tread
/-- The transition-destination symbol. -/
abbrev tmDst : turing.Relations 2 := .tdst
/-- The transition-write symbol. -/
abbrev tmWrite : turing.Relations 2 := .twrite
/-- The input symbol. -/
abbrev tmInp : turing.Relations 2 := .inp

section Shorthands

variable [turing.Structure A]

/-- Being a position. -/
def TMPosn (a : A) : Prop := RelMap tmPosn ![a]
/-- Being a transition. -/
def TMTr (a : A) : Prop := RelMap tmTr ![a]
/-- Being a start state. -/
def TMStart (a : A) : Prop := RelMap tmStart ![a]
/-- Being an accepting state. -/
def TMAcc (a : A) : Prop := RelMap tmAcc ![a]
/-- Being the blank symbol. -/
def TMBlank (a : A) : Prop := RelMap tmBlank ![a]
/-- Moving the head right. -/
def TMRight (a : A) : Prop := RelMap tmRight ![a]
/-- The order on positions. -/
def TMLe (a b : A) : Prop := RelMap tmLe ![a, b]
/-- The state a transition applies in. -/
def TMSrc (a b : A) : Prop := RelMap tmSrc ![a, b]
/-- The symbol a transition reads. -/
def TMRead (a b : A) : Prop := RelMap tmRead ![a, b]
/-- The state a transition moves to. -/
def TMDst (a b : A) : Prop := RelMap tmDst ![a, b]
/-- The symbol a transition writes. -/
def TMWrite (a b : A) : Prop := RelMap tmWrite ![a, b]
/-- The initial contents of a cell. -/
def TMInp (a b : A) : Prop := RelMap tmInp ![a, b]

end Shorthands

/-- The machine an instance describes. -/
def tmData (A : Type) [turing.Structure A] : TMData A where
  Posn := TMPosn
  Le := TMLe
  Tr := TMTr
  Start := TMStart
  Acc := TMAcc
  Blank := TMBlank
  Right := TMRight
  Src := TMSrc
  Read := TMRead
  Dst := TMDst
  Write := TMWrite
  Inp := TMInp

/-- Well-formed acceptance is isomorphism-invariant: the statement. -/
def NTMAcceptInvariant : Prop :=
  ∀ {A B : Type} [turing.Structure A] [turing.Structure B], (A ≃[turing] B) →
    (((tmData A).WellFormed ∧ (tmData A).Accepts) ↔ ((tmData B).WellFormed ∧ (tmData B).Accepts))

/-- Well-formed acceptance is isomorphism-invariant: an isomorphism of
instances transports every symbol, hence runs and their acceptance. -/
axiom ntmAccept_iso : NTMAcceptInvariant

/-- Machine acceptance: does the well-formed machine described by the instance
accept its input in fewer steps than there are positions? Bundled with any
proof `h` of its invariance, `ntmAccept_iso` for one; the problem does not
depend on `h`. -/
def NTMAccept (h : NTMAcceptInvariant) : DecisionProblem turing where
  Holds := fun A _ => (tmData A).WellFormed ∧ (tmData A).Accepts
  iso_invariant := h

end Lax904597.Machines
