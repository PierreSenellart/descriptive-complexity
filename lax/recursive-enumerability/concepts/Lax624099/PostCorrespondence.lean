import Mathlib.Data.List.Forall2
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax904597.Classes
import Lax624099.Problems

/-!
---
title: Post's correspondence problem
type: definition
---
A Post correspondence system is a finite structure whose elements are
dominoes, letters and positions at once: a unary relation marks the
dominoes, two ternary relations give the letter of the top word and of the
bottom word of a domino at a position, and a binary relation is a linear
order on the positions. The top word of a domino is the sequence of its
letters at the positions it uses, in the order of the positions, and
likewise the bottom word. The system has a match when it is well-formed and
some nonempty sequence of dominoes has the same concatenation of top words
and of bottom words, the problem of Post (1946). PCP is the decision problem of the structures
isomorphic to a system with a match.
-/

namespace Lax624099.PostCorrespondence

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of Post correspondence systems. -/
inductive pcpRel : ℕ → Type
  /-- `le x y`: the order of the positions. -/
  | le : pcpRel 2
  /-- `dom d`: the element `d` is one of the dominoes. -/
  | dom : pcpRel 1
  /-- `uAt d p c`: the top word of the domino `d` has the letter `c` at the
  position `p`. -/
  | uAt : pcpRel 3
  /-- `vAt d p c`: the bottom word of the domino `d` has the letter `c` at the
  position `p`. -/
  | vAt : pcpRel 3
  deriving DecidableEq

/-- The relational vocabulary of Post correspondence systems: marked dominoes
carrying two words each, over a universe ordered by the order of the positions
of those words. -/
def pcp : Language :=
  ⟨fun _ => Empty, pcpRel⟩

instance instIsRelationalPcp : IsRelational pcp :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The order symbol of the positions. -/
abbrev pcpLeSym : pcp.Relations 2 := .le

/-- The symbol marking the dominoes. -/
abbrev pcpDomSym : pcp.Relations 1 := .dom

/-- The symbol giving the letters of the top words. -/
abbrev pcpUSym : pcp.Relations 3 := .uAt

/-- The symbol giving the letters of the bottom words. -/
abbrev pcpVSym : pcp.Relations 3 := .vAt

open FirstOrder

open Language Structure

namespace Pcp

section Reading

variable {A : Type} [pcp.Structure A]

/-- `x` precedes `y` in the order of the positions. -/
def Ord (x y : A) : Prop := RelMap pcpLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the positions. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The element `d` is one of the dominoes. -/
def DomG (d : A) : Prop := RelMap pcpDomSym ![d]

/-- The top word of the domino `d` has the letter `c` at the position `p`. -/
def UAt (d p c : A) : Prop := RelMap pcpUSym ![d, p, c]

/-- The bottom word of the domino `d` has the letter `c` at the position
`p`. -/
def VAt (d p c : A) : Prop := RelMap pcpVSym ![d, p, c]

/-- The position `p` carries a letter of the top word of the domino `d`. -/
def UsedU (d p : A) : Prop := ∃ c, UAt d p c

/-- The position `p` carries a letter of the bottom word of the domino `d`. -/
def UsedV (d p : A) : Prop := ∃ c, VAt d p c

end Reading

/-- **Well-formedness of a Post correspondence system**: the order symbol is a
linear order, and each domino carries at most one letter at each position of
each of its two words. -/
structure IsWF (A : Type) [pcp.Structure A] : Prop where
  /-- The order of the positions is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the positions is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the positions is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the positions is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- A top word has at most one letter at each position. -/
  uAt_fun : ∀ d p c c' : A, UAt d p c → UAt d p c' → c = c'
  /-- A bottom word has at most one letter at each position. -/
  vAt_fun : ∀ d p c c' : A, VAt d p c → VAt d p c' → c = c'

section Words

variable {A : Type} [pcp.Structure A]

/-- **The top word of the domino `d` is `w`**: some strictly increasing list
enumerates exactly the positions used by the top word of `d`, and `w` carries
the letters at them. -/
def IsWordU (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedU d p) ∧ List.Forall₂ (UAt d) ps w

/-- **The bottom word of the domino `d` is `w`**, as in
`DescriptiveComplexity.Pcp.IsWordU`. -/
def IsWordV (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedV d p) ∧ List.Forall₂ (VAt d) ps w

end Words

/-- **The system has a match**: the instance is well-formed and there is a
nonempty sequence of dominoes whose top words and whose bottom words have the
same concatenation. -/
def PcpOn (A : Type) [pcp.Structure A] : Prop :=
  IsWF A ∧ ∃ (l : List A) (us vs : List (List A)),
    l ≠ [] ∧ (∀ d ∈ l, DomG d) ∧
      List.Forall₂ IsWordU l us ∧ List.Forall₂ IsWordV l vs ∧ us.flatten = vs.flatten

end Pcp

open Lax904597.Problems Lax624099.Problems

/-- PCP: does the Post correspondence system have a match? -/
def PCP : DecisionProblem pcp :=
  DecisionProblem.ofPred Pcp.PcpOn

end Lax624099.PostCorrespondence
