import Mathlib.Computability.PartrecCode
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax904597.Classes
import Lax624099.Problems

/-!
---
title: Halting of a drawn partial recursive code
type: definition
---
An instance is the syntax tree of a partial recursive code of Mathlib,
drawn with one element per node: a node carries one of the eight constructor
marks, zero, successor, left, right, pair, composition, primitive recursion
and unbounded search, its children are given by two binary relations, and
one node is marked as the root. A node decodes to a code by recursion on the
code: it carries the code's constructor mark and its children decode to the
constructor's arguments. CODEHALT is the decision problem of the structures
isomorphic to one whose root decodes to a code that halts on input zero.
-/

namespace Lax624099.CodeHalting

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of code instances. -/
inductive codeRel : ℕ → Type
  /-- `croot n`: `n` is the root of the syntax tree. -/
  | croot : codeRel 1
  /-- `czero n`: `n` draws the constructor `zero`. -/
  | czero : codeRel 1
  /-- `csucc n`: `n` draws the constructor `succ`. -/
  | csucc : codeRel 1
  /-- `cleft n`: `n` draws the constructor `left`. -/
  | cleft : codeRel 1
  /-- `cright n`: `n` draws the constructor `right`. -/
  | cright : codeRel 1
  /-- `cpair n`: `n` draws the constructor `pair`. -/
  | cpair : codeRel 1
  /-- `ccomp n`: `n` draws the constructor `comp`. -/
  | ccomp : codeRel 1
  /-- `cprec n`: `n` draws the constructor `prec`. -/
  | cprec : codeRel 1
  /-- `crfind n`: `n` draws the constructor `rfind'`. -/
  | crfind : codeRel 1
  /-- `carg1 n m`: `m` is the first child of `n`. -/
  | carg1 : codeRel 2
  /-- `carg2 n m`: `m` is the second child of `n`. -/
  | carg2 : codeRel 2
  deriving DecidableEq

/-- The relational language of code instances: the eight constructor marks,
the mark of the root, and the two child relations. -/
def code : Language :=
  ⟨fun _ => Empty, codeRel⟩

instance instIsRelationalCode : IsRelational code :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The root symbol. -/
abbrev cRoot : code.Relations 1 := .croot

/-- The `zero` symbol. -/
abbrev cZero : code.Relations 1 := .czero

/-- The `succ` symbol. -/
abbrev cSucc : code.Relations 1 := .csucc

/-- The `left` symbol. -/
abbrev cLeft : code.Relations 1 := .cleft

/-- The `right` symbol. -/
abbrev cRight : code.Relations 1 := .cright

/-- The `pair` symbol. -/
abbrev cPair : code.Relations 1 := .cpair

/-- The `comp` symbol. -/
abbrev cComp : code.Relations 1 := .ccomp

/-- The `prec` symbol. -/
abbrev cPrec : code.Relations 1 := .cprec

/-- The `rfind'` symbol. -/
abbrev cRfind : code.Relations 1 := .crfind

/-- The first-child symbol. -/
abbrev cArg1 : code.Relations 2 := .carg1

/-- The second-child symbol. -/
abbrev cArg2 : code.Relations 2 := .carg2

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [code.Structure A]

/-- Being the root. -/
def CRoot (a : A) : Prop := RelMap cRoot ![a]

/-- Drawing the constructor `zero`. -/
def CZero (a : A) : Prop := RelMap cZero ![a]

/-- Drawing the constructor `succ`. -/
def CSucc (a : A) : Prop := RelMap cSucc ![a]

/-- Drawing the constructor `left`. -/
def CLeft (a : A) : Prop := RelMap cLeft ![a]

/-- Drawing the constructor `right`. -/
def CRight (a : A) : Prop := RelMap cRight ![a]

/-- Drawing the constructor `pair`. -/
def CPair (a : A) : Prop := RelMap cPair ![a]

/-- Drawing the constructor `comp`. -/
def CComp (a : A) : Prop := RelMap cComp ![a]

/-- Drawing the constructor `prec`. -/
def CPrec (a : A) : Prop := RelMap cPrec ![a]

/-- Drawing the constructor `rfind'`. -/
def CRfind (a : A) : Prop := RelMap cRfind ![a]

/-- Being the first child. -/
def CArg1 (a b : A) : Prop := RelMap cArg1 ![a, b]

/-- Being the second child. -/
def CArg2 (a b : A) : Prop := RelMap cArg2 ![a, b]

end Shorthands

section Decode

variable {A : Type} [code.Structure A]

/-- **The node `n` draws the code `c`.** A recursion on the code: the mark of
the node must be the constructor's, and its children must draw the
constructor's arguments. -/
def DecodesTo (n : A) : Nat.Partrec.Code → Prop
  | .zero => CZero n
  | .succ => CSucc n
  | .left => CLeft n
  | .right => CRight n
  | .pair cf cg =>
      CPair n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .comp cf cg =>
      CComp n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .prec cf cg =>
      CPrec n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .rfind' cf => CRfind n ∧ ∃ a, CArg1 n a ∧ DecodesTo a cf

end Decode

open Lax904597.Problems Lax624099.Problems

/-- The root of the instance draws a code halting on `0`. -/
def CodeHaltsOn (A : Type) [code.Structure A] : Prop :=
  ∃ (n : A) (c : Nat.Partrec.Code), CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom

/-- CODEHALT: does the partial recursive code drawn in the instance halt on
`0`? -/
def CODEHALT : DecisionProblem code :=
  DecisionProblem.ofPred CodeHaltsOn

end Lax624099.CodeHalting
