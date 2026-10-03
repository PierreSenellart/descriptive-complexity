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
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Computability.RE
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Pi
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic.Ring
import Lax624099.CodeHalting
import Lax624099.FiniteSatisfiability
import Lax904597.Machines
import Lax904597.Problems

/-!
---
title: Problems as sets of concrete finite structures
type: definition
---
A problem on finite structures read as a set of concrete data. A presented
vocabulary numbers the finitely many relation symbols of a vocabulary with
their arities, so that reading a symbol off its number and numbering a
symbol are inverse; every vocabulary of the catalog is presented this way,
and the vocabularies of machine instances, of encoded sentences and of code
instances are presented here. A concrete finite structure over a presented
vocabulary is a universe size and a table of Booleans, one row per symbol,
the row of an $n$-ary symbol read at the number of a tuple written in base
the size of the universe; out-of-range lookups read false, so every such
piece of data denotes a structure, on a nonempty linearly ordered universe.
The predicate a decision problem defines on concrete structures holds of a
piece of data when the structure it denotes is a yes-instance. This is the
type on which Mathlib's computability notions, decidability and recursive
enumerability, are read.
-/

namespace Lax624099.ConcreteInstances

open Lax904597.Problems

open FirstOrder

open FirstOrder.Language Structure

section Digits

/-- The number of a tuple of digits, little-endian in base `c`. -/
def tupleIdx (c : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + c * tupleIdx c l

/-- The `j`-th digit of `t` in base `c`. -/
def digitAt (c t j : ℕ) : ℕ := t / c ^ j % c

end Digits

/-- A **finitely presented relational vocabulary**: the relation symbols of `L`
numbered by `Fin numSyms`, with their arities. Reading a symbol off its number
(`sym`) and numbering a symbol (`index`) are mutually inverse, so the
presentation loses nothing.

Every vocabulary of the catalog is of this shape: `Language.turing` has 12
symbols of arity at most 2, `Language.finsat` 14 of arity at most 3. The
presentations are closed under `Language.sum`
(`FirstOrder.Language.FinVocab.sum`), which is what lets the second-order
machinery – whose vocabularies are sums of the instance's with a block's – be
encoded by the same means. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The number of relation symbols. -/
  numSyms : ℕ
  /-- The symbol with a given number, together with its arity. -/
  symOf : Fin numSyms → ((n : ℕ) × L.Relations n)
  /-- The number of a symbol. -/
  index : ∀ {n : ℕ}, L.Relations n → Fin numSyms
  /-- Reading back the symbol with the number of a symbol gives it back. -/
  symOf_index : ∀ {n : ℕ} (R : L.Relations n), symOf (index R) = ⟨n, R⟩
  /-- Numbering the symbol with a given number gives that number back. -/
  index_symOf : ∀ i : Fin numSyms, index (symOf i).2 = i

namespace FinVocab

variable {L : Language.{0, 0}} (V : FinVocab L)

/-- The arity of the symbol with a given number. -/
abbrev arity (i : Fin V.numSyms) : ℕ := (V.symOf i).1

/-- The symbol with a given number. -/
abbrev sym (i : Fin V.numSyms) : L.Relations (V.arity i) := (V.symOf i).2

end FinVocab

/-- A **concrete finite structure** over the finitely presented vocabulary
`V`: a universe size and a table of Booleans, one row per relation symbol.

The universe is `Fin (univSize + 1)`, so it is nonempty by construction; the
row of an `n`-ary symbol is read at the number of the tuple, little-endian in
base `card`. Anything out of range reads `false`, so every pair of a number
and a list of lists of Booleans denotes a structure. -/
structure FinStruct {L : Language.{0, 0}} (V : FinVocab L) where
  /-- One less than the size of the universe. -/
  univSize : ℕ
  /-- The tables of the relations, one row per symbol. -/
  table : List (List Bool)

namespace FinStruct

variable {L : Language.{0, 0}} {V : FinVocab L}

/-- The size of the universe of a concrete finite structure. -/
abbrev card (s : FinStruct V) : ℕ := s.univSize + 1

/-- The universe of a concrete finite structure: nonempty and linearly ordered
by construction. -/
abbrev Univ (s : FinStruct V) : Type := Fin s.card

/-- The table lookup: does the relation `R` hold of the tuple `x`? -/
def relMapBool (s : FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) : Bool :=
  (s.table.getD (V.index R) []).getD (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false

/-- **The structure a piece of data denotes.** -/
instance instStructure [L.IsRelational] (s : FinStruct V) : L.Structure s.Univ where
  funMap f := isEmptyElim f
  RelMap R x := s.relMapBool R x = true

/-- The concrete structure over a universe `Fin (k + 1)` whose relations are
given by the Boolean function `f`. -/
def ofTable (V : FinVocab L) (k : ℕ)
    (f : ∀ {n : ℕ}, L.Relations n → (Fin n → Fin (k + 1)) → Bool) : FinStruct V where
  univSize := k
  table := List.ofFn fun i : Fin V.numSyms =>
    (List.range ((k + 1) ^ V.arity i)).map fun t =>
      f (V.sym i) fun j => ⟨digitAt (k + 1) t j, Nat.mod_lt _ (Nat.succ_pos k)⟩

/-- The coding of a concrete finite structure as a pair. -/
def equivProd (V : FinVocab L) : FinStruct V ≃ ℕ × List (List Bool) where
  toFun s := (s.univSize, s.table)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- **Concrete finite structures are a `Primcodable` type**: the object
`ComputablePred` and `REPred` are defined on. -/
instance instPrimcodable (V : FinVocab L) : Primcodable (FinStruct V) :=
  Primcodable.ofEquiv _ (equivProd V)

end FinStruct

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The set of concrete instances a decision problem denotes.** This is the
object `ComputablePred` and `REPred` are about: a problem is an
isomorphism-closed property of finite structures, and the numbering of
`FirstOrder.Language.FinStruct` turns it into a property of a `Primcodable`
type, with nothing to write per problem. -/
def DecisionProblem.toPred (P : DecisionProblem L) (V : FinVocab L) :
    FinStruct V → Prop := fun s => P s.Univ

open FirstOrder

open FirstOrder.Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

/-- **A numbering of the symbols is a presentation**, the converse of
`FirstOrder.Language.FinVocab.symEquiv`. -/
def ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n)) : FinVocab L where
  numSyms := k
  symOf := e
  index R := e.symm ⟨_, R⟩
  symOf_index R := e.apply_symm_apply _
  index_symOf i := by simp

/-- **A vocabulary presented by a list of all its symbols**, without
repetitions: the way the vocabularies of the catalog, which are finite
enumerations, are presented. -/
def ofList [DecidableEq ((n : ℕ) × L.Relations n)] (l : List ((n : ℕ) × L.Relations n))
    (nd : l.Nodup) (h : ∀ p : (n : ℕ) × L.Relations n, p ∈ l) : FinVocab L :=
  ofEquivSigma l.length (List.Nodup.getEquivOfForallMemList l nd h)

end FinVocab

open Lax904597.Machines Lax624099.FiniteSatisfiability Lax624099.CodeHalting

instance instDecidableEqSigmaNatRelationsTuring : DecidableEq ((n : ℕ) × turing.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × turingRel n))

instance instDecidableEqSigmaNatRelationsFinsat : DecidableEq ((n : ℕ) × finsat.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × finsatRel n))

instance instDecidableEqSigmaNatRelationsCode : DecidableEq ((n : ℕ) × code.Relations n) :=
  inferInstanceAs (DecidableEq ((n : ℕ) × codeRel n))

/-- **The vocabulary of machine instances, presented**: twelve symbols, six
unary and six binary. -/
def turingVocab : FinVocab turing :=
  FinVocab.ofList
    [⟨1, .posn⟩, ⟨1, .tr⟩, ⟨1, .start⟩, ⟨1, .acc⟩, ⟨1, .blank⟩, ⟨1, .right⟩,
      ⟨2, .le⟩, ⟨2, .tsrc⟩, ⟨2, .tread⟩, ⟨2, .tdst⟩, ⟨2, .twrite⟩, ⟨2, .inp⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

/-- **The vocabulary of first-order sentences as instances, presented**:
fourteen symbols of arity at most three. -/
def finsatVocab : FinVocab finsat :=
  FinVocab.ofList
    [⟨2, .le⟩, ⟨1, .andN⟩, ⟨1, .orN⟩, ⟨1, .allN⟩, ⟨1, .exN⟩, ⟨2, .child⟩,
      ⟨2, .bind⟩, ⟨3, .eqL⟩, ⟨3, .neqL⟩, ⟨2, .posL⟩, ⟨2, .negL⟩, ⟨3, .arg⟩,
      ⟨2, .sig⟩, ⟨1, .root⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

/-- **The vocabulary of code instances, presented**: eleven symbols, nine
unary and two binary. -/
def codeVocab : FinVocab code :=
  FinVocab.ofList
    [⟨1, .croot⟩, ⟨1, .czero⟩, ⟨1, .csucc⟩, ⟨1, .cleft⟩, ⟨1, .cright⟩, ⟨1, .cpair⟩,
      ⟨1, .ccomp⟩, ⟨1, .cprec⟩, ⟨1, .crfind⟩, ⟨2, .carg1⟩, ⟨2, .carg2⟩]
    (by decide) (by rintro ⟨n, R⟩; cases R <;> simp)

end Lax624099.ConcreteInstances
