import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.List.FinRange
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax751879.OrderedStructures
import Lax904597.Problems
import Lax988886.FiniteStructures

/-!
---
title: Decision problems of the core on bit strings
type: definition
---
A vocabulary of the NP core, with finitely many relation symbols, is numbered by a
list of arities. A table of the Immerman–Vardi entry, of that list of arities, then reads
as a structure on an initial segment of the natural numbers, and a decision problem of
the core reads as a property of tables and as a Boolean query. The empty table is a
no-instance, the classes of the core being about nonempty structures. A word that encodes
no table is in no language of the two entries, so nothing else needs care.
-/

namespace Lax832283.StringProblems

open Lax751879.OrderedStructures Lax904597.Problems Lax988886.FiniteStructures

open FirstOrder

/-- An enumeration of the relation symbols of `L`, listing their arities. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The arities of the symbols, in the order of the enumeration. -/
  σ : List ℕ
  /-- The symbol of a given number, with its arity. -/
  sym : Fin σ.length ≃ Σ n, L.Relations n
  /-- The list records the arity of each symbol. -/
  arity_sym : ∀ i, (sym i).1 = σ.get i

namespace FinVocab

variable {L : Language.{0, 0}}

variable (V : FinVocab L)

/-- The number of a given symbol. -/
def toSym {n : ℕ} (R : L.Relations n) : Fin V.σ.length :=
  V.sym.symm ⟨n, R⟩

end FinVocab

open FirstOrder Language Structure



variable {L : Language.{0, 0}}

/-- Read a table of the archive's formalism as a structure of the library. -/
@[reducible]
def ofOrdered [L.IsRelational] (V : FinVocab L) (S : OrderedStructure V.σ) :
    L.Structure (Fin S.size) where
  funMap f := isEmptyElim f
  RelMap {n} R v := S.relation (V.toSym R) (v ∘ Fin.cast
    (show V.σ.get (V.toSym R) = n by rw [← V.arity_sym, FinVocab.toSym, Equiv.apply_symm_apply]))
    = true

/-- A decision problem of the library, as a property of the archive's structures. The
empty structure is a no-instance. -/
def toProperty [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L) :
    Property V.σ :=
  fun S => 0 < S.size ∧ @DecisionProblem.Holds L _ P (Fin S.size) (ofOrdered V S)

/-- A decision problem of the library, as a Boolean query on ordered structures. -/
def toQuery [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L) : Query V.σ 0 :=
  fun S => toProperty V P S.structureValue

end Lax832283.StringProblems
