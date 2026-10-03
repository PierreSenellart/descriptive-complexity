import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Order
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Lax420092.QueryDatabases
import Mathlib.Data.Finset.Sort
import Lax904597.Classes
import Lax799700.Problems
import Lax420092.Evaluation

/-!
---
title: Packaged evaluation instances, their encoding and decoding
type: definition
---
A concrete Boolean conjunctive query over variables and constants is a list
of binary atoms with arguments in their disjoint union, and a concrete graph
database a list of facts over the constants; the query holds in the
database when some assignment of the variables to constants sends every
atom to a fact. A packaged instance fixes the numbers of variables and of
constants, at least one constant, with finite sets of atoms and of facts;
its size is the textbook one, elements plus atoms plus facts. The encoder
computes the structure of an instance, on its variables and constants as
universe, and a concrete query and database give a structure on their
disjoint union directly. A presentation is a raw relation table on a finite
universe; an instance is well-formed when some element is a constant, which
a first-order sentence states, and the decoder reads a packaged instance off
a well-formed presented structure by numbering its variables and its
constants in order. Well-formed evaluation is evaluation restricted to
well-formed instances.
-/

namespace Lax420092.PackagedInstances

open Lax420092.QueryDatabases

open FirstOrder

open Language Structure


/-- A concretely presented finite `L`-structure: a size and a computable
relation table. This is the input type of decoders – the “raw bytes” a
decoding computation reads. -/
structure FinPresentation (L : Language.{0, 0}) where
  /-- The number of elements. -/
  card : ℕ
  /-- The relations, as computations on `Fin card`. -/
  relBool : ∀ {n}, L.Relations n → (Fin n → Fin card) → Bool

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str {L : Language.{0, 0}} [L.IsRelational] (S : FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

section Concrete

variable {V C : Type}

/-- The textbook semantics of a concrete Boolean conjunctive query `q` (a
list of binary atoms with arguments in `V ⊕ C`: variables to the left,
constants to the right) on a concrete graph database `D` (a list of facts
over the constants): some assignment of the variables to constants sends
every atom to a fact. -/
def ConcreteQueryHolds (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) : Prop :=
  ∃ v : V → C, ∀ p ∈ q, (Sum.elim v id p.1, Sum.elim v id p.2) ∈ D

end Concrete

/-- A packaged concrete evaluation instance: `n` query variables, `m + 1`
database constants, a finite set of query atoms over them, and a finite set
of database facts on the constants. -/
structure CQInstance where
  /-- The number of query variables. -/
  vars : ℕ
  /-- The number of constants, minus one: constants are `Fin (consts + 1)`,
  so the database domain is never empty. -/
  consts : ℕ
  /-- The query atoms, over variables and constants. -/
  atoms : Finset ((Fin vars ⊕ Fin (consts + 1)) × (Fin vars ⊕ Fin (consts + 1)))
  /-- The database facts, over the constants. -/
  facts : Finset (Fin (consts + 1) × Fin (consts + 1))
  deriving DecidableEq

/-- The textbook size of a packaged instance: elements (variables and
constants) plus atoms plus facts. This is the one audited line of the
encoding – everything else is checked against it. -/
def cqSize : CQInstance → ℕ
  | ⟨n, m, q, D⟩ => n + (m + 1) + q.card + D.card

/-- The textbook semantics of a packaged instance: `ConcreteQueryHolds`, with
the finite sets in place of lists. -/
def ConcreteCQHolds : CQInstance → Prop
  | ⟨n, m, q, D⟩ => ∃ v : Fin n → Fin (m + 1),
      ∀ p ∈ q, (Sum.elim v id p.1, Sum.elim v id p.2) ∈ D

open FirstOrder

open Language Structure BoundedFormula

/-- The encoder itself, standalone rather than inline in the bundle, so that
it can be audited in isolation: it elaborates as a plain `def` – an encoder
deciding an undecidable predicate could not, the compiler would demand
`noncomputable` – and it genuinely runs (the `#guard`s below). Its
`#print axioms` still cites the classical axioms, harmlessly: `Finset`
membership is decided through `Multiset` quotients, whose instances cite them
in *proof* positions only – executability is witnessed by execution, not by
the axiom report. -/
def cqRelBool (i : CQInstance) {n : ℕ} (R : queryDb.Relations n) :
    (Fin n → (Fin i.vars ⊕ Fin (i.consts + 1))) → Bool :=
  match n, R with
  | _, .isVar => fun x => (x 0).isLeft
  | _, .atom => fun x => decide ((x 0, x 1) ∈ i.atoms)
  | _, .fact => fun x =>
    match x 0, x 1 with
    | Sum.inr a, Sum.inr b => decide ((a, b) ∈ i.facts)
    | _, _ => false

/-- The structure a packaged instance encodes: variables and constants as
universe, the relations the encoder's computations read as propositions. -/
instance cqStructure (i : CQInstance) :
    queryDb.Structure (Fin i.vars ⊕ Fin (i.consts + 1)) where
  funMap f := isEmptyElim f
  RelMap R x := cqRelBool i R x = true

section Concrete

variable {V C : Type}

/-- The `Language.queryDb`-structure encoding a concrete instance: universe
`V ⊕ C`, the variables being the left summands, with the atoms of `q` and
the facts of `D`. -/
@[reducible]
def queryDbStructure (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) :
    queryDb.Structure (V ⊕ C) where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .isVar => fun x =>
      match x 0 with
      | Sum.inl _ => True
      | Sum.inr _ => False
    | _, .atom => fun x => (x 0, x 1) ∈ q
    | _, .fact => fun x =>
      match x 0, x 1 with
      | Sum.inr a, Sum.inr b => (a, b) ∈ D
      | _, _ => False

end Concrete

/-- Well-formedness of an evaluation instance: some element is a constant.
The one condition the decoder needs. -/
noncomputable def cqWFSentence : queryDb.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1)
  (FirstOrder.Language.BoundedFormula.not
    (FirstOrder.Language.Relations.formula₁ qdbIsVar (FirstOrder.Language.Term.var (Sum.inr 0))))

section Decoder

variable (S : FinPresentation queryDb)

/-- The variable elements of a presented instance. -/
def cqVars : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool qdbIsVar ![x]

/-- The constant elements of a presented instance. -/
def cqConsts : Finset (Fin S.card) :=
  Finset.univ.filter fun x => ¬S.relBool qdbIsVar ![x]

/-- The elements of a presented instance read back from their numbers:
variables in order on the left, constants in order on the right. -/
def cqUnnumber {m : ℕ} (h : (cqConsts S).card = m + 1) :
    Fin (cqVars S).card ⊕ Fin (m + 1) → Fin S.card :=
  Sum.elim (fun a => (((cqVars S).orderIsoOfFin rfl) a : Fin S.card))
    fun b => (((cqConsts S).orderIsoOfFin rfl) (Fin.cast h.symm b) : Fin S.card)

/-- The decoder: the packaged instance whose variables, constants, atoms and
facts are those of the presented structure, read through the numbering, or
`none` when the structure has no constant. -/
def cqDecode : Option CQInstance :=
  match h : (cqConsts S).card with
  | 0 => none
  | m + 1 => some ⟨(cqVars S).card, m,
      Finset.univ.filter fun p => S.relBool qdbAtom
        ![cqUnnumber S h p.1, cqUnnumber S h p.2],
      Finset.univ.filter fun p => S.relBool qdbFact
        ![cqUnnumber S h (Sum.inr p.1), cqUnnumber S h (Sum.inr p.2)]⟩

end Decoder

open Lax904597.Problems Lax799700.Problems Lax420092.Evaluation

/-- Evaluation on well-formed instances: those with at least one constant,
the ones the decoder handles. -/
def WFCQEval : DecisionProblem queryDb :=
  DecisionProblem.ofPred fun (A : Type) [queryDb.Structure A] =>
    A ⊨ cqWFSentence ∧ QueryHolds A

end Lax420092.PackagedInstances
