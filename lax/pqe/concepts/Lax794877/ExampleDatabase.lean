import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.ModelTheory.Graph
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise
import Lax794877.WeightedWorlds
import Lax794877.Queries

/-!
---
title: A concrete probabilistic database
type: definition
---
A probabilistic database over the schema $R$, $S$, $T$ has $n$ constants
and, for every possible fact, a status: absent, certain, or uncertain with a
weight of presence and a weight of absence, both below $2^n$. A world gives
every fact a truth value admitted by its status, and has the product of the
weights of its uncertain facts as its weight. The count of the database is
the sum of the weights of the worlds in which $h_0$ holds, and its total the
sum of the weights of all worlds; both are computed by enumerating the
worlds. The database is encoded as a weighted instance on its constants,
which serve as bit positions in their own order.
-/

namespace Lax794877.ExampleDatabase

open FirstOrder

open Language Structure

/-- What a database says of a fact: it is absent, it is certain, or it is
uncertain with weights `a` and `c`, i.e., present with probability
`a / (a + c)`. -/
inductive FactStatus : Type
  /-- The fact is not in the database. -/
  | absent : FactStatus
  /-- The fact is in the database for sure. -/
  | certain : FactStatus
  /-- The fact is present with weight `a` and absent with weight `c`. -/
  | uncertain (a c : ℕ) : FactStatus
  deriving DecidableEq

namespace FactStatus

/-- The fact is certain. -/
def isCert : FactStatus → Bool
  | certain => true
  | _ => false

/-- The fact is uncertain. -/
def isUnc : FactStatus → Bool
  | uncertain _ _ => true
  | _ => false

/-- The weight of presence of an uncertain fact (and `0` otherwise). -/
def presW : FactStatus → ℕ
  | uncertain a _ => a
  | _ => 0

/-- The weight of absence of an uncertain fact (and `0` otherwise). -/
def absW : FactStatus → ℕ
  | uncertain _ c => c
  | _ => 0

end FactStatus

/-- **A probabilistic database** over the schema `R`, `S`, `T`, with `n`
constants: the status of every possible fact. The weights are written in
binary on `n` bits, so they are below `2 ^ n`. -/
structure ProbDb where
  /-- The number of constants. -/
  n : ℕ
  /-- The status of the fact `R(x)`. -/
  r : Fin n → FactStatus
  /-- The status of the fact `S(x, y)`. -/
  s : Fin n → Fin n → FactStatus
  /-- The status of the fact `T(y)`. -/
  t : Fin n → FactStatus
  /-- The weights of the `R`-facts fit in `n` bits. -/
  fits_r : ∀ x, (r x).presW < 2 ^ n ∧ (r x).absW < 2 ^ n
  /-- The weights of the `S`-facts fit in `n` bits. -/
  fits_s : ∀ x y, (s x y).presW < 2 ^ n ∧ (s x y).absW < 2 ^ n
  /-- The weights of the `T`-facts fit in `n` bits. -/
  fits_t : ∀ y, (t y).presW < 2 ^ n ∧ (t y).absW < 2 ^ n

namespace FactStatus

/-- A world may give the fact the truth value `b`: an absent fact is false, a
certain fact is true, an uncertain fact is either. -/
def admits : FactStatus → Bool → Bool
  | absent, b => !b
  | certain, b => b
  | uncertain _ _, _ => true

/-- The weight the fact contributes to a world giving it the truth value `b`:
its weight of presence or of absence if it is uncertain, and `1` otherwise. -/
def weight : FactStatus → Bool → ℕ
  | uncertain a c, b => if b then a else c
  | _, _ => 1

end FactStatus

/-- A world over `n` constants: the truth value of every possible fact. -/
abbrev World (n : ℕ) : Type := (Fin n → Bool) × (Fin n → Fin n → Bool) × (Fin n → Bool)

namespace ProbDb

variable (i : ProbDb)

/-- The world is a possible world of the database. -/
def Valid (W : World i.n) : Prop :=
  (∀ x, (i.r x).admits (W.1 x) = true) ∧ (∀ x y, (i.s x y).admits (W.2.1 x y) = true) ∧
    ∀ y, (i.t y).admits (W.2.2 y) = true

instance instDecidableValid (W : World i.n) : Decidable (i.Valid W) := by
  unfold Valid
  infer_instance

/-- The weight of a world: the product of the weights of the facts. -/
def weight (W : World i.n) : ℕ :=
  (∏ x, (i.r x).weight (W.1 x)) * ((∏ x, ∏ y, (i.s x y).weight (W.2.1 x y)) *
    ∏ y, (i.t y).weight (W.2.2 y))

end ProbDb

/-- The query `h₀` holds in a world. -/
def HoldsH0 {n : ℕ} (W : World n) : Prop :=
  ∃ x y, W.1 x = true ∧ W.2.1 x y = true ∧ W.2.2 y = true

instance {n : ℕ} (W : World n) : Decidable (HoldsH0 W) := by
  unfold HoldsH0
  infer_instance

/-- **The concrete weighted count of `h₀`**: the sum of the weights of the
possible worlds of the database in which the query holds. -/
def ProbDb.count (i : ProbDb) : ℕ :=
  ∑ W : World i.n, if i.Valid W ∧ HoldsH0 W then i.weight W else 0

/-- The weighted count of all the possible worlds: the denominator of the
probability. -/
def ProbDb.total (i : ProbDb) : ℕ :=
  ∑ W : World i.n, if i.Valid W then i.weight W else 0

open Lax794877.WeightedWorlds Lax794877.Queries

/-- The relations of the encoded database: the status of each fact, the binary
digits of its weights, and the order of the constants. -/
def probDbRel (i : ProbDb) : ∀ {n}, (weightedLang rst).Relations n → (Fin n → Fin i.n) → Bool :=
  fun {n} R =>
    match n, R with
    | _, .cert .r => fun x => (i.r (x 0)).isCert
    | _, .cert .s => fun x => (i.s (x 0) (x 1)).isCert
    | _, .cert .t => fun x => (i.t (x 0)).isCert
    | _, .unc .r => fun x => (i.r (x 0)).isUnc
    | _, .unc .s => fun x => (i.s (x 0) (x 1)).isUnc
    | _, .unc .t => fun x => (i.t (x 0)).isUnc
    | _, .pres .r => fun x => (i.r (x 0)).presW.testBit (x 1).1
    | _, .pres .s => fun x => (i.s (x 0) (x 1)).presW.testBit (x 2).1
    | _, .pres .t => fun x => (i.t (x 0)).presW.testBit (x 1).1
    | _, .abs .r => fun x => (i.r (x 0)).absW.testBit (x 1).1
    | _, .abs .s => fun x => (i.s (x 0) (x 1)).absW.testBit (x 2).1
    | _, .abs .t => fun x => (i.t (x 0)).absW.testBit (x 1).1
    | _, .le => fun x => decide (x 0 ≤ x 1)

/-- **The encoded database**: the weighted instance on the constants. -/
def probDbStructure (i : ProbDb) : (weightedLang rst).Structure (Fin i.n) where
  funMap f := isEmptyElim f
  RelMap R x := probDbRel i R x = true

end Lax794877.ExampleDatabase
