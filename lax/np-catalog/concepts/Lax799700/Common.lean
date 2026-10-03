import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Syntax
import Lax904597.Sat
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Clauses, literals and binary numbers
type: definition
---
The two pieces of shared vocabulary the catalog's problems are stated
with. On a CNF structure of the NP core's vocabulary, IsCl, PosIn, NegIn
and OccIn read off clauses and the signed occurrences of variables in
them, and LitTrue evaluates a literal under an assignment; the
satisfiability variants (3SAT, NAE-SAT, 1-in-SAT) are written with these.
On a structure carrying a set of bit positions and an order on them,
bitRank is the number of positions strictly below a position and binNum
decodes a set of positions as the number whose binary digits they are;
the problems written in binary (Knapsack, Partition, 0-1 integer
programming, job sequencing) compare numbers decoded this way. Both
decoders are total, defined for an arbitrary relation in place of the
order, so that isomorphism-invariance is a plain transport statement.

-/

namespace Lax799700.Common

open Lax904597.Sat

section Decode

variable {A : Type}

/-- The rank of a position: the number of positions strictly below it. This is
the place value's exponent. -/
noncomputable def bitRank (Le : A → A → Prop) (Posn : A → Prop) (p : A) : ℕ :=
  ({q | Posn q ∧ Le q p ∧ q ≠ p} : Set A).ncard

/-- The number encoded by the set `b` of positions: `∑ 2 ^ rank`. -/
noncomputable def binNum (Le : A → A → Prop) (Posn b : A → Prop) : ℕ :=
  ∑ᶠ p ∈ {p | Posn p ∧ b p}, 2 ^ bitRank Le Posn p

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses, so that stray
`posIn`/`negIn` facts on non-clause elements do not create gadgets. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

/-- The literal `(x, s)` is true under the assignment `ν`. -/
def LitTrue (ν : A → Prop) (x : A) (s : Bool) : Prop := if s then ν x else ¬ν x

end SatOcc

end Lax799700.Common
