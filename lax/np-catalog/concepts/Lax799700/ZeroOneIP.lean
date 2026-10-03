import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Syntax
import Lax799700.Common
import Lax904597.Machines
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: 0-1 integer programming
type: theorem
---
0-1 INTEGER PROGRAMMING: given a matrix $C$ and a vector $d$, is there a
0-1 vector $x$ with $Cx = d$? It is the multi-row form of Knapsack and is
written in binary like it. The vocabulary carries the columns, the rows,
the bit positions, the bits of each coefficient (the catalog's one
ternary symbol), the bits of each right-hand side, and a linear order
fixing the place values. Entries are natural numbers: Karp states the
problem over the integers, and this restriction is the one his reduction
produces, so its NP-hardness gives his problem's a fortiori. Membership
is by an existential second-order definition, hardness by an ordered
first-order reduction from Knapsack.

-/

namespace Lax799700.ZeroOneIP

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive zeroOneIPRel : ℕ → Type where
/-- `col j`: `j` is a column, that is, a `0-1` variable. -/
  | col : zeroOneIPRel 1
/-- `row r`: `r` is a row, that is, an equation. -/
  | row : zeroOneIPRel 1
/-- `posn p`: `p` is a bit position. -/
  | posn : zeroOneIPRel 1
/-- `coef r j p`: the entry of row `r` in column `j` has bit 1 at `p`. -/
  | coef : zeroOneIPRel 3
/-- `rhs r p`: the right-hand side of row `r` has bit 1 at `p`. -/
  | rhs : zeroOneIPRel 2
/-- `le a b`: the linear order carrying the place values. -/
  | le : zeroOneIPRel 2
  deriving DecidableEq

/-- The relational language of 0-1 integer programs: columns, rows and bit
positions, the bits of each entry and of each right-hand side, and a linear
order. -/
def zeroOneIP : FirstOrder.Language :=
  ⟨fun _ => Empty, zeroOneIPRel⟩

instance instIsRelationalZeroOneIP : FirstOrder.Language.IsRelational zeroOneIP := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `col j`: `j` is a column, that is, a `0-1` variable. -/
abbrev ipCol : zeroOneIP.Relations 1 :=
  .col

/-- `row r`: `r` is a row, that is, an equation. -/
abbrev ipRow : zeroOneIP.Relations 1 :=
  .row

/-- `posn p`: `p` is a bit position. -/
abbrev ipPosn : zeroOneIP.Relations 1 :=
  .posn

/-- `coef r j p`: the entry of row `r` in column `j` has bit 1 at `p`. -/
abbrev ipCoef : zeroOneIP.Relations 3 :=
  .coef

/-- `rhs r p`: the right-hand side of row `r` has bit 1 at `p`. -/
abbrev ipRhs : zeroOneIP.Relations 2 :=
  .rhs

/-- `le a b`: the linear order carrying the place values. -/
abbrev ipLe : zeroOneIP.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [zeroOneIP.Structure A]

/-- `col j`: `j` is a column, that is, a `0-1` variable.  -/
def IPCol {A : Type} [zeroOneIP.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipCol ![a0]

/-- `row r`: `r` is a row, that is, an equation.  -/
def IPRow {A : Type} [zeroOneIP.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipRow ![a0]

/-- `posn p`: `p` is a bit position.  -/
def IPPosn {A : Type} [zeroOneIP.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipPosn ![a0]

/-- `coef r j p`: the entry of row `r` in column `j` has bit 1 at `p`.  -/
def IPCoef {A : Type} [zeroOneIP.Structure A] (a0 : A) (a1 : A) (a2 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipCoef ![a0, a1, a2]

/-- `rhs r p`: the right-hand side of row `r` has bit 1 at `p`.  -/
def IPRhs {A : Type} [zeroOneIP.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipRhs ![a0, a1]

/-- `le a b`: the linear order carrying the place values.  -/
def IPLe {A : Type} [zeroOneIP.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ipLe ![a0, a1]

/-- The entry of a row in a column, decoded. -/
noncomputable def IPCoefVal (r j : A) : ℕ := binNum IPLe IPPosn (IPCoef r j)

/-- The right-hand side of a row, decoded. -/
noncomputable def IPRhsVal (r : A) : ℕ := binNum IPLe IPPosn (IPRhs r)

end Shorthands

section Problem

variable (A : Type) [zeroOneIP.Structure A]

/-- A 0-1 integer program is a yes-instance when its order is a linear order
and some set of columns – the variables set to `1` – makes every equation
hold. -/
def HasZeroOneSolution : Prop :=
  Finite A ∧ IsLinOrd (IPLe (A := A)) ∧
    ∃ x : A → Prop, (∀ j, x j → IPCol j) ∧
      ∀ r, IPRow r → (∑ᶠ j ∈ {j | x j}, IPCoefVal r j) = IPRhsVal r

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasZeroOneSolution` is isomorphism-invariant. -/
axiom hasZeroOneSolution_iso : ∀ {A B : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A] [Lax799700.ZeroOneIP.zeroOneIP.Structure B],
  (A ≃[Lax799700.ZeroOneIP.zeroOneIP] B) → (HasZeroOneSolution A ↔ HasZeroOneSolution B)

/-- The problem ZeroOneIP: does the structure satisfy `HasZeroOneSolution`? -/
def ZeroOneIP : DecisionProblem Lax799700.ZeroOneIP.zeroOneIP :=
  DecisionProblem.ofPred HasZeroOneSolution

/-- The yes-instances of ZeroOneIP are exactly the structures satisfying
`HasZeroOneSolution`. -/
axiom zeroOneIP_iff : ∀ (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A], ZeroOneIP A ↔ HasZeroOneSolution A

/-- ZeroOneIP is NP-complete. -/
axiom zeroOneIP_NP_complete : NP.Complete ZeroOneIP

end Lax799700.ZeroOneIP
