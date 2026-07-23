/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel
import DescriptiveComplexity.Interpretation
import Mathlib.Algebra.BigOperators.Finprod

/-!
# 0-1 integer programming: definition

0-1 INTEGER PROGRAMMING ([Karp 1972][karp1972reducibility]): given a matrix
`C` and a vector `d`, is there a `0-1` vector `x` with `C x = d`? It is the
multi-row form of Knapsack, and like it belongs to **representation (C)**: the
entries are written in binary, since under the unary representation the
problem is solvable in polynomial time by dynamic programming and is therefore
not NP-hard at all.

## The vocabulary

`FirstOrder.Language.zeroOneIP` carries

* `col j`, `row r` and `posn p`, the columns (the `0-1` variables), the rows
  (the equations) and the bit positions;
* `coef r j p`, “the entry of row `r` in column `j` has bit 1 at position
  `p`”, the only ternary symbol of the catalog;
* `rhs r p`, the bits of the right-hand side of row `r`;
* `le`, a linear order fixing the place values, folded into the yes-instances
  (`DescriptiveComplexity.IsLinOrd`) as everywhere in representation (C).

Entries are **natural numbers**: Karp states the problem over the integers,
and the restriction formalized here is the one his reduction produces – a
special case, so its NP-hardness gives his problem's a fortiori, while
membership in NP for signed entries would need the two sides of each equation
weighed separately and is not claimed.
-/

/- The language of 0-1 integer programs lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` and
`Language.order`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of 0-1 integer programs. -/
inductive zeroOneIPRel : ℕ → Type
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
protected def zeroOneIP : Language :=
  ⟨fun _ => Empty, zeroOneIPRel⟩
  deriving IsRelational

/-- The column symbol. -/
abbrev ipCol : Language.zeroOneIP.Relations 1 := .col

/-- The row symbol. -/
abbrev ipRow : Language.zeroOneIP.Relations 1 := .row

/-- The position symbol. -/
abbrev ipPosn : Language.zeroOneIP.Relations 1 := .posn

/-- The entry symbol. -/
abbrev ipCoef : Language.zeroOneIP.Relations 3 := .coef

/-- The right-hand side symbol. -/
abbrev ipRhs : Language.zeroOneIP.Relations 2 := .rhs

/-- The order symbol. -/
abbrev ipLe : Language.zeroOneIP.Relations 2 := .le

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.zeroOneIP.Structure A]

/-- Being a column, that is, a `0-1` variable. -/
def IPCol (a : A) : Prop := RelMap ipCol ![a]

/-- Being a row, that is, an equation. -/
def IPRow (a : A) : Prop := RelMap ipRow ![a]

/-- Being a bit position. -/
def IPPosn (a : A) : Prop := RelMap ipPosn ![a]

/-- The bit of an entry at a position. -/
def IPCoef (r j p : A) : Prop := RelMap ipCoef ![r, j, p]

/-- The bits of a right-hand side. -/
def IPRhs (r p : A) : Prop := RelMap ipRhs ![r, p]

/-- The order carrying the place values. -/
def IPLe (a b : A) : Prop := RelMap ipLe ![a, b]

/-- The entry of a row in a column, decoded. -/
noncomputable def IPCoefVal (r j : A) : ℕ := binNum IPLe IPPosn (IPCoef r j)

/-- The right-hand side of a row, decoded. -/
noncomputable def IPRhsVal (r : A) : ℕ := binNum IPLe IPPosn (IPRhs r)

end Shorthands

/-! ### The problem -/

section Problem

variable (A : Type) [Language.zeroOneIP.Structure A]

/-- A 0-1 integer program is a yes-instance when its order is a linear order
and some set of columns – the variables set to `1` – makes every equation
hold. -/
def HasZeroOneSolution : Prop :=
  Finite A ∧ IsLinOrd (IPLe (A := A)) ∧
    ∃ x : A → Prop, (∀ j, x j → IPCol j) ∧
      ∀ r, IPRow r → (∑ᶠ j ∈ {j | x j}, IPCoefVal r j) = IPRhsVal r

end Problem

section Iso

variable {A B : Type} [Language.zeroOneIP.Structure A] [Language.zeroOneIP.Structure B]

private theorem hasZeroOneSolution_of_iso (e : A ≃[Language.zeroOneIP] B)
    (h : HasZeroOneSolution A) : HasZeroOneSolution B := by
  obtain ⟨hfin, hlin, x, hxc, hsum⟩ := h
  have hle : ∀ a a' : A, IPLe a a' ↔ IPLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e ipLe a a'
  have hposn : ∀ a : A, IPPosn a ↔ IPPosn (e a) := fun a => relMap_equiv₁ e ipPosn a
  have hcol : ∀ a : A, IPCol a ↔ IPCol (e a) := fun a => relMap_equiv₁ e ipCol a
  have hrow : ∀ a : A, IPRow a ↔ IPRow (e a) := fun a => relMap_equiv₁ e ipRow a
  have hcoef : ∀ a b c : A, IPCoef a b c ↔ IPCoef (e a) (e b) (e c) := fun a b c =>
    relMap_equiv₃ e ipCoef a b c
  have hrhs : ∀ a b : A, IPRhs a b ↔ IPRhs (e a) (e b) := fun a b => relMap_equiv₂ e ipRhs a b
  have hcv : ∀ r j : A, IPCoefVal r j = IPCoefVal (e r) (e j) := fun r j =>
    binNum_equiv e.toEquiv hle hposn (hcoef r j)
  have hrv : ∀ r : A, IPRhsVal r = IPRhsVal (e r) := fun r =>
    binNum_equiv e.toEquiv hle hposn (hrhs r)
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => x (e.toEquiv.symm b), fun b hb => ?_, fun r hr => ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hcol _).mp (hxc _ hb)
  · have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := fun b => e.toEquiv.apply_symm_apply b
    have hr' : IPRow (e.toEquiv.symm r) := by
      rw [hrow, hsymm]
      exact hr
    have hbij : Set.BijOn e.toEquiv {j : A | x j} {b : B | x (e.toEquiv.symm b)} := by
      refine ⟨fun j hj => ?_, e.toEquiv.injective.injOn,
        fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
      simpa using hj
    have hstep : ∀ j : A, IPCoefVal (e.toEquiv.symm r) j = IPCoefVal r (e j) := by
      intro j
      rw [hcv (e.toEquiv.symm r) j, hsymm]
    have hrhs' : IPRhsVal (e.toEquiv.symm r) = IPRhsVal r := by
      rw [hrv (e.toEquiv.symm r), hsymm]
    rw [← finsum_mem_eq_of_bijOn e.toEquiv hbij fun j _ => hstep j, hsum _ hr', hrhs']

/-- Being a yes-instance of 0-1 integer programming is
isomorphism-invariant. -/
theorem hasZeroOneSolution_iso (e : A ≃[Language.zeroOneIP] B) :
    HasZeroOneSolution A ↔ HasZeroOneSolution B :=
  ⟨hasZeroOneSolution_of_iso e, hasZeroOneSolution_of_iso e.symm⟩

end Iso

/-- 0-1 INTEGER PROGRAMMING, as a problem on 0-1 integer programs: is there a
set of columns whose entries sum, row by row, exactly to the right-hand
sides? The entries are written in *binary*, which is what makes the problem
NP-hard rather than polynomial-time. -/
def ZeroOneIP : DecisionProblem Language.zeroOneIP where
  Holds := fun A inst => @HasZeroOneSolution A inst
  iso_invariant := fun e => hasZeroOneSolution_iso e

end DescriptiveComplexity
