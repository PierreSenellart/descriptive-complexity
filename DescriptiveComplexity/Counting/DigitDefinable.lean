/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.OrderWalk
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Functions defined by their binary digits

A function from ordered structures to numbers is **digit-definable**
(`DescriptiveComplexity.DigitDefinable`) when its binary digits are relations
of a least fixed point: there are rules
(`DescriptiveComplexity.DigitLFPDef`) and finitely many of their relation
variables, `bit 0`, …, `bit (c - 1)`, all of the same arity `ℓ`, such that the
value is `∑ 2 ^ rank(τ, x̄)` over the pairs of a `τ < c` and a tuple `x̄` in the
relation `bit τ`. The pairs are the *positions* of the digits, ranked by `τ`
first and then lexicographically (`DescriptiveComplexity.orank`): the digit of
weight `2 ^ r` is `1` exactly when the position of rank `r` is in its relation.

Several relations are needed, and not only tuples of one: a structure with one
element has a single tuple of each length, and a function may take any value on
it.

This is the normal form through which QFO(LFP) is shown to capture FP
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], proof of Theorem 4.4):
a function computable in polynomial time has polynomially many digits, each
computable in polynomial time, hence, by the Immerman–Vardi theorem, definable
by a least fixed point over the ordered structure.

Both directions hold for the library's FP
(`DescriptiveComplexity.Problems.CircuitNumber`): digit-definable problems are
in FP (`DescriptiveComplexity.DigitDefinable.mem_FP`), and every problem of FP
is digit-definable (`DescriptiveComplexity.FPDefinable.digitDefinable`, in
`DescriptiveComplexity.Counting.Digits.NormalForm`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- A definition of a number by its binary digits: a least fixed point, as for
`DescriptiveComplexity.LFPDef`, and the relation variables holding the
digits. -/
structure DigitLFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The number of relation variables holding digits. -/
  c : ℕ
  /-- There is at least one. -/
  c_pos : 0 < c
  /-- Their common arity. -/
  ℓ : ℕ
  /-- The relation variables holding the digits, the least significant
  first. -/
  bit : Fin c → B.ι
  /-- They are distinct. -/
  bit_injective : Function.Injective bit
  /-- They have the same arity. -/
  arity_bit : ∀ τ, B.arity (bit τ) = ℓ

namespace DigitLFPDef

variable {L : Language.{0, 0}} (d : DigitLFPDef L) (A : Type) [L.Structure A] [LinearOrder A]

/-- The digit at a position is `1`: the tuple is in the relation of its
group. -/
def Holds (q : Fin d.c ×ₗ Lex (Fin d.ℓ → A)) : Prop :=
  lfpAssign d.rules (d.bit (ofLex q).1)
    fun k => ofLex (ofLex q).2 (Fin.cast (d.arity_bit (ofLex q).1) k)

open Classical in
/-- The value of a definition on an ordered structure: the number whose digit
of weight `2 ^ r` is `1` exactly when the position of rank `r` is in its
relation of the least fixed point. -/
noncomputable def value : ℕ :=
  ∑ᶠ q : Fin d.c ×ₗ Lex (Fin d.ℓ → A), if d.Holds A q then 2 ^ orank q else 0

end DigitLFPDef

/-- A counting problem is **digit-definable** when, on nonempty finite
structures, its binary digits are relations of a least fixed point, whatever
the linear order. -/
def DigitDefinable {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) : Prop :=
  ∃ d : DigitLFPDef L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = d.value A

end DescriptiveComplexity
