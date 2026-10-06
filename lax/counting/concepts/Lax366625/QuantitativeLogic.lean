import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems
import Lax535992.HornFragment
import Lax535992.LeastFixedPoint
import Lax895169.BitPredicate
import Lax904597.SecondOrder
import Lax366625.CountingClasses

/-!
---
title: The class FP, by quantitative first-order logic with least fixed points
type: definition
---
The terms of quantitative first-order logic QFO are built from first-order
formulas, read as $1$ or $0$, and constants, by addition, multiplication,
and sums and products over tuples of elements. A definition in QFO(LFP)
over $L$ is a rule system defining a least fixed point, as in FO(LFP), and a
closed QFO term over $L \cup \{\le\}$ expanded by the relation variables,
read at the fixed point. A counting problem is in FP when some definition
takes the value $C(A)$ on every nonempty finite $L$-structure $A$, for every
linear order on $A$; this is the logic of polynomial-time computable
functions of Arenas, Muñoz, and Riveros. FP is the counting class of these
problems.

A digit definition is a least fixed point together with relation variables
of a common arity holding the binary digits of a number: the digit of
weight $2^r$ is $1$ when the tuple of rank $r$ in the lexicographic order is
in its relation. A counting problem is digit-definable when its value is
given by such a definition.
-/

namespace Lax366625.QuantitativeLogic

open Lax366625.CountingProblems Lax535992.HornFragment Lax535992.LeastFixedPoint
open Lax895169.BitPredicate Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A definition of a number by its binary digits: a least fixed point, as for
`LFPDef`, and the relation variables holding the
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

open FirstOrder

open Language Structure

/-- The terms of quantitative first-order logic over a Boolean layer of
first-order formulas, with free variables in `α`, after Arenas, Muñoz, and
Riveros, restricted to first-order quantifiers. A quantifier binds a block of
`n` variables at once, the variables `Sum.inr i` of `α ⊕ Fin n`; the
quantifiers `Σx` and `Πx` of their logic are the case `n = 1`. -/
inductive QTerm (L : Language.{0, 0}) : Type → Type 1
  /-- A formula: `1` when it holds, `0` when it does not. -/
  | ind {α : Type} (φ : L.Formula α) : QTerm L α
  /-- A constant. -/
  | const {α : Type} (s : ℕ) : QTerm L α
  /-- A sum. -/
  | add {α : Type} (s t : QTerm L α) : QTerm L α
  /-- A product. -/
  | mul {α : Type} (s t : QTerm L α) : QTerm L α
  /-- `Σx̄. t`: the sum over the `n`-tuples of elements of the structure. -/
  | sum {α : Type} (n : ℕ) (t : QTerm L (α ⊕ Fin n)) : QTerm L α
  /-- `Πx̄. t`: the product over the `n`-tuples of elements of the structure. -/
  | prod {α : Type} (n : ℕ) (t : QTerm L (α ⊕ Fin n)) : QTerm L α

namespace QTerm

variable {L L' : Language.{0, 0}}

open Classical in
/-- The value of a term in a structure, under a valuation. -/
noncomputable def eval {A : Type} [L.Structure A] : ∀ {α : Type}, QTerm L α → (α → A) → ℕ
  | _, ind φ, v => if φ.Realize v then 1 else 0
  | _, const s, _ => s
  | _, add s t, v => s.eval v + t.eval v
  | _, mul s t, v => s.eval v * t.eval v
  | _, sum _ t, v => ∑ᶠ w : Fin _ → A, t.eval (Sum.elim v w)
  | _, prod _ t, v => ∏ᶠ w : Fin _ → A, t.eval (Sum.elim v w)

/-- The value of a closed term. -/
noncomputable def value (t : QTerm L Empty) (A : Type) [L.Structure A] : ℕ :=
  t.eval (A := A) default

end QTerm

/-- A definition in QFO(LFP): a least fixed point, as for
`LFPDef`, and a quantitative term over the vocabulary
expanded by its relations, read at the fixed point. -/
structure QLFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The quantitative output. -/
  out : QTerm ((L.sum Language.order).sum B.lang) Empty

/-- The value of a definition on an ordered structure: the output, read at
the least fixed point of the rules. -/
noncomputable def QLFPDef.value {L : Language.{0, 0}} (d : QLFPDef L) (A : Type)
    [L.Structure A] [LinearOrder A] : ℕ :=
  @QTerm.value ((L.sum Language.order).sum d.B.lang) d.out A
    (@sumStructure _ _ A _ (d.B.structure (lfpAssign d.rules)))

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A counting problem is **in FP** when, on nonempty finite structures, it is
the value of a definition in QFO(LFP), whatever the linear order. -/
def FPDefinable (C : CountingProblem L) : Prop :=
  ∃ d : QLFPDef L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = d.value A

open Lax366625.CountingClasses

/-- **FP**: the class of the counting problems definable in QFO(LFP). -/
def FP : CountingClass :=
  CountingClass.ofMem fun C => FPDefinable C

end Lax366625.QuantitativeLogic
