import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Lax366625.CountingProblems
import Lax904597.SecondOrder

/-!
---
title: The quantitative logic ΣQSO(FO)
type: definition
---
The terms of ΣQSO(FO), after Arenas, Muñoz, and Riveros, are built from
first-order formulas, read as $1$ when they hold and $0$ otherwise, and from
constants, by addition, multiplication, sums and products over tuples of
elements, and sums over the assignments of a block of relation variables.
Their value on a structure is computed accordingly. A counting problem $C$
over $L$ is ΣQSO(FO)-definable when some closed term over
$L \cup \{\le\}$ has value $C(A)$ on every nonempty finite $L$-structure
$A$, for every linear order on $A$.
-/

namespace Lax366625.SecondOrderCounting

open Lax366625.CountingProblems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- **The terms of ΣQSO(FO)** over the vocabulary `L`, with free first-order
variables in `α`. A first-order quantifier binds a block of `n` variables at
once, the variables `Sum.inr i` of `α ⊕ Fin n`; a second-order sum binds the
relation variables of a block, the term under it being over the vocabulary
expanded by the block. -/
inductive SQTerm : Language.{0, 0} → Type → Type 1
  /-- A formula: `1` when it holds, `0` when it does not. -/
  | ind {L : Language.{0, 0}} {α : Type} (φ : L.Formula α) : SQTerm L α
  /-- A constant. -/
  | const {L : Language.{0, 0}} {α : Type} (s : ℕ) : SQTerm L α
  /-- A sum. -/
  | add {L : Language.{0, 0}} {α : Type} (s t : SQTerm L α) : SQTerm L α
  /-- A product. -/
  | mul {L : Language.{0, 0}} {α : Type} (s t : SQTerm L α) : SQTerm L α
  /-- `Σx̄. t`: the sum over the `n`-tuples of elements. -/
  | sum {L : Language.{0, 0}} {α : Type} (n : ℕ) (t : SQTerm L (α ⊕ Fin n)) : SQTerm L α
  /-- `Πx̄. t`: the product over the `n`-tuples of elements. -/
  | prod {L : Language.{0, 0}} {α : Type} (n : ℕ) (t : SQTerm L (α ⊕ Fin n)) : SQTerm L α
  /-- `ΣX̄. t`: the sum over the assignments of a block of relation
  variables. -/
  | sosum {L : Language.{0, 0}} {α : Type} (B : SOBlock) (t : SQTerm (L.sum B.lang) α) :
      SQTerm L α

namespace SQTerm

open Classical in
/-- The value of a term in a structure, under a valuation. -/
noncomputable def eval : ∀ {L : Language.{0, 0}} {α : Type}, SQTerm L α →
    ∀ (A : Type) [L.Structure A], (α → A) → ℕ
  | _, _, ind φ, _, _, v => if φ.Realize v then 1 else 0
  | _, _, const s, _, _, _ => s
  | _, _, add s t, A, _, v => s.eval A v + t.eval A v
  | _, _, mul s t, A, _, v => s.eval A v * t.eval A v
  | _, _, sum _ t, A, _, v => ∑ᶠ w : Fin _ → A, t.eval A (Sum.elim v w)
  | _, _, prod _ t, A, _, v => ∏ᶠ w : Fin _ → A, t.eval A (Sum.elim v w)
  | L, _, sosum B t, A, inst, v =>
      ∑ᶠ ρ : B.Assignment A, @eval (L.sum B.lang) _ t A (@sumStructure L _ A inst (B.structure ρ)) v

/-- The value of a closed term. -/
noncomputable def value {L : Language.{0, 0}} (t : SQTerm L Empty) (A : Type) [L.Structure A] : ℕ :=
  t.eval A default

end SQTerm

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **A counting problem is ΣQSO(FO)-definable** when, on nonempty finite
ordered structures, it is the value of a closed term of ΣQSO(FO) over the
ordered expansion, whatever the linear order. -/
def SQDefinable (C : CountingProblem L) : Prop :=
  ∃ t : SQTerm (L.sum Language.order) Empty,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], C A = t.value A

end Lax366625.SecondOrderCounting
