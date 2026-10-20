/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.KernelPair
import DescriptiveComplexity.SecondOrderMerge
import Mathlib.Algebra.BigOperators.Finprod

/-!
# ΣQSO(FO): quantitative second-order logic with second-order sums

The fragment ΣQSO(FO) of the quantitative second-order logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive]: above a Boolean layer
of first-order formulas, terms denoting natural numbers,

`α ::= φ | s | α + α | α · α | Σx. α | Πx. α | ΣX. α`,

the first-order quantitative terms of `DescriptiveComplexity.QTerm` together
with the **second-order sum** `ΣX. α`, the sum over the relations `X` of the
value of `α` in the structure expanded by `X`
(`DescriptiveComplexity.SQTerm`, `DescriptiveComplexity.SQTerm.eval`). The
second-order product `ΠX` of the full logic QSO is left out: ΣQSO(FO) is the
fragment that captures `#P` over ordered structures, which is
`DescriptiveComplexity.mem_sharpP_iff_sqDefinable`.
-/

namespace DescriptiveComplexity

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

end DescriptiveComplexity
