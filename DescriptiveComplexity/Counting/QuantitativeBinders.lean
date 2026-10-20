/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Quantitative

/-!
# Writing quantitative terms

Helpers for writing a term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`) the way it is read, and for evaluating it.

A quantifier of `DescriptiveComplexity.QTerm` binds a block of variables,
named by position in a sum type. `DescriptiveComplexity.QTerm.sumOver` and
`DescriptiveComplexity.QTerm.prodOver` bind *one* variable and hand it to the
body by name: the body is a function of the bound variable, and of the way the
variables already in scope are read under the binder. So
`sumOver fun up x => f (up y) x` is `Σx. f(y, x)`, and its value is a sum over
the elements (`DescriptiveComplexity.QTerm.eval_sumOver`).

`DescriptiveComplexity.QTerm.cond` is the choice between two terms by a
formula.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

/-- `Σx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) : QTerm L γ :=
  .sum 1 (f Sum.inl (Sum.inr 0))

/-- `Πx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) : QTerm L γ :=
  .prod 1 (f Sum.inl (Sum.inr 0))

/-- The choice between two terms: `s` where the formula holds, `t` where it
does not. -/
def cond (φ : L.Formula γ) (s t : QTerm L γ) : QTerm L γ :=
  .add (.mul (.ind φ) s) (.mul (.ind ∼φ) t)

variable {A : Type} [L.Structure A]

theorem eval_sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) (v : γ → A) :
    (sumOver f).eval v =
      ∑ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finsum_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm

theorem eval_prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → QTerm L δ) (v : γ → A) :
    (prodOver f).eval v =
      ∏ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finprod_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm

open Classical in
theorem eval_cond (φ : L.Formula γ) (s t : QTerm L γ) (v : γ → A) :
    (cond φ s t).eval v = if φ.Realize v then s.eval v else t.eval v := by
  by_cases h : φ.Realize v <;> simp [cond, eval, h]

open Classical in
theorem eval_ind (φ : L.Formula γ) (v : γ → A) :
    (ind φ : QTerm L γ).eval v = if φ.Realize v then 1 else 0 :=
  rfl

theorem eval_mul (s t : QTerm L γ) (v : γ → A) : (mul s t).eval v = s.eval v * t.eval v :=
  rfl

theorem eval_add (s t : QTerm L γ) (v : γ → A) : (add s t).eval v = s.eval v + t.eval v :=
  rfl

theorem eval_const (n : ℕ) (v : γ → A) : (const n : QTerm L γ).eval v = n :=
  rfl

end QTerm

end DescriptiveComplexity
