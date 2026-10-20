/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Quantitative
import DescriptiveComplexity.SecondOrderPull

/-!
# Pulling a quantitative term back through an interpretation

A term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`) over the target vocabulary of an
interpretation `I` becomes a term over its source vocabulary, with the same
value: `DescriptiveComplexity.QTerm.pull` and
`DescriptiveComplexity.QTerm.eval_pull`. A formula is pulled back as formulas
are (`DescriptiveComplexity.FOInterpretation.pull`); a sum or a product over
the `n`-tuples of the interpreted universe, which is `Tag × A ^ d`, becomes a
finite sum or product over the assignments of tags to the `n` variables, of a
sum or product over `n · d` elements of `A`.

This is what closes FP under parsimonious reductions
(`DescriptiveComplexity.Counting.FP`), the least fixed point being pulled back
as for PTIME (`DescriptiveComplexity.lfpAssign_pull`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

/-- The sum of a list of terms. -/
def bigAdd : List (QTerm L α) → QTerm L α
  | [] => const 0
  | t :: l => add t (bigAdd l)

/-- The product of a list of terms. -/
def bigMul : List (QTerm L α) → QTerm L α
  | [] => const 1
  | t :: l => mul t (bigMul l)

theorem eval_bigAdd {A : Type} [L.Structure A] (l : List (QTerm L α)) (v : α → A) :
    (bigAdd l).eval v = (l.map fun t => t.eval v).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [bigAdd, eval, ih, List.map_cons, List.sum_cons]

theorem eval_bigMul {A : Type} [L.Structure A] (l : List (QTerm L α)) (v : α → A) :
    (bigMul l).eval v = (l.map fun t => t.eval v).prod := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [bigMul, eval, ih, List.map_cons, List.prod_cons]

end QTerm

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

/-- The pullback of a formula with free variables through an interpretation:
each variable becomes `d` variables, its tag being given. -/
noncomputable def FOInterpretation.pullFormula (I : FOInterpretation L₁ L₂ Tag d) {α : Type}
    (φ : L₂.Formula α) (τ : α → Tag) : L₁.Formula (α × Fin d) :=
  (I.pull (φ : L₂.BoundedFormula α 0) (Sum.elim τ Fin.elim0)).relabel
    fun p : (α ⊕ Fin 0) × Fin d =>
      (Sum.elim (fun a => (a, p.2)) (fun z => z.elim0) p.1 : α × Fin d)

theorem FOInterpretation.realize_pullFormula (I : FOInterpretation L₁ L₂ Tag d) {A : Type}
    [L₁.Structure A] {α : Type} (φ : L₂.Formula α) (τ : α → Tag) (w : α × Fin d → A) :
    (I.pullFormula φ τ).Realize w ↔ φ.Realize (M := I.Map A) (I.liftEnv τ w) := by
  rw [FOInterpretation.pullFormula, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula α 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

/-- The variables of a pulled-back quantifier block: the `d` coordinates of
each of the `n` bound variables, laid out as one block of `n * d`. -/
def blockRelabel {α : Type} {n : ℕ} : (α ⊕ Fin n) × Fin d → (α × Fin d) ⊕ Fin (n * d)
  | (.inl a, j) => .inl (a, j)
  | (.inr i, j) => .inr (finProdFinEquiv (i, j))

/-- **The pullback of a term through an interpretation.** -/
noncomputable def QTerm.pull (I : FOInterpretation L₁ L₂ Tag d) :
    ∀ {α : Type}, QTerm L₂ α → (α → Tag) → QTerm L₁ (α × Fin d)
  | _, .ind φ, τ => .ind (I.pullFormula φ τ)
  | _, .const s, _ => .const s
  | _, .add s t, τ => .add (s.pull I τ) (t.pull I τ)
  | _, .mul s t, τ => .mul (s.pull I τ) (t.pull I τ)
  | _, .sum n t, τ => QTerm.bigAdd ((allTagAssign Tag n).map fun g =>
      .sum (n * d) ((t.pull I (Sum.elim τ g)).relabel blockRelabel))
  | _, .prod n t, τ => QTerm.bigMul ((allTagAssign Tag n).map fun g =>
      .prod (n * d) ((t.pull I (Sum.elim τ g)).relabel blockRelabel))

/-- The tuples of points of the interpreted universe: an assignment of tags,
and one block of coordinates. -/
def blockEquiv (I : FOInterpretation L₁ L₂ Tag d) (A : Type) (n : ℕ) :
    (Fin n → Tag) × (Fin (n * d) → A) ≃ (Fin n → I.Map A) where
  toFun p := fun i => (p.1 i, fun j => p.2 (finProdFinEquiv (i, j)))
  invFun y := (fun i => (y i).1, fun m => (y (finProdFinEquiv.symm m).1).2
    (finProdFinEquiv.symm m).2)
  left_inv p := Prod.ext rfl (funext fun m => by
    change p.2 (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) = p.2 m
    rw [Prod.mk.eta, Equiv.apply_symm_apply])
  right_inv y := funext fun i => Prod.ext rfl (funext fun j => by
    change (y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1).2
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = (y i).2 j
    rw [Equiv.symm_apply_apply])

omit [L₂.IsRelational] [Finite Tag] in
theorem liftEnv_blockRelabel (I : FOInterpretation L₁ L₂ Tag d) {A α : Type} {n : ℕ}
    (τ : α → Tag) (w : α × Fin d → A) (p : (Fin n → Tag) × (Fin (n * d) → A)) :
    I.liftEnv (Sum.elim τ p.1) (Sum.elim w p.2 ∘ blockRelabel) =
      Sum.elim (I.liftEnv τ w) (blockEquiv I A n p) :=
  funext fun x => by cases x <;> rfl

open Classical in
/-- **A pulled-back term has, in the source structure, the value of the term
in the interpreted structure.** -/
theorem QTerm.eval_pull (I : FOInterpretation L₁ L₂ Tag d) {A : Type} [L₁.Structure A]
    [Finite A] {α : Type} (t : QTerm L₂ α) :
    ∀ (τ : α → Tag) (w : α × Fin d → A),
      (t.pull I τ).eval w = t.eval (A := I.Map A) (I.liftEnv τ w) := by
  let : Fintype Tag := Fintype.ofFinite Tag
  let : Fintype A := Fintype.ofFinite A
  have : Finite (I.Map A) := I.map_finite A
  let : Fintype (I.Map A) := Fintype.ofFinite _
  induction t with
  | ind φ =>
    intro τ w
    have h := I.realize_pullFormula φ τ w
    by_cases hφ : φ.Realize (M := I.Map A) (I.liftEnv τ w) <;> simp [QTerm.pull, QTerm.eval, h, hφ]
  | const s => intro τ w; rfl
  | add s t hs ht => intro τ w; simp only [QTerm.pull, QTerm.eval, hs, ht]
  | mul s t hs ht => intro τ w; simp only [QTerm.pull, QTerm.eval, hs, ht]
  | sum n t ht =>
    intro τ w
    simp only [QTerm.pull, QTerm.eval_bigAdd, List.map_map, Function.comp_def, QTerm.eval,
      QTerm.eval_relabel, ht, allTagAssign, finsum_eq_sum_of_fintype]
    rw [Finset.sum_map_toList, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (blockEquiv I A n) _ _ fun p =>
      congrArg t.eval (liftEnv_blockRelabel I τ w p)
  | prod n t ht =>
    intro τ w
    simp only [QTerm.pull, QTerm.eval_bigMul, List.map_map, Function.comp_def, QTerm.eval,
      QTerm.eval_relabel, ht, allTagAssign, finprod_eq_prod_of_fintype]
    rw [Finset.prod_map_toList, ← Fintype.prod_prod_type']
    exact Fintype.prod_equiv (blockEquiv I A n) _ _ fun p =>
      congrArg t.eval (liftEnv_blockRelabel I τ w p)

end Pull

end DescriptiveComplexity
