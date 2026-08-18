/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Composition

/-!
# Interpreting a vocabulary by formulas on a definable part

A first-order interpretation of this library
(`DescriptiveComplexity.FOInterpretation`) builds its universe out of tagged
`d`-tuples, which is what a reduction needs and what makes composition work. A
translation that only has to read *one* element per point pays for that
packaging without using it: the tags are a single one, the dimension is one, and
every statement carries a `Unit × (Fin 1 → A)` that has to be unwound again.

This file is that translation, stated directly. A
`DescriptiveComplexity.FormulaSubst` gives one formula per relation symbol of
the source vocabulary, on as many free variables as the symbol has arguments;
`DescriptiveComplexity.FormulaSubst.substTo` rewrites a source formula by
substituting them and guarding every quantifier by a **domain formula**, and
`DescriptiveComplexity.FormulaSubst.realize_substTo` says what it is worth: the
image, read in the target structure at points of the definable part, says what
the source formula says of the structure those formulas define on that part.

The definable part is not given as a subtype but as an arbitrary type with an
injection into the target whose range the domain formula defines. That is what
lets a caller take the part to be the object it already has – the universe of an
expansion, say – instead of a subtype it would then have to transport across.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ : Language.{0, 0}} {β : Type}

/-! ### The data -/

/-- **An interpretation of `L₁` by `L₂`-formulas**: one formula per relation
symbol, on as many free variables as the symbol has arguments. -/
structure FormulaSubst (L₁ L₂ : Language.{0, 0}) where
  /-- The formula defining a relation symbol. -/
  rel : ∀ {n : ℕ}, L₁.Relations n → L₂.Formula (Fin n)

namespace FormulaSubst

variable (F : FormulaSubst L₁ L₂) (D : L₂.Formula (Fin 1))

/-- The guard “the last bound variable is in the definable part”. -/
def domGuard (n : ℕ) : L₂.BoundedFormula β (n + 1) :=
  BoundedFormula.relabel (fun _ => Sum.inr (Fin.last n)) D

/-- **The translation**: every atom is replaced by the formula defining its
symbol, and every quantifier is guarded by the domain formula. -/
def substTo [L₁.IsRelational] :
    ∀ {n : ℕ}, L₁.BoundedFormula β n → L₂.BoundedFormula β n
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ => Term.bdEqual (Term.var t₁.varOf) (Term.var t₂.varOf)
  | _, .rel r ts => BoundedFormula.relabel (fun i => (ts i).varOf) (F.rel r)
  | _, .imp φ ψ => (substTo φ).imp (substTo ψ)
  | n, .all φ => .all ((domGuard D n).imp (substTo φ))

/-- The image of a sentence. -/
def substSentence [L₁.IsRelational] (φ : L₁.Sentence) : L₂.Sentence :=
  substTo F D φ

/-! ### The structure the formulas define -/

variable {M Pt : Type} [L₂.Structure M] {e : Pt → M}

/-- **The structure the formulas define on the definable part**: a symbol holds
of a tuple exactly when its formula holds of the elements that tuple names. -/
@[instance_reducible]
def strucOn [L₁.IsRelational] (e : Pt → M) : L₁.Structure Pt where
  funMap f := isEmptyElim f
  RelMap {_} r ts := (F.rel r).Realize fun i => e (ts i)

/-! ### Realization -/

variable {F D}

omit [L₂.Structure M] in
private theorem elim_map {n : ℕ} (v : β → Pt) (xs : Fin n → Pt) (x : β ⊕ Fin n) :
    Sum.elim (fun b => e (v b)) (fun i => e (xs i)) x = e (Sum.elim v xs x) := by
  cases x <;> rfl

theorem realize_domGuard {n : ℕ} (v : β → M) (xs : Fin (n + 1) → M) :
    (domGuard (β := β) D n).Realize v xs ↔ D.Realize ![xs (Fin.last n)] := by
  rw [domGuard, BoundedFormula.realize_relabel]
  refine iff_of_eq (congrArg₂ _ (funext fun i => ?_) (Subsingleton.elim _ _))
  rw [Subsingleton.elim i 0]
  rfl

/-- **The image says of the target structure what the source says of the
definable part**: quantifiers range over the part, and atoms hold as their
formulas say. -/
theorem realize_substTo [L₁.IsRelational] (hinj : Function.Injective e)
    (hD : ∀ x : M, D.Realize ![x] ↔ ∃ p : Pt, e p = x) {n : ℕ}
    (φ : L₁.BoundedFormula β n) (v : β → Pt) (xs : Fin n → Pt) :
    (substTo F D φ).Realize (fun b => e (v b)) (fun i => e (xs i)) ↔
      @BoundedFormula.Realize _ Pt (F.strucOn e) _ _ φ v xs := by
  letI := F.strucOn e
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    change (Sum.elim (fun b => e (v b)) (fun i => e (xs i)) t₁.varOf =
        Sum.elim (fun b => e (v b)) (fun i => e (xs i)) t₂.varOf) ↔ _
    rw [elim_map, elim_map]
    change _ ↔ (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs))
    rw [Term.realize_varOf, Term.realize_varOf]
    exact ⟨fun h => hinj h, fun h => congrArg _ h⟩
  | rel r ts =>
    rw [substTo, BoundedFormula.realize_relabel]
    refine Iff.trans (iff_of_eq (congrArg₂ _ (funext fun i => ?_) (Subsingleton.elim _ _)))
      (Iff.rfl : @Formula.Realize _ M _ _ (F.rel r)
        (fun i => e ((ts i).realize (Sum.elim v xs))) ↔ _)
    change Sum.elim (fun b => e (v b)) (fun i => e (xs i)) (ts i).varOf = _
    rw [elim_map]
    exact congrArg e (Term.realize_varOf (ts i)).symm
  | imp _ _ ih₁ ih₂ =>
    rw [substTo]
    exact imp_congr (ih₁ xs) (ih₂ xs)
  | all _ ih =>
    rw [substTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    have hsnoc : ∀ p : Pt, (Fin.snoc (fun i => e (xs i)) (e p) : Fin _ → M) =
        fun i => e ((Fin.snoc xs p : Fin _ → Pt) i) :=
      fun p => funext fun i => congrFun (Fin.comp_snoc e xs p).symm i
    constructor
    · intro h p
      have hg : (domGuard D _).Realize (fun b => e (v b))
          (Fin.snoc (fun i => e (xs i)) (e p)) := by
        rw [realize_domGuard, Fin.snoc_last]
        exact (hD _).mpr ⟨p, rfl⟩
      have hb := h (e p) hg
      rw [hsnoc p] at hb
      exact (ih (Fin.snoc xs p)).mp hb
    · intro h x hg
      rw [realize_domGuard, Fin.snoc_last] at hg
      obtain ⟨p, rfl⟩ := (hD x).mp hg
      have hb := (ih (Fin.snoc xs p)).mpr (h p)
      rw [← hsnoc p] at hb
      exact hb

/-- The sentence form of
`DescriptiveComplexity.FormulaSubst.realize_substTo`. -/
theorem realize_substSentence [L₁.IsRelational] (hinj : Function.Injective e)
    (hD : ∀ x : M, D.Realize ![x] ↔ ∃ p : Pt, e p = x) (φ : L₁.Sentence) :
    (M ⊨ substSentence F D φ) ↔ @Sentence.Realize _ Pt (F.strucOn e) φ := by
  have h := realize_substTo (F := F) (D := D) (e := e) hinj hD (β := Empty) φ default default
  refine Iff.trans (iff_of_eq (congrArg₂
    (fun (u : Empty → M) (ys : Fin 0 → M) =>
      @BoundedFormula.Realize _ M _ _ 0 (substTo F D φ) u ys)
    (funext fun x => x.elim) (Subsingleton.elim _ _))) h

end FormulaSubst

end DescriptiveComplexity
