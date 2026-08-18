/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Composition
import DescriptiveComplexity.Relativize

/-!
# Vocabulary maps with parameters

An `FirstOrder.Language.LHom` renames relation symbols and keeps their arity, so
it cannot express “read this symbol at a value the formula holds in a variable”.
That is exactly what a formula has to do when a second-order variable stands for
a *family* of relations, indexed by the elements of the structure: the family is
one relation of arity one more, and the index is a free variable of the formula,
not an argument of the symbol.

This file is that map. A `DescriptiveComplexity.ParamHom` sends each relation
symbol of the source vocabulary to a symbol of the target of a possibly
different arity, together with a reading of each of its arguments: either one of
the source symbol's own arguments, named by its index, or a **parameter**
variable. The induced map on formulas
(`DescriptiveComplexity.ParamHom.onBoundedFormula`) rewrites every atom that way
and leaves everything else alone. Its
realization (`DescriptiveComplexity.ParamHom.realize_onBoundedFormula`) is the
expected one: reading the image in a target structure is reading the source
formula in the source structure whose symbols are the target's, read at the
parameters' values.

A symbol whose arguments are its own, in order, is the ordinary renaming, so a
`ParamHom` covers an `LHom` as the degenerate case and a translation may mix the
two – which is what its use needs, the base vocabulary passing through untouched
while the block symbols pick up an index. Arguments may also be permuted or
repeated; nothing here needs that, but nothing rules it out either.

The source vocabulary must be relational (as all of this library's are): a
parameter is a variable, and there is no term to substitute it into.

## Reading among the marked elements

The use this was written for reads the source sentence in *part* of the target
structure – the original elements of an extended universe – while the
parameters are the invented values, which are outside that part. So
`DescriptiveComplexity.relativizeTo` cannot be applied on its own: its
correctness moves the whole formula into a substructure, and an atom holding a
parameter has no reading there. The second half of this file is the two steps
taken together (`DescriptiveComplexity.ParamHom.realize_relOnSentenceF`): the
quantifiers are guarded by the marker, and the source structure is read on the
marked elements, at symbols that still mention the parameters.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ : Language.{0, 0}} {α β : Type}

/-! ### The data -/

/-- **A map of vocabularies with parameters**: each relation symbol of `L₁`
becomes a symbol of `L₂` of a possibly different arity, each of whose arguments
is either one of the symbol's own – named by its index – or a **parameter**
variable drawn from `α`. -/
structure ParamHom (L₁ L₂ : Language.{0, 0}) (α : Type) where
  /-- The arity of the target symbol. -/
  ar : ∀ {k : ℕ}, L₁.Relations k → ℕ
  /-- The target symbol. -/
  sym : ∀ {k : ℕ} (r : L₁.Relations k), L₂.Relations (ar r)
  /-- What each argument of the target symbol is: an argument of the source
  symbol, by index, or a parameter variable. -/
  args : ∀ {k : ℕ} (r : L₁.Relations k), Fin (ar r) → Fin k ⊕ α

namespace ParamHom

variable (F : ParamHom L₁ L₂ α)

/-- Renaming a variable of the source formula: the source's own free variables
sit on the left of the target's, the parameters on the right. -/
private def shift {n : ℕ} : β ⊕ Fin n → (β ⊕ α) ⊕ Fin n :=
  Sum.map Sum.inl id

/-! ### The map on formulas -/

/-- **The induced map on formulas**: each atom is rewritten symbol and
arguments, and nothing else changes. -/
def onBoundedFormula [L₁.IsRelational] (F : ParamHom L₁ L₂ α) :
    ∀ {n : ℕ}, L₁.BoundedFormula β n → L₂.BoundedFormula (β ⊕ α) n
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ =>
      Term.bdEqual (Term.var (shift t₁.varOf)) (Term.var (shift t₂.varOf))
  | _, .rel r ts =>
      Relations.boundedFormula (F.sym r) fun i =>
        Term.var (Sum.elim (fun j => shift (ts j).varOf)
          (fun a => Sum.inl (Sum.inr a)) (F.args r i))
  | _, .imp φ ψ => (onBoundedFormula F φ).imp (onBoundedFormula F ψ)
  | _, .all φ => (onBoundedFormula F φ).all

/-- The image of a sentence: a formula on the parameters. -/
def onSentenceF [L₁.IsRelational] (φ : L₁.Sentence) : L₂.Formula α :=
  Formula.relabel (Sum.elim (fun e : Empty => e.elim) id) (onBoundedFormula (β := Empty) F φ)

/-! ### The source structure a target structure induces -/

variable (M : Type) [L₂.Structure M] (w : α → M)

/-- **The source structure read at the parameters**: a symbol of `L₁` holds of a
tuple exactly when its image holds of that tuple and the parameters' values,
each argument taken where the map says. -/
@[instance_reducible]
def struc [L₁.IsRelational] : L₁.Structure M where
  funMap f := isEmptyElim f
  RelMap {_} r ts := RelMap (F.sym r) fun i => Sum.elim ts w (F.args r i)

theorem relMap_struc [L₁.IsRelational] {k : ℕ} (r : L₁.Relations k) (ts : Fin k → M) :
    @RelMap _ M (F.struc M w) _ r ts ↔
      RelMap (F.sym r) fun i => Sum.elim ts w (F.args r i) :=
  Iff.rfl

/-! ### Realization -/

variable {M w}

omit [L₂.Structure M] in
private theorem realize_shift {n : ℕ} (v : β → M) (xs : Fin n → M) (x : β ⊕ Fin n) :
    Sum.elim (Sum.elim v w) xs (shift x) = Sum.elim v xs x := by
  cases x <;> rfl

/-- **The image says of the target structure what the source said of the induced
one.** -/
theorem realize_onBoundedFormula [L₁.IsRelational] {n : ℕ} (φ : L₁.BoundedFormula β n)
    (v : β → M) (xs : Fin n → M) :
    (onBoundedFormula F φ).Realize (Sum.elim v w) xs ↔
      @BoundedFormula.Realize _ M (F.struc M w) _ _ φ v xs := by
  letI := F.struc M w
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    change (Sum.elim (Sum.elim v w) xs (shift t₁.varOf) =
        Sum.elim (Sum.elim v w) xs (shift t₂.varOf)) ↔
      (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs))
    rw [realize_shift, realize_shift, Term.realize_varOf, Term.realize_varOf]
  | rel r ts =>
    have harg : (fun i => Term.realize (Sum.elim (Sum.elim v w) xs)
          ((Term.var (Sum.elim (fun j => shift (ts j).varOf)
            (fun a => Sum.inl (Sum.inr a)) (F.args r i))) : L₂.Term _)) =
        fun i => Sum.elim (fun j => (ts j).realize (Sum.elim v xs)) w (F.args r i) := by
      funext i
      cases h : F.args r i with
      | inl j =>
        change Sum.elim (Sum.elim v w) xs (shift (ts j).varOf) = _
        rw [realize_shift]
        exact (Term.realize_varOf (ts j)).symm
      | inr _ => rfl
    exact iff_of_eq (congrArg (fun f => @RelMap _ M _ _ (F.sym r) f) harg)
  | imp _ _ ih₁ ih₂ =>
    rw [onBoundedFormula]
    exact imp_congr (ih₁ xs) (ih₂ xs)
  | all _ ih =>
    rw [onBoundedFormula, BoundedFormula.realize_all, BoundedFormula.realize_all]
    exact forall_congr' fun a => ih _

/-- The formula form of `DescriptiveComplexity.ParamHom.realize_onBoundedFormula`. -/
theorem realize_onFormula [L₁.IsRelational] (φ : L₁.Formula β) (v : β → M) :
    Formula.Realize (onBoundedFormula F φ) (Sum.elim v w) ↔
      @Formula.Realize _ M (F.struc M w) _ φ v :=
  realize_onBoundedFormula F φ v default

/-- The sentence form of `DescriptiveComplexity.ParamHom.realize_onBoundedFormula`. -/
theorem realize_onSentenceF [L₁.IsRelational] (φ : L₁.Sentence) :
    (F.onSentenceF φ).Realize w ↔ @Sentence.Realize _ M (F.struc M w) φ := by
  have h : (Formula.relabel (Sum.elim (fun e : Empty => e.elim) id)
        (onBoundedFormula (β := Empty) F φ)).Realize w ↔
      Formula.Realize (onBoundedFormula (β := Empty) F φ)
        (Sum.elim (default : Empty → M) w) := by
    rw [Formula.realize_relabel]
    refine iff_of_eq (congrArg (Formula.Realize _) (funext fun x => ?_))
    cases x with
    | inl e => exact e.elim
    | inr a => rfl
  exact h.trans (realize_onFormula (β := Empty) F φ default)

/-! ### Reading among the marked elements

The parameters are values of the target structure that the marked part need not
contain, so the image of a source sentence is read at *guarded* quantifiers
rather than moved into a substructure. -/

section Marked

variable [L₁.IsRelational] (F : ParamHom L₁ L₂ α) (R : L₂.Relations 1)
variable {M : Type} [L₂.Structure M] {w : α → M} {A : Type} {e : A → M}

/-- The source structure on the marked part: a symbol holds of a tuple of marked
elements exactly when its image holds of the parameters' values followed by that
tuple. -/
@[instance_reducible]
def strucOn (e : A → M) (w : α → M) : L₁.Structure A where
  funMap f := isEmptyElim f
  RelMap {_} r ts :=
    RelMap (F.sym r) fun i => Sum.elim (fun j => e (ts j)) w (F.args r i)

/-- **The image, relativized, says of the marked part what the source said**:
every quantifier is guarded by the marker, and every symbol is read through the
parameters. -/
theorem realize_relOnBoundedFormula (hinj : Function.Injective e)
    (hR : ∀ x : M, RelMap R ![x] ↔ ∃ a : A, e a = x) {n : ℕ}
    (φ : L₁.BoundedFormula β n) (v : β → A) (xs : Fin n → A) :
    (relativizeTo R (onBoundedFormula F φ)).Realize (Sum.elim (fun b => e (v b)) w)
        (fun i => e (xs i)) ↔
      @BoundedFormula.Realize _ A (F.strucOn e w) _ _ φ v xs := by
  letI := F.strucOn e w
  have helim : ∀ {k : ℕ} (ys : Fin k → A) (x : β ⊕ Fin k),
      Sum.elim (fun b => e (v b)) (fun i => e (ys i)) x = e (Sum.elim v ys x) := by
    intro k ys x
    cases x <;> rfl
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    change (Sum.elim (Sum.elim (fun b => e (v b)) w) (fun i => e (xs i)) (shift t₁.varOf) =
        Sum.elim (Sum.elim (fun b => e (v b)) w) (fun i => e (xs i)) (shift t₂.varOf)) ↔ _
    rw [realize_shift, realize_shift, helim, helim]
    change _ ↔ (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs))
    rw [Term.realize_varOf, Term.realize_varOf]
    exact ⟨fun h => hinj h, fun h => congrArg _ h⟩
  | rel r ts =>
    have harg : (fun i => Term.realize
          (Sum.elim (Sum.elim (fun b => e (v b)) w) (fun i => e (xs i)))
          ((Term.var (Sum.elim (fun j => shift (ts j).varOf)
            (fun a => Sum.inl (Sum.inr a)) (F.args r i))) : L₂.Term _)) =
        fun i => Sum.elim (fun j => e ((ts j).realize (Sum.elim v xs))) w (F.args r i) := by
      funext i
      cases h : F.args r i with
      | inl j =>
        change Sum.elim (Sum.elim (fun b => e (v b)) w) (fun i => e (xs i))
          (shift (ts j).varOf) = _
        rw [realize_shift, helim]
        exact congrArg e (Term.realize_varOf (ts j)).symm
      | inr _ => rfl
    exact iff_of_eq (congrArg (fun f => @RelMap _ M _ _ (F.sym r) f) harg)
  | imp _ _ ih₁ ih₂ =>
    rw [onBoundedFormula, relativizeTo]
    exact imp_congr (ih₁ xs) (ih₂ xs)
  | all _ ih =>
    rw [onBoundedFormula, relativizeTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    have hsnoc : ∀ a : A, (Fin.snoc (fun i => e (xs i)) (e a) : Fin _ → M) =
        fun i => e ((Fin.snoc xs a : Fin _ → A) i) :=
      fun a => funext fun i => congrFun (Fin.comp_snoc e xs a).symm i
    constructor
    · intro h a
      have hg : (lastGuard R _).Realize (Sum.elim (fun b => e (v b)) w)
          (Fin.snoc (fun i => e (xs i)) (e a)) := by
        rw [realize_lastGuard, Fin.snoc_last]
        exact (hR _).mpr ⟨a, rfl⟩
      have hb := h (e a) hg
      rw [hsnoc a] at hb
      exact (ih (Fin.snoc xs a)).mp hb
    · intro h x hg
      rw [realize_lastGuard, Fin.snoc_last] at hg
      obtain ⟨a, rfl⟩ := (hR x).mp hg
      have hb := (ih (Fin.snoc xs a)).mpr (h a)
      rw [← hsnoc a] at hb
      exact hb

/-- **The image of a sentence, read among the marked elements**: a formula on
the parameters. -/
def relOnSentenceF (φ : L₁.Sentence) : L₂.Formula α :=
  Formula.relabel (Sum.elim (fun e : Empty => e.elim) id)
    (relativizeTo R (onBoundedFormula (β := Empty) F φ))

/-- The sentence form of
`DescriptiveComplexity.ParamHom.realize_relOnBoundedFormula`. -/
theorem realize_relOnSentenceF (hinj : Function.Injective e)
    (hR : ∀ x : M, RelMap R ![x] ↔ ∃ a : A, e a = x) (φ : L₁.Sentence) :
    (F.relOnSentenceF R φ).Realize w ↔ @Sentence.Realize _ A (F.strucOn e w) φ := by
  have h := realize_relOnBoundedFormula (w := w) F R hinj hR (β := Empty) φ default default
  rw [relOnSentenceF, Formula.realize_relabel]
  refine Iff.trans (iff_of_eq (congrArg₂
    (fun u (ys : Fin 0 → M) => @BoundedFormula.Realize _ M _ _ 0
      (relativizeTo R (onBoundedFormula (β := Empty) F φ)) u ys)
    (funext fun x => ?_) (Subsingleton.elim _ _))) h
  cases x with
  | inl b => exact b.elim
  | inr a => rfl

end Marked


end ParamHom

end DescriptiveComplexity
