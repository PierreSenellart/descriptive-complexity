/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureDecide
import DescriptiveComplexity.TransitiveClosureParam

/-!
# Every formula over decided relations is decided

The induction that removes first-order structure around walks: if every
relation variable of a block is decided by a
`DescriptiveComplexity.Decider` – at the tuple as parameters – then every
first-order formula over the base vocabulary expanded by the block is decided
by one (`DescriptiveComplexity.Decider.exists_of_formula`), and the decider is
functional when the block's are.

The induction is on `FirstOrder.Language.BoundedFormula`, whose constructors
are exactly the algebra of `DescriptiveComplexity.TransitiveClosureDecide`:
`⊥`, equality and a base relation are atoms, an atom of the block is its
decider with the parameters renamed to the atom's arguments, implication is
`DescriptiveComplexity.Decider.imp`, and `∀` is
`DescriptiveComplexity.Decider.all` with the bound variable frozen.

Stated for a block whose assignment is a *function of the structure*, as the
reachability relations of a family of walks are
(`DescriptiveComplexity.TCFamily.reachAssign`); the deciders of those are
built in `DescriptiveComplexity.TransitiveClosureDecideReach` and
`DescriptiveComplexity.TransitiveClosureDecideReachDet`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Decider

variable {L : Language.{0, 0}} [L.IsRelational] {B : SOBlock}

/-- Realization of a formula over the expansion of the ordered base by a
block, at the assignment the block has on the structure. -/
abbrev ExpRealize (ρ : (A : Type) → [L.Structure A] → [LinearOrder A] → B.Assignment A)
    {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {n : ℕ}
    (φ : ((L.sum Language.order).sum B.lang).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    Prop :=
  @BoundedFormula.Realize _ A (B.structure₁ (L := L.sum Language.order) (ρ A)) _ _ φ v xs

/-- **Every formula over decided relations is decided.** Given, for each
relation variable of the block, a decider of its assignment at the tuple as
parameters, every first-order formula over the expansion has a decider at its
free variables as parameters, functional when the given ones are. -/
theorem exists_of_formula (ρ : (A : Type) → [L.Structure A] → [LinearOrder A] → B.Assignment A)
    (Dq : ∀ q : B.ι, Decider L (Fin (B.arity q)))
    (hD : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (q : B.ι)
      (w : Fin (B.arity q) → A), (Dq q).Decides w (ρ A q w))
    {α : Type} {n : ℕ} (φ : ((L.sum Language.order).sum B.lang).BoundedFormula α n) :
    ∃ D : Decider L (α ⊕ Fin n),
      (∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A)
        (xs : Fin n → A), D.Decides (Sum.elim v xs) (ExpRealize ρ φ v xs)) ∧
      (∀ (A : Type) [L.Structure A] [LinearOrder A],
        (∀ q, (Dq q).Functional A) → D.Functional A) := by
  induction φ with
  | falsum =>
    refine ⟨atom ⊥, fun A _ _ _ _ v xs => ?_, fun A _ _ _ => functional_atom _⟩
    refine (decides_atom _ _).congr ?_
    change (⊥ : (L.sum Language.order).Formula _).Realize _ ↔ False
    exact Formula.realize_bot
  | equal t₁ t₂ =>
    refine ⟨atom (Term.equal (Term.var t₁.varOf) (Term.var t₂.varOf)),
      fun A _ _ _ _ v xs => ?_, fun A _ _ _ => functional_atom _⟩
    let := B.structure₁ (L := L.sum Language.order) (ρ A)
    refine (decides_atom _ _).congr ?_
    change _ ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var, Term.realize_varOf,
      Term.realize_varOf]
  | rel R ts =>
    rcases R with r | ⟨q, hq⟩
    · refine ⟨atom (Relations.formula r fun i => Term.var (ts i).varOf),
        fun A _ _ _ _ v xs => ?_, fun A _ _ _ => functional_atom _⟩
      let := B.structure₁ (L := L.sum Language.order) (ρ A)
      refine (decides_atom _ _).congr ?_
      change _ ↔ RelMap (L := (L.sum Language.order).sum B.lang) (Sum.inl r)
        fun i => (ts i).realize (Sum.elim v xs)
      rw [Formula.realize_rel]
      refine Iff.trans (iff_of_eq (congrArg (RelMap r) (funext fun i => ?_))) Iff.rfl
      rw [Term.realize_var, Term.realize_varOf]
    · refine ⟨(Dq q).relabelPar fun i => (ts (Fin.cast hq i)).varOf,
        fun A _ _ _ _ v xs => ?_, fun A _ _ hf => functional_relabelPar _ _ (hf q)⟩
      let := B.structure₁ (L := L.sum Language.order) (ρ A)
      refine (decides_relabelPar _ _ _ (hD A q _)).congr ?_
      change _ ↔ RelMap (L := (L.sum Language.order).sum B.lang) (Sum.inr ⟨q, hq⟩)
        fun i => (ts i).realize (Sum.elim v xs)
      refine iff_of_eq (congrArg (ρ A q) (funext fun i => ?_))
      change _ = (ts (Fin.cast hq i)).realize (Sum.elim v xs)
      rw [Term.realize_varOf]
      rfl
  | imp φ ψ ihφ ihψ =>
    obtain ⟨D₁, h₁, hf₁⟩ := ihφ
    obtain ⟨D₂, h₂, hf₂⟩ := ihψ
    refine ⟨imp D₁ D₂, fun A _ _ _ _ v xs => ?_,
      fun A _ _ hf => functional_imp D₁ D₂ (hf₁ A hf) (hf₂ A hf)⟩
    exact (decides_imp D₁ D₂ _ (h₁ A v xs) (h₂ A v xs)).congr (by simp [ExpRealize])
  | all φ ih =>
    obtain ⟨D, h, hf⟩ := ih
    refine ⟨(D.relabelPar (snocVar α _)).all, fun A _ _ _ _ v xs => ?_,
      fun A _ _ hfq => functional_all _ (functional_relabelPar _ _ (hf A hfq))⟩
    refine (decides_all _ _ (P := fun a => ExpRealize ρ φ v (Fin.snoc xs a)) fun a =>
      decides_relabelPar D _ _ ((h A v (Fin.snoc xs a)).congr_val (funext fun i => ?_))).congr ?_
    · rcases i with i | i
      · rfl
      · induction i using Fin.lastCases with
        | last => simp [snocVar, vy]
        | cast j => simp [snocVar, vy]
    · simp only [ExpRealize, BoundedFormula.realize_all]

end Decider

end DescriptiveComplexity
