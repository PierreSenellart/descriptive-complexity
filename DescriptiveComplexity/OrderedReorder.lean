/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.Numbers.BinRel

/-!
# Replacing the order of an ordered structure by a definable one

An ordered reduction is correct for *every* linear order of its input, which
it has no say over. What it may do is replace that order, before anything
else, by any linear order it can define: `DescriptiveComplexity.FOInterpretation.reorder`
is the one-dimensional interpretation of the ordered expansion in itself that
keeps every symbol and interprets the order symbol by a given formula, and
`DescriptiveComplexity.FOInterpretation.reorderLEquiv` says that, when the
formula defines a linear order `ord'` of the structure, the interpreted
structure is the input structure ordered by `ord'`.

This is how a reduction into a problem that reads its output in the order of
the universe – the tape order of `DescriptiveComplexity.DTMNumber` – can be
composed after one that produces the order of significance as a relation of
the instance: the second reduction reorders its input so that the two agree.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Reordering**: the identity interpretation of the ordered expansion in
itself, with the order symbol interpreted by the formula `φ` (its two free
variables being the two arguments). -/
noncomputable def FOInterpretation.reorder (φ : (L.sum Language.order).Formula (Fin 2 × Fin 1)) :
    FOInterpretation (L.sum Language.order) (L.sum Language.order) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => fun _ => Relations.formula (Sum.inl r) fun i => Term.var (i, 0)
    | _, Sum.inr .le => fun _ => φ

variable (φ : (L.sum Language.order).Formula (Fin 2 × Fin 1))
variable (A : Type) [L.Structure A] [LinearOrder A]

/-- When `φ` defines a relation `Le'` that is a linear order, the reordered
structure is the input structure ordered by `Le'`
(`DescriptiveComplexity.IsLinOrd.toLinearOrder`). The new order is passed as
a relation rather than as a `LinearOrder` so that it does not shadow the
order of the input in the statement. -/
noncomputable def FOInterpretation.reorderLEquiv {Le' : A → A → Prop} (h : IsLinOrd Le')
    (hφ : ∀ v : Fin 2 × Fin 1 → A, φ.Realize v ↔ Le' (v (0, 0)) (v (1, 0))) :
    @Language.Equiv (L.sum Language.order) ((FOInterpretation.reorder φ).Map A) A
      (FOInterpretation.mapStructure (FOInterpretation.reorder φ) A)
      (letI := h.toLinearOrder; sumOrderStructure L A) :=
  @Language.Equiv.mk (L.sum Language.order) _ A
    (FOInterpretation.mapStructure (FOInterpretation.reorder φ) A)
    (letI := h.toLinearOrder; sumOrderStructure L A)
    { toFun := fun x => x.2 0
      invFun := fun a => ((), fun _ => a)
      left_inv := fun x =>
        Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
      right_inv := fun _ => rfl }
    (fun f => isEmptyElim f)
    fun {n} R x => by
      cases R with
      | inl r => exact Iff.rfl
      | inr r =>
        cases r with
        | le =>
          change Le' _ _ ↔ ((FOInterpretation.reorder φ).relFormula (Sum.inr .le)
            fun i => (x i).1).Realize fun p => (x p.1).2 p.2
          exact (hφ fun p => (x p.1).2 p.2).symm

end DescriptiveComplexity
