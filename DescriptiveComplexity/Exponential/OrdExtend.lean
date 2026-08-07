/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.OrdFormula

/-!
# Extending an expansion with its own order

`DescriptiveComplexity.ExpExpansion.ordExtend` adds the order symbol to the
expanded vocabulary, defined by the sentence of
`DescriptiveComplexity.Exponential.OrdFormula`, and
`DescriptiveComplexity.ExpExpansion.ordExtendLEquiv` says the result is exactly
the original expansion carrying
`DescriptiveComplexity.ExpExpansion.mapLinearOrder`.

This is the analogue, one level up, of
`DescriptiveComplexity.FOInterpretation.ordExtend` and its `ordExtendLEquiv`,
and it plays the same role: an interpretation whose formulas mention the order
of the structure they read can only be composed with an expansion once that
expansion *defines* its order. It is the missing prerequisite of the outer
composition (`ROADMAP.md` §3), and the only piece of it that is about the order
rather than about quantifiers.

The tag comparison is **static**, exactly as in
`DescriptiveComplexity.lexLeF`: two points with different tags are ordered by
their tags alone, so the defining sentence at such a pair is `⊤` or `⊥`, and
only the equal-tag case emits a real comparison.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-! ### The defining sentence of the order -/

open Classical in
/-- The defining sentence of the order at a pair of tags: the tags are compared
statically, and at equal tags the assignments are compared as binary numbers. -/
noncomputable def ordSentence (t₁ t₂ : X.Tag) :
    ((L.sum Language.order).sum (X.B.replicate 2).lang).Sentence :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  if t₁ = t₂ then X.B.ordLeF L else if t₁ < t₂ then ⊤ else ⊥

variable (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The defining sentence is the order on points.** -/
theorem realize_ordSentence (t₁ t₂ : X.Tag) (ρs : Fin 2 → X.B.Assignment A) :
    (@Sentence.Realize _ A
        ((X.B.replicate 2).structure₁ (L := L.sum Language.order) (X.B.replicateAssign ρs))
        (X.ordSentence t₁ t₂) ↔
      (X.pointLinearOrder A).le (t₁, ρs 0) (t₂, ρs 1)) := by
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  letI := setLinearOrder (X.B.AtomIx A)
  letI := (X.B.replicate 2).structure₁ (L := L.sum Language.order) (X.B.replicateAssign ρs)
  have hle : (X.pointLinearOrder A).le (t₁, ρs 0) (t₂, ρs 1) ↔
      t₁ < t₂ ∨ (t₁ = t₂ ∧
        (setLinearOrder (X.B.AtomIx A)).le (X.B.atomSet (ρs 0)) (X.B.atomSet (ρs 1))) :=
    prodLex_le_iff
  rcases eq_or_ne t₁ t₂ with rfl | hne
  · rw [ordSentence, if_pos rfl, X.B.realize_ordLeF ρs, hle]
    simp
  · rw [ordSentence, if_neg hne, hle]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [if_pos hlt]
      simp only [Sentence.Realize, Formula.realize_top, true_iff]
      exact Or.inl hlt
    · rw [if_neg (not_lt_of_gt hgt)]
      simp only [Sentence.Realize, Formula.realize_bot, false_iff]
      rintro (h | ⟨he, -⟩)
      · exact absurd h (not_lt_of_gt hgt)
      · exact hne he

/-! ### The extended expansion -/

variable {X}

/-- **The expansion extended with its own order**: the tags, the block and the
domain are unchanged, the expanded vocabulary gains the order symbol, and that
symbol is defined by `DescriptiveComplexity.ExpExpansion.ordSentence`. -/
noncomputable def ordExtend : ExpExpansion L where
  Tag := X.Tag
  B := X.B
  E := X.E.sum Language.order
  dom := X.dom
  relSentence {n} r τ :=
    match n, r with
    | _, Sum.inl s => X.relSentence s τ
    | _, Sum.inr .le => X.ordSentence (τ 0) (τ 1)
  dom_nonempty := X.dom_nonempty

variable (X)

omit [Finite A] [Nonempty A] in
/-- The extended expansion has the same universe as the original: same tags,
same block, same domain sentence. -/
theorem ordExtend_map_eq : (ordExtend (X := X)).Map A = X.Map A := rfl

omit [Finite A] [Nonempty A] in
/-- The expanded structure of the order extension, at the vocabulary written as
a sum — equal to the extension's own by definition, but not syntactically, so
instance search has to be handed it. -/
@[instance_reducible]
noncomputable def ordExtendStructure :
    (X.E.sum Language.order).Structure ((ordExtend (X := X)).Map A) :=
  ExpExpansion.mapStructure (ordExtend (X := X)) A

/-- **The extension produces exactly the original expanded structure equipped
with its order**: the identity map is an isomorphism over the order-expanded
vocabulary. -/
noncomputable def ordExtendLEquiv :
    letI := X.mapLinearOrder A
    letI := X.ordExtendStructure A
    (ordExtend (X := X)).Map A ≃[X.E.sum Language.order] X.Map A :=
  letI := X.mapLinearOrder A
  letI := X.ordExtendStructure A
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} r x => by
      cases r with
      | inl s => exact Iff.rfl
      | inr s =>
        cases s with
        | le =>
          exact (X.realize_ordSentence A (x 0).1.1 (x 1).1.1 fun i => (x i).1.2).symm }

end ExpExpansion

end DescriptiveComplexity
