/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderTransitiveClosure

/-!
# One block instead of two: the doubled block

Plumbing for the hardness discharge of SUCCINCT-REACH
(`DescriptiveComplexity.Problems.SuccinctReach.Hardness`).

A `DescriptiveComplexity.SOTCSpec` states its transition condition as a sentence
over *two successive expansions* by the same block – the current state reads
the first copy, the next state the second. That shape is what makes the
pullback through an interpretation cheap
(`DescriptiveComplexity.SecondOrderTransitiveClosurePull`). The Tseitin encoding, on
the other hand, encodes a kernel over *one* block expansion, giving one
propositional variable per relation variable of that block and tuple. So the
discharge needs the two presentations identified:

* `DescriptiveComplexity.SOBlock.double` is the block with two disjoint copies of
  the original relation variables, whose assignments are pairs of assignments
  (`DescriptiveComplexity.SOBlock.joinAssign`);
* `DescriptiveComplexity.blockPairLHom` renames a sentence over two successive
  expansions into one over the doubled expansion, and
  `DescriptiveComplexity.blockFstLHom` renames a sentence over a single expansion
  into one over the doubled expansion that only mentions the *first* copy –
  which is how the endpoint sentences are put on the same footing as the
  transition sentence, so that the three Tseitin encodings of the discharge
  share one block and hence share their propositional variables for the state.

Both renamings are `FirstOrder.Language.LHom.IsExpansionOn` for the structures
concerned, so they preserve realization; the corresponding statements are
`DescriptiveComplexity.realize_blockPairLHom` and
`DescriptiveComplexity.realize_blockFstLHom`.

A third renaming lives here for the same reason. The Tseitin builders produce
formulas over `L ⊕ order` for a base vocabulary `L`; the discharge instantiates
`L` at an *already ordered* `L₀ ⊕ order`, so their output mentions two copies of
the order symbol, both read by the same linear order.
`DescriptiveComplexity.mergeOrdLHom` merges them, which is what lets the formulas
be used as the defining formulas of an interpretation whose source vocabulary
is `L₀ ⊕ order`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The doubled block -/

section Double

variable {A : Type}

/-- The doubled block: two disjoint copies of a block's relation variables,
the first standing for the current state and the second for the next one. -/
def SOBlock.double (B : SOBlock) : SOBlock where
  ι := B.ι ⊕ B.ι
  arity := Sum.elim B.arity B.arity

/-- The assignment of the doubled block made of two assignments of the
original. -/
def SOBlock.joinAssign (B : SOBlock) (ρ σ : B.Assignment A) : B.double.Assignment A
  | Sum.inl i => ρ i
  | Sum.inr i => σ i

/-- The first component of an assignment of the doubled block. -/
def SOBlock.fstAssign (B : SOBlock) (μ : B.double.Assignment A) : B.Assignment A :=
  fun i => μ (Sum.inl i)

/-- The second component of an assignment of the doubled block. -/
def SOBlock.sndAssign (B : SOBlock) (μ : B.double.Assignment A) : B.Assignment A :=
  fun i => μ (Sum.inr i)

@[simp]
theorem SOBlock.fstAssign_joinAssign (B : SOBlock) (ρ σ : B.Assignment A) :
    B.fstAssign (B.joinAssign ρ σ) = ρ :=
  rfl

@[simp]
theorem SOBlock.sndAssign_joinAssign (B : SOBlock) (ρ σ : B.Assignment A) :
    B.sndAssign (B.joinAssign ρ σ) = σ :=
  rfl

end Double

/-! ### Renaming two successive expansions into the doubled one -/

section PairLHom

variable {L₀ : Language.{0, 0}} (B : SOBlock)

/-- The renaming of two successive expansions by a block into the expansion by
the doubled block: the first copy's symbols become the first copy's, the
second copy's the second's. -/
def blockPairLHom : ((L₀.sum B.lang).sum B.lang) →ᴸ (L₀.sum B.double.lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl s
    | Sum.inl (Sum.inr s) => Sum.inr ⟨Sum.inl s.1, s.2⟩
    | Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

/-- The renaming of a single expansion by a block into the expansion by the
doubled block, landing in the *first* copy. -/
def blockFstLHom : (L₀.sum B.lang) →ᴸ (L₀.sum B.double.lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl g => Sum.inl g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl s => Sum.inl s
    | Sum.inr s => Sum.inr ⟨Sum.inl s.1, s.2⟩

variable {A : Type} [instA : L₀.Structure A]

/-- The pair renaming is an expansion, the two copies being interpreted by the
two components of a joined assignment. -/
theorem blockPairLHom_isExpansionOn (ρ σ : B.Assignment A) :
    @LHom.IsExpansionOn _ _ (blockPairLHom (L₀ := L₀) B) A
      (B.structure₂ ρ σ) (B.double.structure₁ (B.joinAssign ρ σ)) := by
  let := B.structure₂ (L := L₀) ρ σ
  let := B.double.structure₁ (L := L₀) (B.joinAssign ρ σ)
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl g) => rfl
    | Sum.inl (Sum.inr g) => exact g.elim
    | Sum.inr g => exact g.elim
  · match r with
    | Sum.inl (Sum.inl s) => rfl
    | Sum.inl (Sum.inr s) => rfl
    | Sum.inr s => rfl

/-- The first-copy renaming is an expansion. -/
theorem blockFstLHom_isExpansionOn (μ : B.double.Assignment A) :
    @LHom.IsExpansionOn _ _ (blockFstLHom (L₀ := L₀) B) A
      (B.structure₁ (B.fstAssign μ)) (B.double.structure₁ μ) := by
  let := B.structure₁ (L := L₀) (B.fstAssign μ)
  let := B.double.structure₁ (L := L₀) μ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl g => rfl
    | Sum.inr g => exact g.elim
  · match r with
    | Sum.inl s => rfl
    | Sum.inr s => rfl

/-- **The pair renaming preserves realization**: a sentence over two successive
expansions says of a pair of assignments what its renaming says of the joined
assignment. -/
theorem realize_blockPairLHom (ρ σ : B.Assignment A)
    (φ : ((L₀.sum B.lang).sum B.lang).Sentence) :
    @Sentence.Realize _ A (B.double.structure₁ (B.joinAssign ρ σ))
        ((blockPairLHom B).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₂ ρ σ) φ :=
  letI := B.structure₂ (L := L₀) ρ σ
  letI := B.double.structure₁ (L := L₀) (B.joinAssign ρ σ)
  haveI := blockPairLHom_isExpansionOn (L₀ := L₀) B ρ σ
  LHom.realize_onSentence (M := A) (blockPairLHom B) φ

/-- **The first-copy renaming preserves realization**, and in particular the
result does not depend on the second component of the assignment. -/
theorem realize_blockFstLHom (μ : B.double.Assignment A)
    (φ : (L₀.sum B.lang).Sentence) :
    @Sentence.Realize _ A (B.double.structure₁ μ) ((blockFstLHom B).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₁ (B.fstAssign μ)) φ :=
  letI := B.structure₁ (L := L₀) (B.fstAssign μ)
  letI := B.double.structure₁ (L := L₀) μ
  haveI := blockFstLHom_isExpansionOn (L₀ := L₀) B μ
  LHom.realize_onSentence (M := A) (blockFstLHom B) φ

end PairLHom

/-! ### Merging two copies of the order -/

section MergeOrd

variable (L₀ : Language.{0, 0})

/-- The renaming merging the two order symbols of a doubly ordered expansion:
the Tseitin builders add an order to the vocabulary they are given, which here
is already ordered. -/
def mergeOrdLHom : ((L₀.sum Language.order).sum Language.order) →ᴸ (L₀.sum Language.order) where
  onFunction {_} f :=
    match f with
    | Sum.inl g => g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl s => s
    | Sum.inr s => Sum.inr s

variable {L₀} {A : Type} [L₀.Structure A] [LinearOrder A]

/-- Merging the two order symbols is an expansion: both are read by the same
linear order. -/
theorem mergeOrdLHom_isExpansionOn :
    (mergeOrdLHom L₀).IsExpansionOn A := by
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl g => rfl
    | Sum.inr g => exact g.elim
  · match r with
    | Sum.inl s => rfl
    | Sum.inr s => rfl

/-- **Merging the two order symbols preserves realization.** -/
theorem realize_mergeOrdLHom {γ : Type} (φ : ((L₀.sum Language.order).sum Language.order).Formula γ)
    (v : γ → A) : ((mergeOrdLHom L₀).onFormula φ).Realize v ↔ φ.Realize v :=
  haveI := mergeOrdLHom_isExpansionOn (L₀ := L₀) (A := A)
  LHom.realize_onFormula (mergeOrdLHom L₀) φ

end MergeOrd

end DescriptiveComplexity
