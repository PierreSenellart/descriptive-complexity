/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Block

/-!
# Writing an expansion's sentences with iterated block expansions

An exponential expansion defines an `n`-ary symbol by a sentence over the base
vocabulary expanded by `DescriptiveComplexity.SOBlock.replicate` – *one* block
holding `n` copies. The rest of the library writes its multi-state sentences
over *iterated* expansions instead: one copy of `B.lang` per state, stacked as
nested sums (`DescriptiveComplexity.SOBlock.structure₁`,
`DescriptiveComplexity.SOBlock.structure₂` – the shape of an
`DescriptiveComplexity.SOTCSpec`).

This file bridges the two presentations at the arities an expansion actually
needs, one and two:

* `DescriptiveComplexity.SOBlock.oneLHom` reads a sentence over `L ⊕ B.lang`
  inside `L ⊕ (B.replicate 1).lang`;
* `DescriptiveComplexity.SOBlock.twoLHom` reads a sentence over
  `(L ⊕ B.lang) ⊕ B.lang` inside `L ⊕ (B.replicate 2).lang`, the first copy
  becoming copy `0` and the second copy `1`.

Both transports are definitional on assignments – reading copy `k` of a
replicated assignment *is* reading the `k`-th assignment – so their correctness
lemmas are `DescriptiveComplexity.SOBlock.realize_homSentence` and one
`LHom.IsExpansionOn` whose relation case is `rfl`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : SOBlock)

/-! ### One copy -/

variable (L) in
/-- Reading a sentence over one copy of a block inside the block replicated
once. -/
def oneLHom : (L.sum B.lang) →ᴸ (L.sum (B.replicate 1).lang) :=
  LHom.sumMap (LHom.id L) (homLHom (fun i => ((0 : Fin 1), i)) fun _ => rfl)

variable {A : Type} [L.Structure A]

/-- **Correctness of the one-copy reading**: the replicated assignment holds
the original assignment in its single copy. -/
theorem realize_oneLHom (ρs : Fin 1 → B.Assignment A) (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize _ A ((B.replicate 1).structure₁ (L := L) (B.replicateAssign ρs))
        ((B.oneLHom L).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) (ρs 0)) φ :=
  realize_homSentence (B := B) (B' := B.replicate 1) (fun i => ((0 : Fin 1), i)) (fun _ => rfl)
    (B.replicateAssign ρs) φ

/-! ### Two copies -/

variable (L) in
/-- Reading a sentence over two stacked copies of a block inside the block
replicated twice: the inner copy becomes copy `0`, the outer copy `1`. -/
def twoLHom : ((L.sum B.lang).sum B.lang) →ᴸ (L.sum (B.replicate 2).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl s
    | Sum.inl (Sum.inr s) => Sum.inr (B.replicateSym 0 s)
    | Sum.inr s => Sum.inr (B.replicateSym 1 s)

/-- The two-copy reading is an expansion between the stacked structure and the
replicated one. Stated at a *family* of two assignments rather than at a pair,
since that is the shape a defining sentence of an expansion is realized
against. -/
theorem twoLHom_isExpansionOn (ρs : Fin 2 → B.Assignment A) :
    @LHom.IsExpansionOn _ _ (B.twoLHom L) A (B.structure₂ (L := L) (ρs 0) (ρs 1))
      ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)) := by
  letI := B.structure₂ (L := L) (ρs 0) (ρs 1)
  letI := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  refine ⟨fun {_} f _ => ?_, fun {_} r _ => ?_⟩
  · match f with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl

/-- **Correctness of the two-copy reading**: the replicated assignment holds
the current state in copy `0` and the next one in copy `1`. -/
theorem realize_twoLHom (ρs : Fin 2 → B.Assignment A)
    (φ : ((L.sum B.lang).sum B.lang).Sentence) :
    @Sentence.Realize _ A ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs))
        ((B.twoLHom L).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₂ (L := L) (ρs 0) (ρs 1)) φ :=
  letI := B.structure₂ (L := L) (ρs 0) (ρs 1)
  letI := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  haveI := B.twoLHom_isExpansionOn (L := L) ρs
  LHom.realize_onSentence (M := A) (B.twoLHom L) φ

/-! ### Two copies, the other way

`DescriptiveComplexity.SOBlock.twoLHom` reads a *stacked* sentence inside a
replicated one, which is what an expansion's defining sentence needs. A walk
over an expanded universe needs the converse: an
`DescriptiveComplexity.SOTCSpec` states its transition over two stacked copies
of its state block, while everything said about two points of an expanded
universe — their order, their equality, one being the successor of the other —
is written over the block replicated twice. -/

variable (L) in
/-- Reading a sentence over a block replicated twice inside two *stacked*
copies: copy `0` becomes the inner copy, copy `1` the outer. -/
def twoLHom' : (L.sum (B.replicate 2).lang) →ᴸ ((L.sum B.lang).sum B.lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s =>
        if s.1.1 = 0 then Sum.inl (Sum.inr ⟨s.1.2, s.2⟩) else Sum.inr ⟨s.1.2, s.2⟩

theorem twoLHom'_isExpansionOn (ρs : Fin 2 → B.Assignment A) :
    @LHom.IsExpansionOn _ _ (B.twoLHom' L) A
      ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs))
      (B.structure₂ (L := L) (ρs 0) (ρs 1)) := by
  letI := B.structure₂ (L := L) (ρs 0) (ρs 1)
  letI := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  refine ⟨fun {_} f _ => ?_, fun {_} r x => ?_⟩
  · match f with
    | Sum.inl _ => rfl
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl _ => rfl
    | Sum.inr s =>
      obtain ⟨⟨⟨cv, hcv⟩, i⟩, hs⟩ := s
      simp only [twoLHom']
      rcases cv with _ | _ | cv
      · rfl
      · rfl
      · omega

/-- **Correctness of the reversed reading**: the stacked structure holds copy
`0` in its inner copy and copy `1` in its outer one. -/
theorem realize_twoLHom' (ρs : Fin 2 → B.Assignment A)
    (φ : (L.sum (B.replicate 2).lang).Sentence) :
    @Sentence.Realize _ A (B.structure₂ (L := L) (ρs 0) (ρs 1))
        ((B.twoLHom' L).onSentence φ) ↔
      @Sentence.Realize _ A ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)) φ :=
  letI := B.structure₂ (L := L) (ρs 0) (ρs 1)
  letI := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  haveI := B.twoLHom'_isExpansionOn (L := L) ρs
  LHom.realize_onSentence (M := A) (B.twoLHom' L) φ

end SOBlock

end DescriptiveComplexity
