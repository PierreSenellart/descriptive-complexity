/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointExpand

/-!
# Eliminating an induction under a quantifier prefix

`DescriptiveComplexity.sigmaSODefinable_of_ifpExpand` removes an inflationary
induction from a `Σ₁` definition. This file does it under a prefix of *any*
length and either polarity
(`DescriptiveComplexity.exists_expand_sorealize`), which is what closes every
level of the polynomial hierarchy – and `PH` itself – under FO(LFP) reductions
(`DescriptiveComplexity.FixedPointReductionHierarchy`).

## Why the prefix is peeled from outside in

The blocks of a second-order prefix quantify relations on *the same universe*
as the induction runs on, so each of them commutes with the expansion: the
outermost quantifier can be pulled out, its block joined to the base
vocabulary, and the rest treated by the same theorem one block shorter. Two
constructions of `DescriptiveComplexity.FixedPointExpand` are what make the
step legal – expanding by the induction's block and by the prefix's block in
either order is the same structure (`DescriptiveComplexity.swapExpand`), and an
induction read over the larger vocabulary computes the same value
(`DescriptiveComplexity.StepDef.inflLimit_liftLang`).

The recursion therefore stops at **one** block, not at none, and that is where
the polarity enters. With one block left the whole formula is “some (or every)
assignment makes an induction-expanded kernel true”; the kernel's problem is in
PTIME, so it is `Σ₁` *and* `Π₁` definable, and the block that replaces the
induction is quantified the same way as the block already there – so the two
merge (`DescriptiveComplexity.SOBlock.cons`) and the level does not rise.
Existentially that is `DescriptiveComplexity.PTIME_subset_NP`, universally
`DescriptiveComplexity.PTIME_subset_coNP`; the parity of the prefix decides
which is used, and nothing else in the argument changes.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Merging the last block with the one that replaces the induction -/

section Merge

variable {L : Language.{0, 0}} {B C : SOBlock} {A : Type}

/-- Two consecutive quantifiers of the same polarity, over two blocks, are one
quantifier over the merged block. -/
theorem sorealize_cons_merge (instA : L.Structure A)
    (ψ : ((L.sum B.lang).sum C.lang).Sentence) (pol : Bool) :
    (@SORealize L A instA [SOBlock.cons B C] ((mergeStep L B C).onSentence ψ) pol) ↔
      quantB pol fun ρ : B.Assignment A =>
        quantB pol fun μ : C.Assignment A =>
          @Sentence.Realize _ A
            (@SOBlock.structure₁ (L.sum B.lang) C A (B.structure₁ (L := L) ρ) μ) ψ := by
  have key : ∀ (ρ : B.Assignment A) (μ : C.Assignment A),
      (@Sentence.Realize _ A
          (@SOBlock.structure₁ L (SOBlock.cons B C) A instA (consAssign ρ μ))
          ((mergeStep L B C).onSentence ψ)) ↔
        @Sentence.Realize _ A
          (@SOBlock.structure₁ (L.sum B.lang) C A (B.structure₁ (L := L) ρ) μ) ψ := by
    intro ρ μ
    let := instA
    let := B.structure ρ
    let := C.structure μ
    let := (SOBlock.cons B C).structure (consAssign ρ μ)
    have := mergeStep_isExpansionOn L instA B C ρ μ
    exact LHom.realize_onSentence (M := A) (φ := mergeStep L B C) (ψ := ψ)
  have hcons : ∀ π : (SOBlock.cons B C).Assignment A,
      consAssign (fun i => π (Sum.inl i)) (fun i => π (Sum.inr i)) = π := by
    intro π
    funext i
    cases i with
    | inl i => rfl
    | inr i => rfl
  cases pol with
  | true =>
    refine Iff.trans ?_ (Iff.refl _)
    constructor
    · rintro ⟨π, hπ⟩
      refine ⟨fun i => π (Sum.inl i), fun i => π (Sum.inr i), (key _ _).mp ?_⟩
      rwa [hcons π]
    · rintro ⟨ρ, μ, h⟩
      exact ⟨consAssign ρ μ, (key ρ μ).mpr h⟩
  | false =>
    refine Iff.trans ?_ (Iff.refl _)
    constructor
    · intro h ρ μ
      exact (key ρ μ).mp (h (consAssign ρ μ))
    · intro h π
      have hπ := (key (fun i => π (Sum.inl i)) (fun i => π (Sum.inr i))).mpr (h _ _)
      rwa [hcons π] at hπ

end Merge

/-! ### Peeling the prefix -/

section Peel

open Classical in
/-- **An induction can be eliminated from a definition with any quantifier
prefix**: a prefix of `n + 1` blocks over the structure expanded by the value
of an induction is a prefix of `n + 1` blocks over the base structure, at the
same polarity.

The blocks are peeled from the outside in: each quantifies relations on the
same universe, so it commutes with the expansion, and the recursion ends at one
block, where the induction is replaced by a quantifier of that block's own
polarity and merged into it. -/
private theorem exists_expand_aux :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (_instRel : L.IsRelational) (d : StepDef L)
      (B : SOBlock) (φ : (soLang (L.sum d.B.lang) (B :: Bs)).Sentence) (pol : Bool),
      ∃ (Bs' : List SOBlock) (φ' : (soLang L Bs').Sentence),
        Bs'.length = Bs.length + 1 ∧
        ∀ (A : Type) (instA : L.Structure A) (_ : Finite A) (_ : Nonempty A),
          (@SORealize (L.sum d.B.lang) A
              (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA))
              (B :: Bs) φ pol ↔
            @SORealize L A instA Bs' φ' pol) := by
  intro Bs
  induction Bs with
  | nil =>
    -- one block left: the induction becomes a quantifier of that block's polarity
    intro L instRel d B φ pol
    let := instRel
    -- the induction, read over the base expanded by the block, with the swapped
    -- kernel as its output: a problem in PTIME
    let dC : StepDef (L.sum B.lang) :=
      { B := (d.liftLang (LHom.sumInl (L' := B.lang))).B
        step := (d.liftLang (LHom.sumInl (L' := B.lang))).step
        out := (swapExpand L d.B B).onSentence φ }
    have hexpB : ∀ (A : Type) (instA : L.Structure A) (ρ : B.Assignment A),
        @LHom.IsExpansionOn L (L.sum B.lang) (LHom.sumInl (L' := B.lang)) A instA
          (@SOBlock.structure₁ L B A instA ρ) := by
      intro A instA ρ
      let := instA
      let := B.structure ρ
      infer_instance
    have hlim : ∀ (A : Type) (instA : L.Structure A) (ρ : B.Assignment A),
        @StepDef.inflLimit (L.sum B.lang) dC A (@SOBlock.structure₁ L B A instA ρ) =
          @StepDef.inflLimit L d A instA :=
      fun A instA ρ => d.inflLimit_liftLang (LHom.sumInl (L' := B.lang)) instA
        (@SOBlock.structure₁ L B A instA ρ) (hexpB A instA ρ)
    let R : DecisionProblem (L.sum B.lang) :=
      { Holds := fun A inst => @StepDef.IFPHolds (L.sum B.lang) dC A inst
        iso_invariant := fun {M N} instM instN e =>
          @StepDef.ifpHolds_equiv (L.sum B.lang) dC M N instM instN e }
    have hRfree : IFPDefinableFree R := ⟨dC, fun A _ _ _ => Iff.rfl⟩
    have hRmem : R ∈ PTIME := (ifpDefinable_iff_mem_PTIME R).mp hRfree.ifpDefinable
    -- the body of the remaining quantifier, at each assignment of the block
    have hbody : ∀ (A : Type) (instA : L.Structure A) (_ : Finite A) (_ : Nonempty A)
        (ρ : B.Assignment A),
        (@Sentence.Realize _ A
            (@SOBlock.structure₁ (L.sum d.B.lang) B A
              (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA)) ρ) φ) ↔
          @DecisionProblem.Holds _ _ R A (@SOBlock.structure₁ L B A instA ρ) := by
      intro A instA _ _ ρ
      refine Iff.symm (Iff.trans ?_ (realize_swapExpand instA
        (@StepDef.inflLimit L d A instA) ρ φ))
      change (@StepDef.IFPHolds (L.sum B.lang) dC A (@SOBlock.structure₁ L B A instA ρ)) ↔ _
      rw [StepDef.IFPHolds, hlim A instA ρ]
      exact Iff.rfl
    cases pol with
    | true =>
      obtain ⟨Cs, hlen, ψ, hψ⟩ := PTIME_subset_NP hRmem
      obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hlen
      refine ⟨[SOBlock.cons B C], (mergeStep L B C).onSentence ψ, rfl, ?_⟩
      intro A instA hfin hne
      refine Iff.trans (exists_congr fun ρ => ?_) (sorealize_cons_merge instA ψ true).symm
      exact (hbody A instA hfin hne ρ).trans
        (@hψ A (@SOBlock.structure₁ L B A instA ρ) hfin hne)
    | false =>
      obtain ⟨Cs, hlen, ψ, hψ⟩ := PTIME_subset_coNP hRmem
      obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hlen
      refine ⟨[SOBlock.cons B C], (mergeStep L B C).onSentence ψ, rfl, ?_⟩
      intro A instA hfin hne
      refine Iff.trans (forall_congr' fun ρ => ?_) (sorealize_cons_merge instA ψ false).symm
      exact (hbody A instA hfin hne ρ).trans
        (@hψ A (@SOBlock.structure₁ L B A instA ρ) hfin hne)
  | cons B₂ Bs ih =>
    -- peel the outermost block and recurse over the enlarged base vocabulary
    intro L instRel d B φ pol
    let := instRel
    obtain ⟨Bs'', φ'', hlen, hiff⟩ :=
      ih (L.sum B.lang) inferInstance (d.liftLang (LHom.sumInl (L' := B.lang))) B₂
        ((soLangLift (B₂ :: Bs) ((L.sum d.B.lang).sum B.lang)
          ((L.sum B.lang).sum d.B.lang) (swapExpand L d.B B)).onSentence φ) (!pol)
    refine ⟨B :: Bs'', φ'', by simp only [List.length_cons, hlen], ?_⟩
    intro A instA hfin hne
    have hstep : ∀ ρ : B.Assignment A,
        (@SORealize ((L.sum d.B.lang).sum B.lang) A
            (@SOBlock.structure₁ (L.sum d.B.lang) B A
              (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA)) ρ)
            (B₂ :: Bs) φ (!pol) ↔
          @SORealize (L.sum B.lang) A (@SOBlock.structure₁ L B A instA ρ) Bs'' φ'' (!pol)) := by
      intro ρ
      have hexpB : @LHom.IsExpansionOn L (L.sum B.lang) (LHom.sumInl (L' := B.lang)) A instA
          (@SOBlock.structure₁ L B A instA ρ) := by
        let := instA
        let := B.structure ρ
        infer_instance
      have hlim := d.inflLimit_liftLang (LHom.sumInl (L' := B.lang)) instA
        (@SOBlock.structure₁ L B A instA ρ) hexpB
      have hswap := sorealize_soLangLift (B₂ :: Bs) ((L.sum d.B.lang).sum B.lang)
        ((L.sum B.lang).sum d.B.lang) (swapExpand L d.B B) A
        (@SOBlock.structure₁ (L.sum d.B.lang) B A
          (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA)) ρ)
        (@SOBlock.structure₁ (L.sum B.lang) d.B A
          (@SOBlock.structure₁ L B A instA ρ) (@StepDef.inflLimit L d A instA))
        (swapExpand_isExpansionOn instA (@StepDef.inflLimit L d A instA) ρ) φ (!pol)
      refine Iff.trans hswap.symm (Iff.trans ?_ (hiff A (@SOBlock.structure₁ L B A instA ρ)
        hfin hne))
      rw [hlim]
      exact Iff.rfl
    cases pol with
    | true => exact exists_congr fun ρ => hstep ρ
    | false => exact forall_congr' fun ρ => hstep ρ

/-- **A `Σ`- or `Π`-definition read over the value of an induction is one over
the base structure**, at the same level and the same polarity. -/
theorem exists_expand_sorealize {L : Language.{0, 0}} [L.IsRelational] (d : StepDef L)
    (Bs : List SOBlock) (hBs : Bs ≠ []) (φ : (soLang (L.sum d.B.lang) Bs).Sentence)
    (pol : Bool) :
    ∃ (Bs' : List SOBlock) (φ' : (soLang L Bs').Sentence),
      Bs'.length = Bs.length ∧
      ∀ (A : Type) (instA : L.Structure A) (_ : Finite A) (_ : Nonempty A),
        (@SORealize (L.sum d.B.lang) A
            (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA))
            Bs φ pol ↔
          @SORealize L A instA Bs' φ' pol) := by
  cases Bs with
  | nil => exact absurd rfl hBs
  | cons B Bs => exact exists_expand_aux Bs L inferInstance d B φ pol

end Peel

end DescriptiveComplexity
