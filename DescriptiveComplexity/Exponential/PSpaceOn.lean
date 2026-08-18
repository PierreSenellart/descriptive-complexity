/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Translate
import DescriptiveComplexity.PSpaceHierarchy

/-!
# Every first-order property of an expansion is in the polynomial hierarchy

The immediate payoff of the translation lemma
(`DescriptiveComplexity.ExpExpansion.exists_translate`), and the first check on
`DescriptiveComplexity.ExpExpansion` in the direction nothing else tests:
the other checks on the operator validate it *from below*
(`PSPACE ⊆ NL.exp ⊆ EXPTIME`), while this bounds it from above. A property of
the expanded universe that a first-order sentence can express is not
exponentially hard: it is `Σₖ` over the base, hence in `PH`, hence in `PSPACE`.

Two steps, both off the shelf once the translation is available.

* The translated sentence is second-order over the **ordered** base – the
  expansion's own discipline, “the sentences see the order, the problem does
  not”. `DescriptiveComplexity.sigmaSODefinable_of_orderPull` re-quantifies the
  order inside the first block, which is legitimate here because the hypothesis
  holds for *every* linear order on the instance, so “for some” and “for every”
  agree.
* The prefix is padded by one trivial block
  (`DescriptiveComplexity.sorealize_append_trivial`), so that it has a first
  block to carry the order variable even when the sentence has no quantifiers
  at all.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} [L.IsRelational] (X : ExpExpansion L)
variable (φ : (X.E.sum Language.order).Sentence) (P : DecisionProblem L)

/-- **A first-order property of an exponential expansion is in `PH`.** The
quantifiers of the sentence become second-order quantifier blocks over the base
(`DescriptiveComplexity.ExpExpansion.exists_translate`), two per quantifier, and
the order the expansion's sentences read is guessed inside the first block. -/
theorem mem_PH_of_fo_on_expansion
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      letI := X.mapLinearOrder A
      (P A ↔ @Sentence.Realize _ (X.Map A) _ φ)) :
    P ∈ PH := by
  obtain ⟨Bs, ψ, pol, hB⟩ := exists_translate X φ
  have hkey : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A] (lo : LinearOrder A),
      letI := lo
      (P A ↔ SORealize (L.sum Language.order) A Bs ψ pol) := by
    intro A _ _ _ lo
    let := lo
    exact (h A).trans (hB A)
  cases pol with
  | true =>
    refine sigmaP_subset_PH (Bs.length + 1) (P := P) ?_
    refine sigmaSODefinable_of_orderPull (k := Bs.length) (Bs ++ [SOBlock.trivial])
      (by simp) ((soLangAppendOne SOBlock.trivial (L.sum Language.order) Bs).onSentence ψ) ?_
    intro A _ _ _
    constructor
    · intro hP
      let := finiteLinearOrder A
      exact ⟨finiteLinearOrder A,
        (sorealize_append_trivial Bs (L.sum Language.order) A inferInstance ψ true).mpr
          ((hkey A (finiteLinearOrder A)).mp hP)⟩
    · rintro ⟨lo, hlo⟩
      let := lo
      exact (hkey A lo).mpr
        ((sorealize_append_trivial Bs (L.sum Language.order) A inferInstance ψ true).mp hlo)
  | false =>
    refine piP_subset_PH Bs.length (P := P) ?_
    refine piSODefinable_of_orderPull (k := Bs.length) (Bs ++ [SOBlock.trivial])
      (by simp) ((soLangAppendOne SOBlock.trivial (L.sum Language.order) Bs).onSentence ψ) ?_
    intro A _ _ _
    constructor
    · intro hP lo
      let := lo
      exact (sorealize_append_trivial Bs (L.sum Language.order) A inferInstance ψ false).mpr
        ((hkey A lo).mp hP)
    · intro hall
      let := finiteLinearOrder A
      exact (hkey A (finiteLinearOrder A)).mpr
        ((sorealize_append_trivial Bs (L.sum Language.order) A inferInstance ψ false).mp
          (hall (finiteLinearOrder A)))

/-- **A first-order property of an exponential expansion is in `PSPACE`.** -/
theorem mem_PSPACE_of_fo_on_expansion
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      letI := X.mapLinearOrder A
      (P A ↔ @Sentence.Realize _ (X.Map A) _ φ)) :
    P ∈ PSPACE :=
  PH_subset_PSPACE (mem_PH_of_fo_on_expansion X φ P h)

end ExpExpansion

end DescriptiveComplexity
