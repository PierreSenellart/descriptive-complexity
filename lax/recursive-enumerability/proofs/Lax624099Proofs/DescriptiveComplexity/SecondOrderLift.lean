/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.SecondOrder
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.DescriptiveComplexity.PiSODefinable
end Lax624099Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax624099Proofs.DescriptiveComplexity.SOBlock
end Lax624099Proofs.DescriptiveComplexity.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable

/-!
# Functoriality of block expansion, and padding with trivial blocks

Infrastructure for the second-order definability layer of
`Lax624099Proofs.DescriptiveComplexity.SecondOrder`:

* *Functoriality*: a language morphism `Φ : L →ᴸ L'` lifts through the
  expansion by a list of blocks (`Lax624099Proofs.DescriptiveComplexity.soLangLift`), and alternating
  second-order satisfaction is invariant when the base structure is expanded
  along `Φ` (`Lax624099Proofs.DescriptiveComplexity.sorealize_soLangLift`).
* *Embedded first-order sentences*: a sentence of the base language, embedded
  into the block expansion (`Lax624099Proofs.DescriptiveComplexity.soLangEmbed`), can be pulled out of
  the second-order quantification when it appears as a conjunct or as the
  premise of an implication (`Lax624099Proofs.DescriptiveComplexity.sorealize_inf_embed`,
  `Lax624099Proofs.DescriptiveComplexity.sorealize_imp_embed`). This is how the auxiliary order of an
  ordered reduction is eliminated: the order becomes a second-order variable
  of the first block, guarded by the first-order sentence “it is a linear
  order”.
* *Padding*: appending or prepending the trivial (empty) block
  (`Lax624099Proofs.DescriptiveComplexity.SOBlock.trivial`) does not change alternating second-order
  satisfaction (`Lax624099Proofs.DescriptiveComplexity.sorealize_append_trivial`), so `Σₖ`- and
  `Πₖ`-definability satisfy the level inclusions of the polynomial hierarchy:
  `Σₖ ⊆ Σₖ₊₁ ∩ Πₖ₊₁` and dually (`Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.succ`,
  `Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.piSucc`, `Lax624099Proofs.DescriptiveComplexity.PiSODefinable.succ`,
  `Lax624099Proofs.DescriptiveComplexity.PiSODefinable.sigmaSucc`).

Languages vary through all the inductions, so the recursive definitions and
statements take them as explicit arguments.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Assignments always exist -/

instance SOBlock.instNonemptyAssignment (B : Lax904597.SecondOrder.SOBlock) (A : Type) :
    Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (instNonemptyAssignment)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Functoriality of block expansion -/

/-- Lift of a language morphism through the expansion by blocks: symbols of
the base language are mapped by the morphism, relation variables of the
blocks to themselves. -/
def soLangLift : ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L L' : Language.{0, 0}),
    (L →ᴸ L') → (Lax904597.SecondOrder.soLang L Bs →ᴸ Lax904597.SecondOrder.soLang L' Bs)
  | [], _, _, Φ => Φ
  | B :: Bs, L, L', Φ =>
      soLangLift Bs (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang))

/-- Alternating second-order satisfaction only depends on the base structure
through the symbols the kernel mentions: it is invariant under transporting
the kernel along a language morphism whose expansion the structure is. -/
theorem sorealize_soLangLift :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L L' : Language.{0, 0}) (Φ : L →ᴸ L') (A : Type)
      (instL : L.Structure A) (instL' : L'.Structure A),
      @LHom.IsExpansionOn L L' Φ A instL instL' →
      ∀ (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
        @Lax904597.SecondOrder.SORealize L' A instL' Bs ((soLangLift Bs L L' Φ).onSentence φ) pol ↔
          @Lax904597.SecondOrder.SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L L' Φ A instL instL' hexp φ pol
    let := instL
    let := instL'
    have := hexp
    exact Φ.realize_onSentence A φ
  | cons B Bs ih =>
    intro L L' Φ A instL instL' hexp φ pol
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L'.sum B.lang) A (@sumStructure L' B.lang A instL' (B.structure ρ)) Bs
            ((soLangLift Bs (L.sum B.lang) (L'.sum B.lang)
              (Φ.sumMap (LHom.id B.lang))).onSentence φ) false) ↔
        ∃ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ false
      refine exists_congr fun ρ => ?_
      exact ih (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang)) A _ _
        (by let := instL; let := instL'; let := B.structure ρ; have := hexp
            infer_instance) φ false
    | false =>
      change (∀ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L'.sum B.lang) A (@sumStructure L' B.lang A instL' (B.structure ρ)) Bs
            ((soLangLift Bs (L.sum B.lang) (L'.sum B.lang)
              (Φ.sumMap (LHom.id B.lang))).onSentence φ) true) ↔
        ∀ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ true
      refine forall_congr' fun ρ => ?_
      exact ih (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang)) A _ _
        (by let := instL; let := instL'; let := B.structure ρ; have := hexp
            infer_instance) φ true

/-! ### Embedding the base language into a block expansion -/

/-- The embedding of the base language into its expansion by blocks. -/
def soLangEmbed : ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}), L →ᴸ Lax904597.SecondOrder.soLang L Bs
  | [], L => LHom.id L
  | B :: Bs, L => (soLangEmbed Bs (L.sum B.lang)).comp LHom.sumInl

private theorem soLangEmbed_cons (B : Lax904597.SecondOrder.SOBlock) (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0})
    (χ : L.Sentence) :
    (soLangEmbed (B :: Bs) L).onSentence χ =
      (soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) :=
  congrFun (LHom.comp_onBoundedFormula (soLangEmbed Bs (L.sum B.lang)) LHom.sumInl) χ

/-- A conjunct that is (the embedding of) a sentence of the base language can
be pulled out of the second-order quantification. -/
theorem sorealize_inf_embed :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (χ : L.Sentence) (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A instL Bs ((soLangEmbed Bs L).onSentence χ ⊓ φ) pol ↔
        @Sentence.Realize L A instL χ ∧ @Lax904597.SecondOrder.SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL χ φ pol
    let := instL
    let : (Lax904597.SecondOrder.soLang L []).Structure A := instL
    refine Iff.trans (Sentence.realize_inf (L := Lax904597.SecondOrder.soLang L []) (M := A)) ?_
    exact and_congr_left' ((LHom.id L).realize_onSentence A χ)
  | cons B Bs ih =>
    intro L A instL χ φ pol
    rw [soLangEmbed_cons]
    have key : ∀ ρ : B.Assignment A,
        @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            (!pol) ↔
          @Sentence.Realize L A instL χ ∧
            @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
              φ (!pol) := by
      intro ρ
      let := instL
      let := B.structure ρ
      refine (ih (L.sum B.lang) A _ (LHom.sumInl.onSentence χ) φ (!pol)).trans ?_
      exact and_congr_left' (LHom.sumInl.realize_onSentence A χ)
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            false) ↔ _
      refine (exists_congr fun ρ => key ρ).trans ?_
      exact exists_and_left
    | false =>
      change (∀ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            true) ↔ _
      refine (forall_congr' fun ρ => key ρ).trans ?_
      constructor
      · intro h
        exact ⟨(h (Classical.arbitrary _)).1, fun ρ => (h ρ).2⟩
      · rintro ⟨hχ, h⟩ ρ
        exact ⟨hχ, h ρ⟩

/-! ### The trivial block, and padding -/

/-! ### Level inclusions at the definability level -/

variable {L : Language.{0, 0}} [L.IsRelational] {k : ℕ} {P : Lax904597.Problems.DecisionProblem L}

end Lax624099Proofs.DescriptiveComplexity


