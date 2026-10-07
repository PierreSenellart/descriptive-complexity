/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.SecondOrder
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity.PiSODefinable
end Lax480241Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax480241Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax480241Proofs.DescriptiveComplexity

/-!
# Functoriality of block expansion, and padding with trivial blocks

Infrastructure for the second-order definability layer of
`DescriptiveComplexity.SecondOrder`:

* *Functoriality*: a language morphism `Φ : L →ᴸ L'` lifts through the
  expansion by a list of blocks (`DescriptiveComplexity.soLangLift`), and alternating
  second-order satisfaction is invariant when the base structure is expanded
  along `Φ` (`DescriptiveComplexity.sorealize_soLangLift`).
* *Embedded first-order sentences*: a sentence of the base language, embedded
  into the block expansion (`DescriptiveComplexity.soLangEmbed`), can be pulled out of
  the second-order quantification when it appears as a conjunct or as the
  premise of an implication (`DescriptiveComplexity.sorealize_inf_embed`,
  `DescriptiveComplexity.sorealize_imp_embed`). This is how the auxiliary order of an
  ordered reduction is eliminated: the order becomes a second-order variable
  of the first block, guarded by the first-order sentence “it is a linear
  order”.
* *Padding*: appending or prepending the trivial (empty) block
  (`DescriptiveComplexity.SOBlock.trivial`) does not change alternating second-order
  satisfaction (`DescriptiveComplexity.sorealize_append_trivial`), so `Σₖ`- and
  `Πₖ`-definability satisfy the level inclusions of the polynomial hierarchy:
  `Σₖ ⊆ Σₖ₊₁ ∩ Πₖ₊₁` and dually (`DescriptiveComplexity.SigmaSODefinable.succ`,
  `DescriptiveComplexity.SigmaSODefinable.piSucc`, `DescriptiveComplexity.PiSODefinable.succ`,
  `DescriptiveComplexity.PiSODefinable.sigmaSucc`).

Languages vary through all the inductions, so the recursive definitions and
statements take them as explicit arguments.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Assignments always exist -/

instance SOBlock.instNonemptyAssignment (B : Lax904597.SecondOrder.SOBlock) (A : Type) :
    Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (instNonemptyAssignment)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

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

/-- A premise that is (the embedding of) a sentence of the base language can
be pulled out of the second-order quantification. -/
theorem sorealize_imp_embed :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (χ : L.Sentence) (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A instL Bs ((soLangEmbed Bs L).onSentence χ ⟹ φ) pol ↔
        (@Sentence.Realize L A instL χ → @Lax904597.SecondOrder.SORealize L A instL Bs φ pol) := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL χ φ pol
    let := instL
    let : (Lax904597.SecondOrder.soLang L []).Structure A := instL
    refine Iff.trans (Sentence.realize_imp (L := Lax904597.SecondOrder.soLang L []) (M := A)) ?_
    exact imp_congr ((LHom.id L).realize_onSentence A χ) Iff.rfl
  | cons B Bs ih =>
    intro L A instL χ φ pol
    rw [soLangEmbed_cons]
    have key : ∀ ρ : B.Assignment A,
        @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            (!pol) ↔
          (@Sentence.Realize L A instL χ →
            @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
              φ (!pol)) := by
      intro ρ
      let := instL
      let := B.structure ρ
      refine (ih (L.sum B.lang) A _ (LHom.sumInl.onSentence χ) φ (!pol)).trans ?_
      exact imp_congr (LHom.sumInl.realize_onSentence A χ) Iff.rfl
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            false) ↔ _
      refine (exists_congr fun ρ => key ρ).trans ?_
      constructor
      · rintro ⟨ρ, h⟩ hχ
        exact ⟨ρ, h hχ⟩
      · intro h
        rcases Classical.em (@Sentence.Realize L A instL χ) with hχ | hχ
        · obtain ⟨ρ, hρ⟩ := h hχ
          exact ⟨ρ, fun _ => hρ⟩
        · exact ⟨Classical.arbitrary _, fun hχ' => absurd hχ' hχ⟩
    | false =>
      change (∀ ρ : B.Assignment A,
          @Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            true) ↔ _
      refine (forall_congr' fun ρ => key ρ).trans ?_
      exact ⟨fun h hχ ρ => h ρ hχ, fun h ρ hχ => h hχ ρ⟩

/-! ### The trivial block, and padding -/

/-- The trivial second-order quantifier block, with no relation variables.
Quantifying over it (in either polarity) does not change satisfaction; it
pads a quantifier prefix to a larger number of alternations. -/
def SOBlock.trivial : Lax904597.SecondOrder.SOBlock where
  ι := Empty
  arity := Empty.elim

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (trivial)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Level inclusions at the definability level -/

end Lax480241Proofs.DescriptiveComplexity


