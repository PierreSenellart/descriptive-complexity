/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax420092Proofs.DescriptiveComplexity.SecondOrder
import Lax420092Proofs.DescriptiveComplexity.Ordered
import Lax420092Proofs.DescriptiveComplexity.Encoding
import Lax420092.Evaluation
import Lax420092.PackagedInstances
import Lax420092.QueryDatabases
import Lax420092.QueryPairs
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

namespace Lax420092Proofs.DescriptiveComplexity.DecisionProblem
end Lax420092Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity.FOReduction
end Lax420092Proofs.DescriptiveComplexity.FOReduction

namespace Lax420092Proofs.DescriptiveComplexity.FinPresentation
end Lax420092Proofs.DescriptiveComplexity.FinPresentation

namespace Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable

/-!
# Well-formed instances and computable decodings

The decoding direction of an encoding (`Lax420092Proofs.DescriptiveComplexity.Encoding`):
membership results transfer to the concrete problem along a faithful encoding
for free, but reading a *hardness* theorem back to concrete data needs a
converse – the abstract problem must not be hard only on junk structures the
encoding never produces. This file makes that converse checkable, in two
independent, composable pieces designed to keep the user-facing work minimal.

**Well-formedness is a decision problem.** The junk-free structures are cut
out by an isomorphism-invariant property `W` – typically a plain first-order
sentence, bundled by `Lax420092Proofs.DescriptiveComplexity.DecisionProblem.ofSentence` so that
invariance comes for free. Hardness *on well-formed instances* then needs no
new framework at all: it is ordinary hardness of the conjunction `W ⊓ P`
(pointwise `∧`, the `Min` instance below), and the library's existing
machinery applies to it unchanged. A user upgrades an existing completeness
proof with two one-liners:

* **hardness**: a reduction into `P` whose images are all well-formed is a
  reduction into `W ⊓ P` –
  `Lax420092Proofs.DescriptiveComplexity.FOReduction.withInvariant` /
  `Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction.withInvariant` turn the existing
  reduction plus an image lemma into the strengthened one;
* **membership**: `Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`
  conjoins the sentence `W` into the existing `Σ₁` kernel.

The choice of `W` is self-policing: chosen too narrow, the hardness reduction
cannot land in it; chosen too wide, the decoding below cannot handle it.
Both failure modes are proofs that do not close, never silent unsoundness.

**Decodings are computations.** An *existential* decoding statement
(`∀ A, ∃ i, Conc i ↔ P A`) is classically near-vacuous:
casing on `P A` discharges it with no decoding whatsoever, whenever the
concrete type has one yes- and one no-instance. The honest content is a
*function*, so `Lax420092Proofs.DescriptiveComplexity.Decoding` bundles one, with the same
computability hygiene as encoders: a plain `def`

* `dec : FinPresentation L → Option ι` – from concretely presented finite
  structures (`Lax420092Proofs.DescriptiveComplexity.FinPresentation`: a size and a `Bool`-valued
  relation table) to concrete instances, `none` *being* the junk case, so no
  proof-carrying arguments and no partiality tricks;
* `sound` – whatever `dec` returns is decided by `Conc` exactly as the
  presented structure is by `P`;
* `total` – on well-formed (nonempty) presentations, `dec` returns something.

Because `dec` is `Option`-valued and computable, it can be *run*: `#guard`s
can test a decoder on small presentations exactly as they test encoders, and
the compiler rejects a decoder whose data decides an undecidable predicate.
The residual gap is also the same as for encoders: computability is enforced,
a *complexity bound* is not (a decoder may brute-force the answer), since
stating one means measuring the decoder against a machine model, which this
interface does not do.

The `Prop`-level consequence – every well-formed finite structure is
semantically a concrete instance – is
`Lax420092Proofs.DescriptiveComplexity.Decoding.exists_conc_iff`; unlike its removed
predecessor it cannot be established by classical casing, because it is
derived from the bundled function.

Worked decoders are in the two tutorials
(`Lax420092Proofs.DescriptiveComplexity.Examples.ConjunctiveQueries`,
`Lax420092Proofs.DescriptiveComplexity.Examples.GraphCrawling`); the crawling one exists only
thanks to well-formedness – on structures marking several roots no honest
decoder can choose without computing reachability, and `W` (“exactly one
root”) is what removes them. `Lax420092Proofs.DescriptiveComplexity.bwDecoding`
(`Lax420092Proofs.DescriptiveComplexity.Encoding.BinarySubsetSum`) is the opposite extreme,
`W` being `⊤`: a binary-weighted structure whose order is not linear is a
definite no-instance, so a concrete no-instance decodes it and there is
nothing to exclude.

## Main declarations

* `Lax420092Proofs.DescriptiveComplexity.DecisionProblem.ofSentence`: a first-order sentence
  as a decision problem, the usual shape of a well-formedness condition;
* the `Min` instance on `Lax420092Proofs.DescriptiveComplexity.DecisionProblem`, giving the
  restriction `W ⊓ P`;
* `Lax420092Proofs.DescriptiveComplexity.FOReduction.withInvariant` and
  `Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction.withInvariant`: strengthen a
  reduction's target by an invariant its images satisfy;
* `Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`: conjoin a
  first-order sentence into a `Σₖ` definition;
* `Lax420092Proofs.DescriptiveComplexity.Encoding.Faithful.inf`: encoded instances that are
  well-formed are faithful for the restricted problem;
* `Lax420092Proofs.DescriptiveComplexity.FinPresentation` and `Lax420092Proofs.DescriptiveComplexity.Decoding`:
  concretely presented structures and computable decodings, with
  `Lax420092Proofs.DescriptiveComplexity.Decoding.exists_conc_iff` as the `Prop`-level
  consequence.
-/

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Well-formedness as a decision problem -/

/-- The conjunction of two decision problems: a structure is a yes-instance
when it is one of both. Written `W ⊓ P` (through the `Min` instance below);
with `W` a well-formedness condition, `W ⊓ P` is “`P`, on well-formed
instances”. -/
protected def DecisionProblem.and [L.IsRelational] (W P : Lax904597.Problems.DecisionProblem L) :
    Lax904597.Problems.DecisionProblem L where
  Holds := fun A inst => @Lax904597.Problems.DecisionProblem.Holds L _ W A inst ∧ @Lax904597.Problems.DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => and_congr (W.iso_invariant e) (P.iso_invariant e)

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (and)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

instance [L.IsRelational] : Min (Lax904597.Problems.DecisionProblem L) :=
  ⟨DecisionProblem.and⟩

@[simp]
theorem DecisionProblem.min_holds [L.IsRelational] (W P : Lax904597.Problems.DecisionProblem L) (A : Type)
    [L.Structure A] :
    (W ⊓ P) A ↔ W A ∧ P A :=
  Iff.rfl

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (min_holds)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- A first-order sentence, read as a decision problem: the structures
satisfying it. Isomorphism-invariance is automatic, which makes this the
cheapest way to state a well-formedness condition `W`. -/
protected def DecisionProblem.ofSentence [L.IsRelational] (ψ : L.Sentence) :
    Lax904597.Problems.DecisionProblem L where
  Holds := fun A inst => @Sentence.Realize L A inst ψ
  iso_invariant := fun e => StrongHomClass.realize_sentence e ψ

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (ofSentence)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

@[simp]
theorem DecisionProblem.ofSentence_holds [L.IsRelational] (ψ : L.Sentence) (A : Type)
    [L.Structure A] :
    DecisionProblem.ofSentence ψ A ↔ A ⊨ ψ :=
  Iff.rfl

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (ofSentence_holds)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Reductions with an image invariant

A reduction into `P` whose images all satisfy `W` is a reduction into
`W ⊓ P` – so hardness of the restricted problem costs one image lemma on top
of the reduction already at hand. Only the *last* hop of a reduction chain
needs the lemma: composing any further reduction in front leaves the images
unchanged. -/

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-- Strengthen the target of a reduction by an invariant its images satisfy. -/
def FOReduction.withInvariant [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    {Q : Lax904597.Problems.DecisionProblem L'}
    (f : P ≤ᶠᵒ Q) (W : Lax904597.Problems.DecisionProblem L')
    (h : ∀ (A : Type) [L.Structure A] [Nonempty A], W (f.toInterpretation.Map A)) :
    P ≤ᶠᵒ (W ⊓ Q) :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => (f.correct A).trans ⟨fun hq => ⟨h A, hq⟩, And.right⟩ }

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax420092Proofs.DescriptiveComplexity.FOReduction (withInvariant)

end Lax904597.Interpretations.FOReduction

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-! ### Conjoining a sentence into a second-order definition -/

instance (B : Lax904597.SecondOrder.SOBlock) (A : Type) : Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

/-- A sentence of the base language, lifted to the language of a kernel: the
symbols are unchanged, only their address in the iterated sum grows. -/
def soLift : ∀ {L : Language.{0, 0}} (Bs : List Lax904597.SecondOrder.SOBlock),
    L.Sentence → (Lax904597.SecondOrder.soLang L Bs).Sentence
  | _, [], ψ => ψ
  | _, _ :: Bs, ψ => soLift Bs (LHom.sumInl.onSentence ψ)

/-- Realization of a lifted sentence conjoined into a kernel: the lifted
conjunct does not mention the quantified relation variables, so it pulls out
of the second-order quantifiers. -/
private theorem sorealize_soLift_inf :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A : Type) (inst : L.Structure A)
      (ψ : L.Sentence) (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A inst Bs (soLift Bs ψ ⊓ φ) pol ↔
        (@Sentence.Realize L A inst ψ ∧ @Lax904597.SecondOrder.SORealize L A inst Bs φ pol)
  | [], L, A, inst, ψ, φ, pol => by
    change @Sentence.Realize L A inst (ψ ⊓ φ) ↔ _
    exact Formula.realize_inf
  | B :: Bs, L, A, inst, ψ, φ, pol => by
    have hψ : ∀ ρ : B.Assignment A,
        @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
            (LHom.sumInl.onSentence ψ) ↔
          @Sentence.Realize L A inst ψ := fun ρ => by
      let := B.structure ρ
      exact LHom.sumInl.realize_onSentence (M := A) ψ
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, hρ⟩
        obtain ⟨h1, h2⟩ := (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ false).mp hρ
        exact ⟨(hψ ρ).mp h1, ρ, h2⟩
      · rintro ⟨h1, ρ, h2⟩
        exact ⟨ρ, (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ false).mpr
            ⟨(hψ ρ).mpr h1, h2⟩⟩
    | false =>
      constructor
      · intro h
        obtain ⟨ρ₀⟩ : Nonempty (B.Assignment A) := inferInstance
        refine ⟨(hψ ρ₀).mp ((sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ₀)) _ φ true).mp (h ρ₀)).1,
          fun ρ => ((sorealize_soLift_inf Bs (L.sum B.lang) A
            (@sumStructure L B.lang A inst (B.structure ρ)) _ φ true).mp (h ρ)).2⟩
      · rintro ⟨h1, h2⟩ ρ
        exact (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ true).mpr
            ⟨(hψ ρ).mpr h1, h2 ρ⟩

/-- **Conjoining a first-order sentence preserves `Σₖ`-definability**: the
sentence joins the kernel, lifted along the block languages. This is the
membership half of restricting a problem to its well-formed instances. -/
theorem SigmaSODefinable.inf_ofSentence {k : ℕ} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax904597.SecondOrder.SigmaSODefinable k P) (ψ : L.Sentence) :
    Lax904597.SecondOrder.SigmaSODefinable k (DecisionProblem.ofSentence ψ ⊓ P) := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  refine ⟨Bs, hlen, soLift Bs ψ ⊓ φ, ?_⟩
  intro A inst _ _
  exact (and_congr Iff.rfl (hφ A)).trans
    (sorealize_soLift_inf Bs L A inst ψ φ true).symm

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SigmaSODefinable

export Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable (inf_ofSentence)

end Lax904597.SecondOrder.SigmaSODefinable

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-! ### Faithfulness for the restricted problem -/

/-! ### Concretely presented structures and computable decodings -/

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str [L.IsRelational] (S : Lax420092.PackagedInstances.FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

end Lax420092Proofs.DescriptiveComplexity

namespace Lax420092.PackagedInstances.FinPresentation

export Lax420092Proofs.DescriptiveComplexity.FinPresentation (str)

end Lax420092.PackagedInstances.FinPresentation

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

variable {L' : Language.{0, 0}} [L'.IsRelational]

@[simp]
theorem FinPresentation.relMap_iff [L.IsRelational] (S : Lax420092.PackagedInstances.FinPresentation L) {n}
    (R : L.Relations n) (x : Fin n → Fin S.card) :
    RelMap R x ↔ S.relBool R x = true :=
  Iff.rfl

end Lax420092Proofs.DescriptiveComplexity

namespace Lax420092.PackagedInstances.FinPresentation

export Lax420092Proofs.DescriptiveComplexity.FinPresentation (relMap_iff)

end Lax420092.PackagedInstances.FinPresentation

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

variable {L' : Language.{0, 0}} [L'.IsRelational]

end Lax420092Proofs.DescriptiveComplexity


