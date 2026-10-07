/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.SecondOrder
import Lax794877Proofs.DescriptiveComplexity.Ordered
import Lax794877Proofs.DescriptiveComplexity.Encoding
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity.DecisionProblem
end Lax794877Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax794877Proofs.DescriptiveComplexity.FOReduction
end Lax794877Proofs.DescriptiveComplexity.FOReduction

namespace Lax794877Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax794877Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax794877Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax794877Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize SigmaSODefinable soLang)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Well-formed instances and computable decodings

The decoding direction of an encoding (`DescriptiveComplexity.Encoding`):
membership results transfer to the concrete problem along a faithful encoding
for free, but reading a *hardness* theorem back to concrete data needs a
converse – the abstract problem must not be hard only on junk structures the
encoding never produces. This file makes that converse checkable, in two
independent, composable pieces designed to keep the user-facing work minimal.

**Well-formedness is a decision problem.** The junk-free structures are cut
out by an isomorphism-invariant property `W` – typically a plain first-order
sentence, bundled by `DescriptiveComplexity.DecisionProblem.ofSentence` so that
invariance comes for free. Hardness *on well-formed instances* then needs no
new framework at all: it is ordinary hardness of the conjunction `W ⊓ P`
(pointwise `∧`, the `Min` instance below), and the library's existing
machinery applies to it unchanged. A user upgrades an existing completeness
proof with two one-liners:

* **hardness**: a reduction into `P` whose images are all well-formed is a
  reduction into `W ⊓ P` –
  `DescriptiveComplexity.FOReduction.withInvariant` /
  `DescriptiveComplexity.OrderedFOReduction.withInvariant` turn the existing
  reduction plus an image lemma into the strengthened one;
* **membership**: `DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`
  conjoins the sentence `W` into the existing `Σ₁` kernel.

The choice of `W` is self-policing: chosen too narrow, the hardness reduction
cannot land in it; chosen too wide, the decoding below cannot handle it.
Both failure modes are proofs that do not close, never silent unsoundness.

**Decodings are computations.** An *existential* decoding statement
(`∀ A, ∃ i, Conc i ↔ P A`) is classically near-vacuous:
casing on `P A` discharges it with no decoding whatsoever, whenever the
concrete type has one yes- and one no-instance. The honest content is a
*function*, so `DescriptiveComplexity.Decoding` bundles one, with the same
computability hygiene as encoders: a plain `def`

* `dec : FinPresentation L → Option ι` – from concretely presented finite
  structures (`DescriptiveComplexity.FinPresentation`: a size and a `Bool`-valued
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
`DescriptiveComplexity.Decoding.exists_conc_iff`; unlike its removed
predecessor it cannot be established by classical casing, because it is
derived from the bundled function.

Worked decoders are in the two tutorials
(`DescriptiveComplexity.Examples.ConjunctiveQueries`,
`DescriptiveComplexity.Examples.GraphCrawling`); the crawling one exists only
thanks to well-formedness – on structures marking several roots no honest
decoder can choose without computing reachability, and `W` (“exactly one
root”) is what removes them. `DescriptiveComplexity.bwDecoding`
(`DescriptiveComplexity.Encoding.BinarySubsetSum`) is the opposite extreme,
`W` being `⊤`: a binary-weighted structure whose order is not linear is a
definite no-instance, so a concrete no-instance decodes it and there is
nothing to exclude.

## Main declarations

* `DescriptiveComplexity.DecisionProblem.ofSentence`: a first-order sentence
  as a decision problem, the usual shape of a well-formedness condition;
* the `Min` instance on `DescriptiveComplexity.DecisionProblem`, giving the
  restriction `W ⊓ P`;
* `DescriptiveComplexity.FOReduction.withInvariant` and
  `DescriptiveComplexity.OrderedFOReduction.withInvariant`: strengthen a
  reduction's target by an invariant its images satisfy;
* `DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`: conjoin a
  first-order sentence into a `Σₖ` definition;
* `DescriptiveComplexity.Encoding.Faithful.inf`: encoded instances that are
  well-formed are faithful for the restricted problem;
* `DescriptiveComplexity.FinPresentation` and `DescriptiveComplexity.Decoding`:
  concretely presented structures and computable decodings, with
  `DescriptiveComplexity.Decoding.exists_conc_iff` as the `Prop`-level
  consequence.
-/

namespace Lax794877Proofs.DescriptiveComplexity

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

end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax794877Proofs.DescriptiveComplexity.DecisionProblem (and)

end Lax904597.Problems.DecisionProblem

namespace Lax794877Proofs.DescriptiveComplexity

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

end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax794877Proofs.DescriptiveComplexity.DecisionProblem (min_holds)

end Lax904597.Problems.DecisionProblem

namespace Lax794877Proofs.DescriptiveComplexity

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

/-! ### Conjoining a sentence into a second-order definition -/

instance (B : Lax904597.SecondOrder.SOBlock) (A : Type) : Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

/-! ### Faithfulness for the restricted problem -/

/-! ### Concretely presented structures and computable decodings -/

end Lax794877Proofs.DescriptiveComplexity


