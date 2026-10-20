/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Counting.Class
import Lax280166Proofs.DescriptiveComplexity.Counting.Post
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

namespace Lax280166Proofs.DescriptiveComplexity.CountingProblem
end Lax280166Proofs.DescriptiveComplexity.CountingProblem

namespace Lax280166Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax280166Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax280166Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax280166Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax280166Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax280166Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

/-!
# One-call counting reductions, and the one-call closure of a counting class

A parsimonious reduction preserves the number of solutions, hence also whether
there is one: no problem with an easy decision version is parsimoniously
`#P`-hard unless `P = NP`
(`DescriptiveComplexity.NP_subset_PTIME_of_sharpP_parsimoniousHard`). The
classical `#P`-complete problems of that kind – counting the models of a DNF
formula, the independent sets of a graph – are complete under a weaker notion,
defined here.

A **one-call reduction** `C ≤ᶜ[≤] D` is a relativized ordered first-order
interpretation `I` together with a post-processing term `post`
(`DescriptiveComplexity.PostTerm`), such that

`C A = post.eval A (D (I.MapRel A))`

on every finite ordered structure: one question is asked of the oracle for
`D`, at an instance defined first-order, and the count is recovered from the
answer by arithmetic on it and on first-order definable cardinalities of the
instance.

## Relation to the literature

* A parsimonious reduction is the case `post = oracle`
  (`DescriptiveComplexity.RelOrderedParsimoniousReduction.toOneCall`).
* A one-call reduction is what the literature calls a **metric reduction**,
  `f(x) = ψ(x, g(φ(x)))` with `φ` and `ψ` computable in polynomial time, a
  notion due to [Krentel 1988][krentel1988complexity] (here as stated in
  [Faliszewski and Hemaspaandra 2009][faliszewski2009complexity],
  Definition 1.2), or equivalently a *polynomial-time 1-Turing reduction*: one
  oracle call, and polynomial-time computation before and after it. It is a
  restricted one, `φ` being a first-order interpretation and `ψ` a fixed
  arithmetic term. A one-call hard problem is therefore `#P`-hard under
  metric reductions, hence under Turing reductions, the sense the literature
  most often means. There is no single agreed notion of completeness for
  classes of functions: beside the metric and the parsimonious reductions, the
  *many-one* reductions for functions ask that `ψ` not read the input,
  `f(x) = ψ(g(φ(x)))`; a one-call reduction is one of those when its term
  mentions no cardinality of the instance.
  [Durand, Haak, Kontinen, Vollmer 2016][durand2016descriptive] use exactly
  the reduction of #SAT to #DNF by `2 ^ n - oracle`, under the name of an
  AC⁰-Turing reduction (their Lemma 19; the preprint of the paper calls it a
  metric reduction), and a division of the oracle's answer for another, a
  TC⁰-Turing reduction (their Lemma 20), as the digit extractions of this
  library do.
* That notion is coarse.
  [Toda and Watanabe 1992][toda1992polynomial] show that a problem `#P`-hard
  under polynomial-time 1-Turing reductions is hard for the higher counting
  classes `#·Πₖᵖ` as well, which is strong evidence that `#P` is not closed
  under such reductions. Membership in a counting class is therefore closed
  under parsimonious reductions only, never under these, and one-call
  hardness does not tell `#P` apart from the classes above it.
* The *subtractive reductions* of
  [Durand, Hermann, Kolaitis 2005][durand2005subtractive] were introduced to
  repair this: a strong subtractive reduction asks the oracle two questions,
  at instances `f(x)` and `g(x)` with the solutions of the first among those
  of the second, and returns the difference of the answers; `#P` is closed
  under them (their Theorem 3.3). The reduction of #SAT to #DNF is one
  (their Proposition 3.4), `g(x)` being a tautology: here it is the one-call
  reduction with term `2 ^ n - oracle`, the answer at the tautology being
  known. Subtractive reductions are formalized in
  `DescriptiveComplexity.Counting.Subtractive`, with the closure of `#P`. The
  reductions that read a digit by a quotient and a remainder are not
  subtractive, and nothing is claimed here about whether their targets are
  complete under subtractive reductions.

## The one-call closure of a class

`#P` is not expected to be closed under one-call reductions, so the plain
words *hard* and *complete* are not used for them: as on the decision side,
those words belong to reductions the class is closed under, here the
subtractive ones (`DescriptiveComplexity.Counting.Subtractive`). What one-call reductions
are the reductions *of* is the **one-call closure** of a class,
`DescriptiveComplexity.CountingClass.OneCallMem`: the problems that reduce with
one call to a problem of the class. It contains the class, is closed under
one-call reductions (`DescriptiveComplexity.CountingClass.OneCallMem.of_oneCall`),
and `DescriptiveComplexity.CountingClass.OneCallHard` is hardness for it
(`DescriptiveComplexity.CountingClass.oneCallHard_iff`);
`DescriptiveComplexity.CountingClass.OneCallComplete` conjoins the two.
Parsimonious hardness implies one-call hardness
(`DescriptiveComplexity.oneCallHard_sharpP_of_parsimoniousHard`).

The one-call closure of `#P` is a logical counterpart of the class `FP^#P` of
the functions computable in polynomial time with a `#P` oracle. It is not
given that name: that it is the same class would need one oracle call to
suffice, and a polynomial-time computation after the call to be replaceable by
a post-processing term, and neither is proved here.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- A one-call counting reduction: a relativized ordered interpretation and a
post-processing term recovering the count of the source from the count of the
interpreted instance. -/
structure OneCallReduction [L.IsRelational] [L'.IsRelational]
    (C : Lax366625.CountingProblems.CountingProblem L) (D : Lax366625.CountingProblems.CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : Lax904597.Relativized.RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- The arithmetic applied to the answer of the oracle. -/
  post : PostTerm L
  /-- The count of the source is the post-processed count of the interpreted
  instance, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = post.eval A (D (toRelInterpretation.MapRel A))

@[inherit_doc]
scoped notation:50 C:51 " ≤ᶜ[≤] " D:51 => OneCallReduction C D

section Basic

end Basic

section Trans

end Trans

/-! ### The one-call closure of a class: membership, hardness, completeness -/

namespace CountingClass

end CountingClass

end Lax280166Proofs.DescriptiveComplexity


