/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.Class
import Lax794877Proofs.DescriptiveComplexity.Counting.Post
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax794877Proofs.DescriptiveComplexity.CountingProblem
end Lax794877Proofs.DescriptiveComplexity.CountingProblem

namespace Lax794877Proofs.DescriptiveComplexity.OneCallReduction
end Lax794877Proofs.DescriptiveComplexity.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.OneCallReductions (OneCallReduction PostTerm)
end Lax794877Proofs.DescriptiveComplexity

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

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 C:51 " ≤ᶜ[≤] " D:51 => Lax859101.OneCallReductions.OneCallReduction C D

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- The relativized universe of the output of a reduction is nonempty on
nonempty finite ordered inputs. -/
theorem OneCallReduction.mapRel_nonempty (f : C ≤ᶜ[≤] D) (A : Type)
    [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (f.toRelInterpretation.MapRel A) :=
  let ⟨t, w, h⟩ := f.dom_nonempty A
  ⟨⟨(t, w), h⟩⟩

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax794877Proofs.DescriptiveComplexity.OneCallReduction (mapRel_nonempty)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- A relativized parsimonious reduction is a one-call reduction that returns
the answer of the oracle unchanged. -/
def RelOrderedParsimoniousReduction.toOneCall (f : C ≤ʳᵖ[≤] D) : C ≤ᶜ[≤] D :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    post := .oracle
    correct := f.correct }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (toOneCall)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- An ordered parsimonious reduction is a one-call reduction. -/
def OrderedParsimoniousReduction.toOneCall (f : C ≤ᵖ[≤] D) : C ≤ᶜ[≤] D :=
  f.toRel.toOneCall

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction (toOneCall)

end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- A parsimonious reduction is a one-call reduction. -/
noncomputable def ParsimoniousReduction.toOneCall (f : C ≤ᵖ D) : C ≤ᶜ[≤] D :=
  f.toOrdered.toOneCall

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.ParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.ParsimoniousReduction (toOneCall)

end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- Replacing the source of a one-call reduction by a counting problem with the
same values on finite structures. -/
def OneCallReduction.congrSource {C' : Lax366625.CountingProblems.CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (g : C ≤ᶜ[≤] D) :
    C' ≤ᶜ[≤] D :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    post := g.post
    correct := fun A => (h A).symm.trans (g.correct A) }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax794877Proofs.DescriptiveComplexity.OneCallReduction (congrSource)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- Replacing the target of a one-call reduction by a counting problem with the
same values on finite structures. -/
def OneCallReduction.congrTarget {D' : Lax366625.CountingProblems.CountingProblem L'}
    (h : ∀ (A : Type) [L'.Structure A] [Finite A], D A = D' A) (g : C ≤ᶜ[≤] D) :
    C ≤ᶜ[≤] D' :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    post := g.post
    correct := fun A _ _ _ _ =>
      haveI := g.toRelInterpretation.mapRel_finite A
      (g.correct A).trans
        (congrArg (fun c => g.post.eval A c) (h (g.toRelInterpretation.MapRel A))) }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax794877Proofs.DescriptiveComplexity.OneCallReduction (congrTarget)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- **Post-processing a reduction.** If the count of `C` is recovered from the
count of `C'` by a post-processing term, a one-call reduction from `C'` gives
one from `C`. -/
def OneCallReduction.ofPost {C' : Lax366625.CountingProblems.CountingProblem L} (g : C' ≤ᶜ[≤] D) (post : Lax859101.OneCallReductions.PostTerm L)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = post.eval A (C' A)) : C ≤ᶜ[≤] D :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    post := post.subst g.post
    correct := fun A _ _ _ _ => by
      rw [PostTerm.eval_subst, ← g.correct A]
      exact h A }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax794877Proofs.DescriptiveComplexity.OneCallReduction (ofPost)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

end Basic

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- **Transitivity of one-call reductions.** The interpretations compose as
for relativized reductions; the post-processing of the second reduction is
pulled back to the instance and substituted for the oracle's answer in the
post-processing of the first. There is still one call. -/
noncomputable def OneCallReduction.trans (g : C ≤ᶜ[≤] D) (f : D ≤ᶜ[≤] E) : C ≤ᶜ[≤] E :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toRelInterpretation := f.toRelInterpretation.compRel g.toRelInterpretation.ordExtendRel
    dom_nonempty := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      obtain ⟨y⟩ := f.mapRel_nonempty (g.toRelInterpretation.MapRel A)
      obtain ⟨⟨t, w⟩, hw⟩ := (e2.comp e3).symm y
      exact ⟨t, w, hw⟩
    post := g.post.subst (f.post.pull g.toRelInterpretation)
    correct := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toRelInterpretation.MapRel A)
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      rw [PostTerm.eval_subst, PostTerm.eval_pull, E.iso_invariant (e2.comp e3), ← h2]
      exact h1 }

end Trans

end Lax794877Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax794877Proofs.DescriptiveComplexity.OneCallReduction (trans)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

end Trans

/-! ### The one-call closure of a class: membership, hardness, completeness -/

namespace CountingClass

variable (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- A counting problem is in the **one-call closure** of a class when it
reduces with one call to a problem of the class. -/
def OneCallMem (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  ∃ (L'' : Language.{0, 0}) (_ : L''.IsRelational) (D : Lax366625.CountingProblems.CountingProblem L''),
    D ∈ K ∧ Nonempty (C ≤ᶜ[≤] D)

/-- A counting problem is **one-call hard** for a class when every problem of
the class reduces to it with one call. -/
def OneCallHard (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''),
    D ∈ K → Nonempty (D ≤ᶜ[≤] C)

/-- A counting problem is **one-call complete** for a class when it is in the
one-call closure of the class and one-call hard for it. -/
def OneCallComplete (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  K.OneCallMem C ∧ K.OneCallHard C

variable {K}

/-- A problem of the class is in its one-call closure. -/
theorem OneCallMem.of_mem {C : Lax366625.CountingProblems.CountingProblem L} (h : C ∈ K) : K.OneCallMem C :=
  ⟨L, inferInstance, C, h, ⟨(ParsimoniousReduction.refl C).toOneCall⟩⟩

/-- One-call hardness travels forward along one-call reductions. -/
theorem OneCallHard.of_oneCall {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}
    (f : C ≤ᶜ[≤] D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  fun E hE => ⟨(hC E hE).some.trans f⟩

/-- One-call hardness travels forward along ordered parsimonious reductions. -/
theorem OneCallHard.of_orderedParsimonious {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}
    (f : C ≤ᵖ[≤] D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  hC.of_oneCall f.toOneCall

/-- One-call hardness travels forward along parsimonious reductions. -/
theorem OneCallHard.of_parsimonious {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}
    (f : C ≤ᵖ D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  hC.of_oneCall f.toOneCall

/-- One-call hardness only depends on the values of a counting problem on
finite structures. -/
theorem oneCallHard_congr_finite {C D : Lax366625.CountingProblems.CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) :
    K.OneCallHard C ↔ K.OneCallHard D :=
  ⟨fun hC _ _ E hE => ⟨(hC E hE).some.congrTarget h⟩,
    fun hD _ _ E hE => ⟨(hD E hE).some.congrTarget fun A _ _ => (h A).symm⟩⟩

/-- A problem of the class that is one-call hard for it is one-call
complete. -/
theorem OneCallComplete.of_mem {C : Lax366625.CountingProblems.CountingProblem L} (hC : C ∈ K) (h : K.OneCallHard C) :
    K.OneCallComplete C :=
  ⟨OneCallMem.of_mem hC, h⟩

end CountingClass

variable [L.IsRelational]

/-- **Parsimonious `#P`-hardness implies one-call `#P`-hardness**: a
parsimonious reduction is a one-call reduction. -/
theorem oneCallHard_sharpP_of_parsimoniousHard {C : Lax366625.CountingProblems.CountingProblem L}
    (h : SharpP.ParsimoniousHard C) : SharpP.OneCallHard C :=
  fun D hD => (h D hD).map fun g => g.toOneCall

end Lax794877Proofs.DescriptiveComplexity


