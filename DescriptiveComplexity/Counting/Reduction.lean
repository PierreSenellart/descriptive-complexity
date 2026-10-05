/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Class
import DescriptiveComplexity.Counting.Post

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
* A one-call reduction is a *polynomial-time 1-Turing reduction*: one oracle
  call, and polynomial-time computation before and after it. It is a
  restricted one, the instance being first-order definable and the computation
  after the call a fixed arithmetic term. A one-call hard problem is
  therefore `#P`-hard under 1-Turing reductions, hence under Turing
  reductions, the sense the literature most often means.
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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- A one-call counting reduction: a relativized ordered interpretation and a
post-processing term recovering the count of the source from the count of the
interpreted instance. -/
structure OneCallReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
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

variable [L.IsRelational] [L'.IsRelational] {C : CountingProblem L} {D : CountingProblem L'}

/-- The relativized universe of the output of a reduction is nonempty on
nonempty finite ordered inputs. -/
theorem OneCallReduction.mapRel_nonempty (f : C ≤ᶜ[≤] D) (A : Type)
    [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (f.toRelInterpretation.MapRel A) :=
  let ⟨t, w, h⟩ := f.dom_nonempty A
  ⟨⟨(t, w), h⟩⟩

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

/-- An ordered parsimonious reduction is a one-call reduction. -/
def OrderedParsimoniousReduction.toOneCall (f : C ≤ᵖ[≤] D) : C ≤ᶜ[≤] D :=
  f.toRel.toOneCall

/-- A parsimonious reduction is a one-call reduction. -/
noncomputable def ParsimoniousReduction.toOneCall (f : C ≤ᵖ D) : C ≤ᶜ[≤] D :=
  f.toOrdered.toOneCall

/-- Replacing the source of a one-call reduction by a counting problem with the
same values on finite structures. -/
def OneCallReduction.congrSource {C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (g : C ≤ᶜ[≤] D) :
    C' ≤ᶜ[≤] D :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    post := g.post
    correct := fun A => (h A).symm.trans (g.correct A) }

/-- Replacing the target of a one-call reduction by a counting problem with the
same values on finite structures. -/
def OneCallReduction.congrTarget {D' : CountingProblem L'}
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

/-- **Post-processing a reduction.** If the count of `C` is recovered from the
count of `C'` by a post-processing term, a one-call reduction from `C'` gives
one from `C`. -/
def OneCallReduction.ofPost {C' : CountingProblem L} (g : C' ≤ᶜ[≤] D) (post : PostTerm L)
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

/-- A counting problem read through an interpretation: the count of the
interpreted structure. -/
def CountingProblem.pullback {Tag : Type} {dim : ℕ} (D : CountingProblem L')
    (I : FOInterpretation L L' Tag dim) : CountingProblem L where
  Count := fun A _ => D (I.Map A)
  iso_invariant := fun e => D.iso_invariant (I.mapLEquiv e)

/-- A counting problem read through an interpretation reduces parsimoniously
to the problem itself, by that interpretation. -/
def CountingProblem.pullbackReduction {Tag : Type} [Finite Tag] [Nonempty Tag] {dim : ℕ}
    (D : CountingProblem L') (I : FOInterpretation L L' Tag dim) : D.pullback I ≤ᵖ D where
  Tag := Tag
  dim := dim
  toInterpretation := I
  correct := fun _ _ _ _ => rfl

end Basic

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {C : CountingProblem L₁} {D : CountingProblem L₂} {E : CountingProblem L₃}

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

/-! ### The one-call closure of a class: membership, hardness, completeness -/

namespace CountingClass

variable (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- A counting problem is in the **one-call closure** of a class when it
reduces with one call to a problem of the class. -/
def OneCallMem (C : CountingProblem L) : Prop :=
  ∃ (L'' : Language.{0, 0}) (_ : L''.IsRelational) (D : CountingProblem L''),
    D ∈ K ∧ Nonempty (C ≤ᶜ[≤] D)

/-- A counting problem is **one-call hard** for a class when every problem of
the class reduces to it with one call. -/
def OneCallHard (C : CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    D ∈ K → Nonempty (D ≤ᶜ[≤] C)

/-- A counting problem is **one-call complete** for a class when it is in the
one-call closure of the class and one-call hard for it. -/
def OneCallComplete (C : CountingProblem L) : Prop :=
  K.OneCallMem C ∧ K.OneCallHard C

variable {K}

theorem OneCallComplete.oneCallMem {C : CountingProblem L} (h : K.OneCallComplete C) :
    K.OneCallMem C := h.1

theorem OneCallComplete.oneCallHard {C : CountingProblem L} (h : K.OneCallComplete C) :
    K.OneCallHard C := h.2

/-- A problem of the class is in its one-call closure. -/
theorem OneCallMem.of_mem {C : CountingProblem L} (h : C ∈ K) : K.OneCallMem C :=
  ⟨L, inferInstance, C, h, ⟨(ParsimoniousReduction.refl C).toOneCall⟩⟩

/-- **The one-call closure is closed under one-call reductions.** -/
theorem OneCallMem.of_oneCall {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ᶜ[≤] D) (hD : K.OneCallMem D) : K.OneCallMem C := by
  obtain ⟨L'', _, E, hE, ⟨g⟩⟩ := hD
  exact ⟨L'', inferInstance, E, hE, ⟨f.trans g⟩⟩

/-- One-call hardness travels forward along one-call reductions. -/
theorem OneCallHard.of_oneCall {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ᶜ[≤] D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  fun E hE => ⟨(hC E hE).some.trans f⟩

/-- One-call hardness is hardness for the one-call closure: every problem of
the closure, and not only of the class, reduces to a one-call hard problem. -/
theorem oneCallHard_iff {C : CountingProblem L} :
    K.OneCallHard C ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
        K.OneCallMem D → Nonempty (D ≤ᶜ[≤] C) := by
  constructor
  · rintro hC L'' _ D ⟨L₃, _, E, hE, ⟨g⟩⟩
    exact ⟨g.trans (hC E hE).some⟩
  · intro h L'' _ D hD
    exact h D (OneCallMem.of_mem hD)

/-- One-call hardness travels forward along relativized parsimonious
reductions. -/
theorem OneCallHard.of_relOrderedParsimonious {C : CountingProblem L}
    {D : CountingProblem L'} (f : C ≤ʳᵖ[≤] D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  hC.of_oneCall f.toOneCall

/-- One-call hardness travels forward along ordered parsimonious reductions. -/
theorem OneCallHard.of_orderedParsimonious {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ᵖ[≤] D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  hC.of_oneCall f.toOneCall

/-- One-call hardness travels forward along parsimonious reductions. -/
theorem OneCallHard.of_parsimonious {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ᵖ D) (hC : K.OneCallHard C) : K.OneCallHard D :=
  hC.of_oneCall f.toOneCall

/-- One-call hardness only depends on the values of a counting problem on
finite structures. -/
theorem oneCallHard_congr_finite {C D : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) :
    K.OneCallHard C ↔ K.OneCallHard D :=
  ⟨fun hC _ _ E hE => ⟨(hC E hE).some.congrTarget h⟩,
    fun hD _ _ E hE => ⟨(hD E hE).some.congrTarget fun A _ _ => (h A).symm⟩⟩

/-- A problem of the class that is one-call hard for it is one-call
complete. -/
theorem OneCallComplete.of_mem {C : CountingProblem L} (hC : C ∈ K) (h : K.OneCallHard C) :
    K.OneCallComplete C :=
  ⟨OneCallMem.of_mem hC, h⟩

end CountingClass

variable [L.IsRelational]

/-- **Parsimonious `#P`-hardness implies one-call `#P`-hardness**: a
parsimonious reduction is a one-call reduction. -/
theorem oneCallHard_sharpP_of_parsimoniousHard {C : CountingProblem L}
    (h : SharpP.ParsimoniousHard C) : SharpP.OneCallHard C :=
  fun D hD => (h D hD).map fun g => g.toOneCall

/-- A parsimoniously `#P`-complete problem is one-call `#P`-complete. -/
theorem oneCallComplete_sharpP_of_parsimoniousComplete {C : CountingProblem L}
    (h : SharpP.ParsimoniousComplete C) : SharpP.OneCallComplete C :=
  .of_mem h.1 (oneCallHard_sharpP_of_parsimoniousHard h.2)

end DescriptiveComplexity
