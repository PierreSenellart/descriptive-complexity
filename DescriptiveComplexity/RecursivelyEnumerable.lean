/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewOrdered
import DescriptiveComplexity.Hierarchy

/-!
# The class RE, defined by value invention

**RE** (`DescriptiveComplexity.RE`), the recursively enumerable problems,
*defined* – like every class in this library – by a logic: definability in
`∃SO[new]`, existential second-order logic over a universe extended by finitely
many invented values (`DescriptiveComplexity.SigmaSONewDefinable`, in
`DescriptiveComplexity.SecondOrderNew`).

It is a bona fide `DescriptiveComplexity.ComplexityClass` because `∃SO[new]`
definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSONewDefinable.of_foReduction` in
`DescriptiveComplexity.SecondOrderNewPull`, and
`DescriptiveComplexity.SigmaSONewDefinable.of_orderedReduction` in
`DescriptiveComplexity.SecondOrderNewOrdered`): the target's extended universe
is definable inside the source's, with the same invented values, so the kernel
pulls back through a relativized interpretation, and the order of an ordered
reduction is re-quantified inside the block under a guard relativized to the
original elements.

`DescriptiveComplexity.NP_subset_RE` is the inclusion `NP ⊆ RE`, by inventing
nothing.

## What this file claims, and where the rest is

RE is here a *logically defined* class, exactly as NP is `Σ₁`-definability
rather than a machine notion: a completeness proof for it is an `∃SO[new]`
definition plus a first-order reduction. Two facts about it are proved
elsewhere, where the class meets Mathlib's computability layer, and nothing in
this file assumes them:

* `DescriptiveComplexity.mem_RE_iff_rePred` – RE *is* recursive enumerability:
  a problem is `∃SO[new]`-definable exactly when its concrete instances form an
  `REPred`;
* `DescriptiveComplexity.RE_ne_coRE` – RE differs from its complement
  `DescriptiveComplexity.coRE`. That separation is not available here:
  `coNP = Π₁ᵖ` has a *logical* dual definition, while `∃SO[new]` has no dual
  reading, so nothing in this file relates the two classes. It is the
  undecidability of an RE-complete problem, through Post's theorem, that
  separates them.

Both are in `DescriptiveComplexity.Computability.CodeHaltComplete`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **The class RE**: the problems definable in `∃SO[new]`, existential
second-order logic with value invention. Unbounding the number of invented
values is the only change from the `Σ₁` definition of NP, and it is what takes
the class from “search a space exponential in the instance” to “search an
unbounded space of finite witnesses”.

It is a `DescriptiveComplexity.ComplexityClass` by the two closure theorems of
`DescriptiveComplexity.SecondOrderNewPull` and
`DescriptiveComplexity.SecondOrderNewOrdered`; hardness is *cofinal*, as
everywhere in this development (see `DescriptiveComplexity.hard_RE_iff`). -/
noncomputable def RE : ComplexityClass where
  Mem P := SigmaSONewDefinable P
  Hard P := CofinalHard (fun Q => SigmaSONewDefinable Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  hard_of_relOrderedReduction f hP := CofinalHard.of_relOrderedReduction f hP
  mem_congr_finite h := sigmaSONewDefinable_congr h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-- **co-RE**: the problems whose complement is recursively enumerable. Unlike
`coNP`, which the second-order quantifier duality identifies with `Π₁`
definability, this is only the complement operator applied to RE: `∃SO[new]`
has no dual reading here, and no inclusion between RE and co-RE is available at
this level. That the two classes differ is
`DescriptiveComplexity.RE_ne_coRE`. -/
noncomputable abbrev coRE : ComplexityClass := RE.compl

variable {L : Language.{0, 0}}

@[simp]
theorem mem_RE_iff (P : DecisionProblem L) : P ∈ RE ↔ SigmaSONewDefinable P :=
  Iff.rfl

@[simp]
theorem mem_coRE_iff (P : DecisionProblem L) : P ∈ coRE ↔ SigmaSONewDefinable Pᶜ :=
  Iff.rfl

/-- Over a relational vocabulary, cofinal RE-hardness is the usual notion:
every `∃SO[new]`-definable problem reduces to `P`. -/
theorem hard_RE_iff [L.IsRelational] (P : DecisionProblem L) :
    RE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        SigmaSONewDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- **`NP ⊆ RE`**: an existential second-order sentence is an `∃SO[new]`
sentence that invents nothing (`DescriptiveComplexity.SigmaSODefinable.toNew`).
-/
theorem NP_subset_RE : NP ⊆ RE :=
  fun _ _ hP => SigmaSODefinable.toNew hP

/-- `coNP ⊆ coRE`, by complementing `DescriptiveComplexity.NP_subset_RE`. -/
theorem coNP_subset_coRE : coNP ⊆ coRE :=
  fun _ P hP => NP_subset_RE ((mem_piP_iff 1 P).mp hP)

end DescriptiveComplexity
