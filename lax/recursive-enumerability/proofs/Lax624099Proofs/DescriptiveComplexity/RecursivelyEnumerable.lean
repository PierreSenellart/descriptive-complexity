/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.SecondOrderNewOrdered
import Lax624099Proofs.DescriptiveComplexity.Hierarchy
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

/-!
# The class RE, defined by value invention

**RE** (`Lax624099Proofs.DescriptiveComplexity.RE`), the recursively enumerable problems,
*defined* – like every class in this library – by a logic: definability in
`∃SO[new]`, existential second-order logic over a universe extended by finitely
many invented values (`Lax624099Proofs.DescriptiveComplexity.SigmaSONewDefinable`, in
`Lax624099Proofs.DescriptiveComplexity.SecondOrderNew`).

It is a bona fide `Lax624099Proofs.DescriptiveComplexity.ComplexityClass` because `∃SO[new]`
definability is closed under (ordered) first-order reductions
(`Lax624099Proofs.DescriptiveComplexity.SigmaSONewDefinable.of_foReduction` in
`Lax624099Proofs.DescriptiveComplexity.SecondOrderNewPull`, and
`Lax624099Proofs.DescriptiveComplexity.SigmaSONewDefinable.of_orderedReduction` in
`Lax624099Proofs.DescriptiveComplexity.SecondOrderNewOrdered`): the target's extended universe
is definable inside the source's, with the same invented values, so the kernel
pulls back through a relativized interpretation, and the order of an ordered
reduction is re-quantified inside the block under a guard relativized to the
original elements.

`Lax624099Proofs.DescriptiveComplexity.NP_subset_RE` is the inclusion `NP ⊆ RE`, by inventing
nothing.

## What this file claims, and where the rest is

RE is here a *logically defined* class, exactly as NP is `Σ₁`-definability
rather than a machine notion: a completeness proof for it is an `∃SO[new]`
definition plus a first-order reduction. Two facts about it are proved
elsewhere, where the class meets Mathlib's computability layer, and nothing in
this file assumes them:

* `Lax624099Proofs.DescriptiveComplexity.mem_RE_iff_rePred` – RE *is* recursive enumerability:
  a problem is `∃SO[new]`-definable exactly when its concrete instances form an
  `REPred`;
* `Lax624099Proofs.DescriptiveComplexity.RE_ne_coRE` – RE differs from its complement
  `Lax624099Proofs.DescriptiveComplexity.coRE`. That separation is not available here:
  `coNP = Π₁ᵖ` has a *logical* dual definition, while `∃SO[new]` has no dual
  reading, so nothing in this file relates the two classes. It is the
  undecidability of an RE-complete problem, through Post's theorem, that
  separates them.

Both are in `Lax624099Proofs.DescriptiveComplexity.Computability.CodeHaltComplete`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **The class RE**: the problems definable in `∃SO[new]`, existential
second-order logic with value invention. Unbounding the number of invented
values is the only change from the `Σ₁` definition of NP, and it is what takes
the class from “search a space exponential in the instance” to “search an
unbounded space of finite witnesses”.

It is a `Lax624099Proofs.DescriptiveComplexity.ComplexityClass` by the two closure theorems of
`Lax624099Proofs.DescriptiveComplexity.SecondOrderNewPull` and
`Lax624099Proofs.DescriptiveComplexity.SecondOrderNewOrdered`; hardness is *cofinal*, as
everywhere in this development (see `Lax624099Proofs.DescriptiveComplexity.hard_RE_iff`). -/
noncomputable def RE : ComplexityClass :=
  .ofMem (fun P => Lax624099.ValueInvention.SigmaSONewDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSONewDefinable_congr h)

/-- **co-RE**: the problems whose complement is recursively enumerable. Unlike
`coNP`, which the second-order quantifier duality identifies with `Π₁`
definability, this is only the complement operator applied to RE: `∃SO[new]`
has no dual reading here, and no inclusion between RE and co-RE is available at
this level. That the two classes differ is
`Lax624099Proofs.DescriptiveComplexity.RE_ne_coRE`. -/
noncomputable abbrev coRE : ComplexityClass := RE.compl

variable {L : Language.{0, 0}}

@[simp]
theorem mem_RE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : P ∈ RE ↔ Lax624099.ValueInvention.SigmaSONewDefinable P :=
  Iff.rfl

@[simp]
theorem mem_coRE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : P ∈ coRE ↔ Lax624099.ValueInvention.SigmaSONewDefinable Pᶜ :=
  Iff.rfl

/-- Over a relational vocabulary, cofinal RE-hardness is the usual notion:
every `∃SO[new]`-definable problem reduces to `P`. -/
theorem hard_RE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    RE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
        Lax624099.ValueInvention.SigmaSONewDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

end Lax624099Proofs.DescriptiveComplexity


