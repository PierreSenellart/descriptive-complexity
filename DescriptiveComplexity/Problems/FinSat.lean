/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Membership
import DescriptiveComplexity.Problems.FinSat.Reduction
import DescriptiveComplexity.Relationalize

/-!
# Trakhtenbrot's theorem: finite satisfiability is RE-complete

The umbrella of the `FINSAT` files. The problem
(`DescriptiveComplexity.FINSAT`) is: *given a first-order sentence, encoded as a
finite structure, does it have a finite model?* Its two halves are

* **membership** – `DescriptiveComplexity.finsat_mem_RE`: the model is
  *invented*, which is exactly what `∃SO[new]` (and nothing weaker) can do;
* **hardness** – `DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`: an
  `∃SO[new]` certificate is “a finite extension of the universe plus relations
  on it satisfying a fixed first-order kernel”, and a finite model of a sentence
  is “a finite universe plus relations on it satisfying a given first-order
  sentence”; the reduction is the translation of the first into the second.

Together: `DescriptiveComplexity.FINSAT_RE_complete`.

## Where the work is

The mathematical content of hardness is
`DescriptiveComplexity.FinSat.finsat_hard_of_sigmaSONewDefinable`, which builds
the sentence `σ_A` – an existential prefix naming the elements of the instance, a
diagram forcing them apart, and the negation-normal-form translation of the
kernel, whose atoms of the instance's own vocabulary are read by the
*interpretation* and never mentioned by the sentence. It asks the source
vocabulary to be **relational**, because the encoded sentence carries its own
quantifiers and would otherwise have to name what a function symbol does on an
invented value – an undefinable junk element.

`DescriptiveComplexity.CofinalHard` quantifies over every source vocabulary, and
the step from one to the other is
`DescriptiveComplexity.exists_relational_of_sigmaSONewDefinable`
(`DescriptiveComplexity.Relationalize`): every `∃SO[new]`-definable problem
reduces to an `∃SO[new]`-definable problem over the atomic diagram language.

## What the theorem does and does not say

RE here is the logically defined class of
`DescriptiveComplexity.RecursivelyEnumerable`, so this is “finite satisfiability
is complete for `∃SO[new]`”. It becomes *undecidability* of finite
satisfiability only through the bridge to Mathlib's computability layer,
`DescriptiveComplexity.Computability`, where the encoding of finite structures
as numbers turns it into `DescriptiveComplexity.finsat_not_computable`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **The hardness half of Trakhtenbrot's theorem**: every `∃SO[new]`-definable
problem, over *any* vocabulary, admits an ordered first-order reduction to
finite satisfiability.

The source is first moved to a relational vocabulary
(`DescriptiveComplexity.exists_relational_of_sigmaSONewDefinable`), where
`DescriptiveComplexity.FinSat.finsat_hard_of_sigmaSONewDefinable` – the encoded
sentence `σ_A` – applies. -/
theorem finsat_hard_of_sigmaSONewDefinable :
    ∀ {L : Language.{0, 0}} (Q : DecisionProblem L),
      SigmaSONewDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] FINSAT) := by
  intro L Q hQ
  obtain ⟨L', hrel, Q', hQ', ⟨f⟩⟩ := exists_relational_of_sigmaSONewDefinable hQ
  haveI := hrel
  obtain ⟨g⟩ := FinSat.finsat_hard_of_sigmaSONewDefinable Q' hQ'
  exact ⟨f.toOrdered.toRel.trans g.toRel⟩

/-- **Trakhtenbrot's theorem, in the logical form**: finite satisfiability of a
first-order sentence is RE-complete.

Membership is `DescriptiveComplexity.finsat_mem_RE`, hardness
`DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`. -/
theorem FINSAT_RE_complete : RE.Complete FINSAT :=
  ⟨finsat_mem_RE,
    (hard_RE_iff FINSAT).mpr fun Q hQ => finsat_hard_of_sigmaSONewDefinable Q hQ⟩

/-- FINSAT is RE-hard. -/
theorem finsat_RE_hard : RE.Hard FINSAT := FINSAT_RE_complete.hard

end DescriptiveComplexity
