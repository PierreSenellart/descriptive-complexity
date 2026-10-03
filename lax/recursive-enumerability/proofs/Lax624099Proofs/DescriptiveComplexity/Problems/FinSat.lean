/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Problems.FinSat.Membership
import Lax624099Proofs.DescriptiveComplexity.Problems.FinSat.Reduction
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
# Trakhtenbrot's theorem: finite satisfiability is RE-complete

The umbrella of the `FINSAT` files. The problem
(`Lax624099Proofs.DescriptiveComplexity.FINSAT`) is: *given a first-order sentence, encoded as a
finite structure, does it have a finite model?* Its two halves are

* **membership** – `Lax624099Proofs.DescriptiveComplexity.finsat_mem_RE`: the model is
  *invented*, which is exactly what `∃SO[new]` (and nothing weaker) can do;
* **hardness** – `Lax624099Proofs.DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`: an
  `∃SO[new]` certificate is “a finite extension of the universe plus relations
  on it satisfying a fixed first-order kernel”, and a finite model of a sentence
  is “a finite universe plus relations on it satisfying a given first-order
  sentence”; the reduction is the translation of the first into the second.

Together: `Lax624099Proofs.DescriptiveComplexity.FINSAT_RE_complete`.

## Where the work is

The mathematical content of hardness is
`Lax624099Proofs.DescriptiveComplexity.FinSat.finsat_hard_of_sigmaSONewDefinable`, which builds
the sentence `σ_A` – an existential prefix naming the elements of the instance, a
diagram forcing them apart, and the negation-normal-form translation of the
kernel, whose atoms of the instance's own vocabulary are read by the
*interpretation* and never mentioned by the sentence. The construction works
because the source vocabulary is **relational** – as every vocabulary of a
`Lax624099Proofs.DescriptiveComplexity.DecisionProblem` is: the encoded sentence carries its own
quantifiers and would otherwise have to name what a function symbol does on an
invented value – an undefinable junk element.

## What the theorem does and does not say

RE here is the logically defined class of
`Lax624099Proofs.DescriptiveComplexity.RecursivelyEnumerable`, so this is “finite satisfiability
is complete for `∃SO[new]`”. It becomes *undecidability* of finite
satisfiability only through the bridge to Mathlib's computability layer,
`Lax624099Proofs.DescriptiveComplexity.Computability`, where the encoding of finite structures
as numbers turns it into `Lax624099Proofs.DescriptiveComplexity.finsat_not_computable`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **The hardness half of Trakhtenbrot's theorem**: every `∃SO[new]`-definable
problem admits an ordered first-order reduction to finite satisfiability –
`Lax624099Proofs.DescriptiveComplexity.FinSat.finsat_hard_of_sigmaSONewDefinable`, the encoded
sentence `σ_A`, in the relativized form hardness is stated in. -/
theorem finsat_hard_of_sigmaSONewDefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : Lax904597.Problems.DecisionProblem L),
      Lax624099.ValueInvention.SigmaSONewDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] FINSAT) := by
  intro L _ Q hQ
  obtain ⟨g⟩ := FinSat.finsat_hard_of_sigmaSONewDefinable Q hQ
  exact ⟨g.toRel⟩

/-- **Trakhtenbrot's theorem, in the logical form**: finite satisfiability of a
first-order sentence is RE-complete.

Membership is `Lax624099Proofs.DescriptiveComplexity.finsat_mem_RE`, hardness
`Lax624099Proofs.DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`. -/
theorem FINSAT_RE_complete : RE.Complete FINSAT :=
  ⟨finsat_mem_RE,
    (hard_RE_iff FINSAT).mpr fun Q hQ => finsat_hard_of_sigmaSONewDefinable Q hQ⟩

/-- FINSAT is RE-hard. -/
theorem finsat_RE_hard : RE.Hard FINSAT := FINSAT_RE_complete.hard

end Lax624099Proofs.DescriptiveComplexity


