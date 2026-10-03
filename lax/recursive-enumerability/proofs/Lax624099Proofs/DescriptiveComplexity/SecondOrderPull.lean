/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Composition
import Lax624099Proofs.DescriptiveComplexity.SecondOrder
import Mathlib.Data.Finite.Sigma
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

namespace Lax624099Proofs.DescriptiveComplexity.FOInterpretation
end Lax624099Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax624099Proofs.DescriptiveComplexity.PiSODefinable
end Lax624099Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax624099Proofs.DescriptiveComplexity.SOBlock
end Lax624099Proofs.DescriptiveComplexity.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable

/-!
# Pulling second-order definability back through an interpretation

If `P ≤ᶠᵒ Q` and `Q` is `Σₖ`- (resp. `Πₖ`-) definable, then so is `P`
(`Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.of_foReduction`,
`Lax624099Proofs.DescriptiveComplexity.PiSODefinable.of_foReduction`): the levels of the polynomial
hierarchy, defined by second-order alternation, are closed under first-order
reductions.

The proof pulls the defining second-order sentence back through the
interpretation `I` underlying the reduction, block by block:

* a second-order quantifier over an `n`-ary relation on the interpreted
  universe `Tag × A^d` becomes a family of second-order quantifiers over
  `(n·d)`-ary relations on `A`, one per `n`-tuple of tags
  (`Lax624099Proofs.DescriptiveComplexity.SOBlock.pull`; assignments transfer bijectively via
  `Lax624099Proofs.DescriptiveComplexity.SOBlock.pullAssign` / `Lax624099Proofs.DescriptiveComplexity.SOBlock.mergeAssign`);
* the interpretation extends to the languages expanded by a block
  (`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.extendSO`): relation variables of the block
  are interpreted by the corresponding pulled relation variables, reading the
  tag tuple off statically; interpreting-then-expanding agrees with
  expanding-then-interpreting (`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.extendSOEquiv`);
* the first-order kernel is pulled back by
  `Lax624099Proofs.DescriptiveComplexity.FOInterpretation.pull` from `Lax624099Proofs.DescriptiveComplexity.Composition`, packaged
  at the sentence level as `Lax624099Proofs.DescriptiveComplexity.FOInterpretation.pullSentence`.

`Lax624099Proofs.DescriptiveComplexity.sorealize_pullSO` puts these together: alternating second-order
satisfaction in the interpreted structure coincides with alternating
second-order satisfaction of the pulled sentence (over the pulled blocks) in
the base structure.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Pulling back a sentence -/

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

end PullSentence

/-! ### Pulling back a block -/

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

/-- The pullback of a second-order quantifier block through a tagged
`d`-dimensional interpretation: an `n`-ary relation variable on the
interpreted universe `Tag × A^d` becomes one `(n·d)`-ary relation variable on
`A` per `n`-tuple of tags. -/
def SOBlock.pull (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Σ i : B.ι, Fin (B.arity i) → Tag
  arity p := B.arity p.1 * d

end PullBlock

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (pull)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

end PullBlock

/-! ### Extending an interpretation along a block -/

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (B : Lax904597.SecondOrder.SOBlock) (A : Type)

variable [instA : L₁.Structure A]

end ExtendSO

/-! ### Pulling back an alternating second-order sentence -/

section PullSO

variable {Tag : Type} {d : ℕ} [Finite Tag]

end PullSO

/-! ### Closure of the definability levels under FO reductions -/

section Closure

variable [L₁.IsRelational] [L₂.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

variable {k : ℕ}

end Closure

/-! ### Pulling back atoms, guards and tag assignments

The clausal fragments (SO-Horn, SO-Krom) pull a *clause list* back through an
interpretation rather than a formula: each clause becomes one clause per static
assignment of tags to its universally quantified variables, its guard becoming
an ordinary formula pullback and its atoms becoming atoms of the pulled
relation variables. The pieces that do not depend on the shape of a clause are
collected here, and are shared by `Lax624099Proofs.DescriptiveComplexity.SecondOrderHornPull` and
`Lax624099Proofs.DescriptiveComplexity.SecondOrderKromPull`. -/

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

section Guards

variable [L₂.IsRelational]

end Guards

end Clausal

end Lax624099Proofs.DescriptiveComplexity


