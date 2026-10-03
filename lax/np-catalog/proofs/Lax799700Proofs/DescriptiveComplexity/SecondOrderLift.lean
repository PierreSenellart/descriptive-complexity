/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
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

/-!
# Functoriality of block expansion, and padding with trivial blocks

Infrastructure for the second-order definability layer of
`Lax799700Proofs.DescriptiveComplexity.SecondOrder`:

* *Functoriality*: a language morphism `Φ : L →ᴸ L'` lifts through the
  expansion by a list of blocks (`Lax799700Proofs.DescriptiveComplexity.soLangLift`), and alternating
  second-order satisfaction is invariant when the base structure is expanded
  along `Φ` (`Lax799700Proofs.DescriptiveComplexity.sorealize_soLangLift`).
* *Embedded first-order sentences*: a sentence of the base language, embedded
  into the block expansion (`Lax799700Proofs.DescriptiveComplexity.soLangEmbed`), can be pulled out of
  the second-order quantification when it appears as a conjunct or as the
  premise of an implication (`Lax799700Proofs.DescriptiveComplexity.sorealize_inf_embed`,
  `Lax799700Proofs.DescriptiveComplexity.sorealize_imp_embed`). This is how the auxiliary order of an
  ordered reduction is eliminated: the order becomes a second-order variable
  of the first block, guarded by the first-order sentence “it is a linear
  order”.
* *Padding*: appending or prepending the trivial (empty) block
  (`Lax799700Proofs.DescriptiveComplexity.SOBlock.trivial`) does not change alternating second-order
  satisfaction (`Lax799700Proofs.DescriptiveComplexity.sorealize_append_trivial`), so `Σₖ`- and
  `Πₖ`-definability satisfy the level inclusions of the polynomial hierarchy:
  `Σₖ ⊆ Σₖ₊₁ ∩ Πₖ₊₁` and dually (`Lax799700Proofs.DescriptiveComplexity.SigmaSODefinable.succ`,
  `Lax799700Proofs.DescriptiveComplexity.SigmaSODefinable.piSucc`, `Lax799700Proofs.DescriptiveComplexity.PiSODefinable.succ`,
  `Lax799700Proofs.DescriptiveComplexity.PiSODefinable.sigmaSucc`).

Languages vary through all the inductions, so the recursive definitions and
statements take them as explicit arguments.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Assignments always exist -/

instance SOBlock.instNonemptyAssignment (B : Lax904597.SecondOrder.SOBlock) (A : Type) :
    Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

end Lax799700Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax799700Proofs.DescriptiveComplexity.SOBlock (instNonemptyAssignment)

end Lax904597.SecondOrder.SOBlock

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Functoriality of block expansion -/

/-! ### Embedding the base language into a block expansion -/

/-! ### The trivial block, and padding -/

/-! ### Level inclusions at the definability level -/

variable {L : Language.{0, 0}} [L.IsRelational] {k : ℕ} {P : Lax904597.Problems.DecisionProblem L}

end Lax799700Proofs.DescriptiveComplexity


