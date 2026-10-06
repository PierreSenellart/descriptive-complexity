/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.SecondOrder
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

namespace Lax895169Proofs.DescriptiveComplexity.PiSODefinable
end Lax895169Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax895169Proofs.DescriptiveComplexity.SOBlock
end Lax895169Proofs.DescriptiveComplexity.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax895169Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Functoriality of block expansion, and padding with trivial blocks

Infrastructure for the second-order definability layer of
`DescriptiveComplexity.SecondOrder`:

* *Functoriality*: a language morphism `Φ : L →ᴸ L'` lifts through the
  expansion by a list of blocks (`DescriptiveComplexity.soLangLift`), and alternating
  second-order satisfaction is invariant when the base structure is expanded
  along `Φ` (`DescriptiveComplexity.sorealize_soLangLift`).
* *Embedded first-order sentences*: a sentence of the base language, embedded
  into the block expansion (`DescriptiveComplexity.soLangEmbed`), can be pulled out of
  the second-order quantification when it appears as a conjunct or as the
  premise of an implication (`DescriptiveComplexity.sorealize_inf_embed`,
  `DescriptiveComplexity.sorealize_imp_embed`). This is how the auxiliary order of an
  ordered reduction is eliminated: the order becomes a second-order variable
  of the first block, guarded by the first-order sentence “it is a linear
  order”.
* *Padding*: appending or prepending the trivial (empty) block
  (`DescriptiveComplexity.SOBlock.trivial`) does not change alternating second-order
  satisfaction (`DescriptiveComplexity.sorealize_append_trivial`), so `Σₖ`- and
  `Πₖ`-definability satisfy the level inclusions of the polynomial hierarchy:
  `Σₖ ⊆ Σₖ₊₁ ∩ Πₖ₊₁` and dually (`DescriptiveComplexity.SigmaSODefinable.succ`,
  `DescriptiveComplexity.SigmaSODefinable.piSucc`, `DescriptiveComplexity.PiSODefinable.succ`,
  `DescriptiveComplexity.PiSODefinable.sigmaSucc`).

Languages vary through all the inductions, so the recursive definitions and
statements take them as explicit arguments.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Assignments always exist -/

instance SOBlock.instNonemptyAssignment (B : Lax904597.SecondOrder.SOBlock) (A : Type) :
    Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (instNonemptyAssignment)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Functoriality of block expansion -/

/-! ### Embedding the base language into a block expansion -/

/-! ### The trivial block, and padding -/

/-! ### Level inclusions at the definability level -/

end Lax895169Proofs.DescriptiveComplexity


