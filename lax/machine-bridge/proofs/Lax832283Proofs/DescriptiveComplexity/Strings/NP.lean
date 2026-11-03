/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.Hierarchy
import Lax832283Proofs.DescriptiveComplexity.Strings.ExistentialSecondOrder
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.Captures
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
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax988886.ExistentialSecondOrder
end Lax988886.ExistentialSecondOrder

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax988886.NondeterministicPolynomialTime
end Lax988886.NondeterministicPolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (language)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
export Lax988886.ExistentialSecondOrder (Definable)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
export Lax988886.NondeterministicPolynomialTime (InNP LanguageInNP)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab toProperty)
end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax832283Proofs.DescriptiveComplexity

/-!
# The class NP, against certificates checked by a machine

The class `DescriptiveComplexity.NP` of this library is defined by second-order
logic. The theorems of this file say that, over a vocabulary with finitely many
relation symbols, it is the textbook class: a problem belongs to it exactly when the
language of the binary encodings of its yes-instances has polynomially bounded
certificates checked by a polynomial-time Mathlib `Turing.FinTM2`.

The logical half, `DescriptiveComplexity.Strings.mem_NP_iff_definable`, is
unconditional. The machine half takes Fagin's theorem as a hypothesis
(`DescriptiveComplexity.Strings.Lax.FaginCaptures`), which the Lax archive registers
as `lax-988886`.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder

open Lax.FiniteStructures Lax.NondeterministicPolynomialTime

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A problem is in `NP` exactly when it reads as a property of the archive's structures
defined by an existential second-order sentence of the archive. -/
theorem mem_NP_iff_definable (V : Lax832283.StringProblems.FinVocab L) (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ NP ↔ Lax988886.ExistentialSecondOrder.Definable (Lax832283.StringProblems.toProperty V P) :=
  sigmaSODefinable_one_iff V P

end Lax832283Proofs.DescriptiveComplexity.Strings


