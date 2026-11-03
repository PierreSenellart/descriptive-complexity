/-
Mirror of `Lax988886.ExistentialSecondOrder`: lax-988886, “Fagin's theorem”, formalized by Szymon
Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
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

namespace Lax988886.ExistentialSecondOrder
end Lax988886.ExistentialSecondOrder

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (Interpretation Isomorphism IsomorphismInvariant Property Structure Symbol Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
export Lax988886.ExistentialSecondOrder (Definable FirstOrder Satisfies Sentence)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

/-!
# Existential second-order logic

An existential second-order sentence has the form `∃ R₁ … ∃ Rₛ, φ`, where each
relation has a fixed arity and the matrix `φ` is first-order. Witness relations
range over all relations of their arities on the existing universe.

The first-order basis consists of truth, equality, input-relation and
witness-relation atoms, negation, conjunction, and existential element
quantification. There is no built-in order or fixed-point operator. Element
quantification binds variable zero. The witness vocabulary records the finite
second-order quantifier prefix.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

open FiniteStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder


