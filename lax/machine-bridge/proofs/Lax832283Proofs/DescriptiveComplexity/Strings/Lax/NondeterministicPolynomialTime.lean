/-
Mirror of `Lax988886.NondeterministicPolynomialTime`: lax-988886, “Fagin's theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
import Mathlib.Computability.TuringMachine.Computable
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

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax988886.NondeterministicPolynomialTime
end Lax988886.NondeterministicPolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (Property Vocabulary language)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
export Lax988886.NondeterministicPolynomialTime (InNP LanguageInNP encodePair)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime

/-!
# NP through polynomially bounded certificates

A bit-string language belongs to NP if membership is equivalent to the existence
of a certificate of polynomially bounded length accepted by a deterministic
polynomial-time verifier: the usual certificate definition of NP, the verifier
being a concrete finite multi-stack Turing machine of Mathlib with its
machine-step polynomial bound.

The verifier reads a pair of bit strings: each input bit is preceded by a
one-bit, a zero-bit terminates the input, and the remaining bits form the
certificate. A property belongs to NP when its language of structure encodings
does; the language excludes malformed encodings.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime

open FiniteStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime


