/-
Mirror of `Lax751879.PolynomialTime`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding
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

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax751879.PolynomialTime
end Lax751879.PolynomialTime

namespace Lax751879.StructureEncoding
end Lax751879.StructureEncoding

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (PointedStructure Query Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding
export Lax751879.StructureEncoding (encode)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime
export Lax751879.PolynomialTime (InP language)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime

/-!
# Polynomial-time queries on ordered structures

A query is polynomial-time decidable when a finite deterministic Turing machine
decides the language of encodings of its satisfying pointed structures within a
polynomial in the input bit length. Malformed encodings are rejected. The machine
and polynomial are fixed for the query.

The machine model and step count are Mathlib's bundled finite multi-stack Turing
machines (`Turing.TM2ComputableInPolyTime`), with identity encoding on input bit
strings and a single output bit.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime

open OrderedStructures StructureEncoding

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime


