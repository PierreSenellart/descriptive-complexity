/-
Mirror of `Lax988886.FiniteStructures`: lax-988886, “Fagin's theorem”, formalized by Szymon
Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding
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

namespace Lax751879.StructureEncoding
end Lax751879.StructureEncoding

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure Symbol Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding
export Lax751879.StructureEncoding (encode)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (Interpretation Isomorphism IsomorphismInvariant Property Structure Symbol Vocabulary encode language)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

/-!
# Finite relational structures and their properties

A structure has universe `Fin n` and an interpretation of each relation. The
numbering is used for binary input encodings; it is not available as an order
predicate in the logic. Properties are required to be invariant under
isomorphism, so they do not depend on the numbering. The representation and
dense binary encoding are reused from the Immerman–Vardi entry, forgetting its
distinguished order. Empty universes and nullary relations are allowed.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures


