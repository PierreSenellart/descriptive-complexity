/-
Mirror of `Lax751879.StructureEncoding`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Action.Defs
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

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (PointedStructure Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding
export Lax751879.StructureEncoding (encode tuples unary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding

/-!
# Binary encodings of ordered structures and tuples

Encode a structure of size `n` by `n` one-bits and a zero-bit, followed by the
characteristic tables of its relations in vocabulary order, each listing tuples
in lexicographic order. The distinguished order is determined by `n` and needs
no table. Each coordinate `a` of the query tuple is appended as `a` one-bits and
a zero-bit.

The fixed vocabulary and query arity determine all table boundaries, so the
encoding is injective (`encodeInjective`), and its length is computed by
`encodeLength`.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding

open OrderedStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.StructureEncoding


