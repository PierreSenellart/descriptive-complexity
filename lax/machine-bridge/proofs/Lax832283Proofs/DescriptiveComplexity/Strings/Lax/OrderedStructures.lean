/-
Mirror of `Lax751879.OrderedStructures`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
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

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure PointedStructure Query Symbol Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

/-!
# Finite ordered relational structures and queries

A finite relational vocabulary is a finite list of arities. An ordered
structure of size `n` has universe `{0, …, n - 1}`, its usual strict order, and
an interpretation of each relation symbol: the canonical representative of a
finite linearly ordered structure up to isomorphism. The order is available to
formulas as a distinguished atomic predicate.

A pointed structure additionally carries a `k`-tuple of elements, and a `k`-ary
query is a property of these pointed structures; `k = 0` gives Boolean queries.
Empty universes and nullary relation symbols are allowed. The vocabulary and
query arity are fixed independently of the input structure.

The declarations of this directory mirror two entries of the Lax archive: see
`DescriptiveComplexity.Strings`.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures


