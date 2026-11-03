/-
Mirror of `Lax751879.FixedPointSyntax`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
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

namespace Lax751879.FixedPointSyntax
end Lax751879.FixedPointSyntax

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (Symbol Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax
export Lax751879.FixedPointSyntax (Formula RawFormula Sentence)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax

/-!
# First-order logic with least fixed points

FO(LFP) extends first-order logic with `[lfp_{R, x̄} φ](ȳ)`, where every
occurrence of `R` in `φ` is positive (under an even number of negations). Fixed
points may be nested, negated, and have free first-order parameters. Equality,
order, relation atoms, negation, conjunction, and existential quantification
form the first-order basis; truth is included explicitly.

The indices record the number of available element variables and the arities of
available relation variables. A quantifier binds element variable zero. A fixed
point binds relation variable zero and the first `k` element variables of its
body; the remaining variables are parameters.

Raw syntax is separated from admissibility solely to express the positivity
check. A `Formula` always includes admissibility at every nested fixed point.
`positiveAt` traverses nested binders, shifting the relation-variable index, and
tracks the parity of negations.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax

open OrderedStructures

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax


