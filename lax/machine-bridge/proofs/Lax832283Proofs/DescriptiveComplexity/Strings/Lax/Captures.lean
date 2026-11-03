/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime
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

namespace Lax751879.FixedPointSemantics
end Lax751879.FixedPointSemantics

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax751879.PolynomialTime
end Lax751879.PolynomialTime

namespace Lax988886.ExistentialSecondOrder
end Lax988886.ExistentialSecondOrder

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax988886.NondeterministicPolynomialTime
end Lax988886.NondeterministicPolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (Query Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
export Lax751879.FixedPointSemantics (Definable)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime
export Lax751879.PolynomialTime (InP)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.PolynomialTime

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (IsomorphismInvariant Property Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
export Lax988886.ExistentialSecondOrder (Definable)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime
export Lax988886.NondeterministicPolynomialTime (InNP)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.NondeterministicPolynomialTime

/-!
# The capture theorems of the Lax archive, as statements

Fagin's theorem (`lax-988886`) and the Immerman–Vardi theorem (`lax-751879`), as
stated in the archive, for the mirrored definitions of this directory. They are
propositions here, hypotheses of the bridge theorems of
`DescriptiveComplexity.Strings`, and nothing in this library proves them: a Lax
submission replaces the mirror by the two entries, where each is one application
of a registered statement.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax

/-- **Fagin's theorem**, as registered: on finite structures, an
isomorphism-invariant property is existential second-order definable exactly when
its language of encodings is in NP. -/
def FaginCaptures : Prop :=
  ∀ {σ : Lax988886.FiniteStructures.Vocabulary} (Q : Lax988886.FiniteStructures.Property σ),
    Lax988886.FiniteStructures.IsomorphismInvariant Q →
      (Lax988886.ExistentialSecondOrder.Definable Q ↔ Lax988886.NondeterministicPolynomialTime.InNP Q)

/-- **The Immerman–Vardi theorem**, as registered: on finite ordered structures, a
query is FO(LFP)-definable exactly when a machine decides its language of
encodings in polynomial time. -/
def ImmermanVardiCaptures : Prop :=
  ∀ {σ : Lax751879.OrderedStructures.Vocabulary} {k : ℕ} (Q : Lax751879.OrderedStructures.Query σ k),
    Lax751879.FixedPointSemantics.Definable Q ↔ Lax751879.PolynomialTime.InP Q

end Lax832283Proofs.DescriptiveComplexity.Strings.Lax


