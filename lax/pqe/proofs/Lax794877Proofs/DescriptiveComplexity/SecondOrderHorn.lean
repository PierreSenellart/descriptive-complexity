/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.SecondOrder
import Lax794877Proofs.DescriptiveComplexity.Ordered
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax794877Proofs.DescriptiveComplexity.HornClause
end Lax794877Proofs.DescriptiveComplexity.HornClause

namespace Lax794877Proofs.DescriptiveComplexity.HornProgram
end Lax794877Proofs.DescriptiveComplexity.HornProgram

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax794877Proofs.DescriptiveComplexity

/-!
# SO-Horn: existential second-order logic with a Horn kernel

The fragment SO-Horn of Grädel ([Grädel 1992][gradel1992capturing]): existential
second-order sentences whose first-order kernel is a conjunction of *Horn
clauses* in the quantified relation variables. On ordered structures SO-Horn
captures polynomial time – the Horn kernel is exactly what makes the guessed
relations *determined* rather than merely guessed, since a satisfiable Horn
formula has a least model, computable by unit propagation.

## The kernel, as data

The Horn condition constrains only the occurrences of the *second-order*
variables: a clause is

```
guard(x̄) ∧ R₁(x̄) ∧ … ∧ Rₙ(x̄) → R₀(x̄)   (or → ⊥)
```

where `guard` is an arbitrary first-order formula over the *input* vocabulary
alone (in the definability notion below, over its ordered expansion). Rather
than carve this shape out of `FirstOrder.Language.BoundedFormula` with a
syntactic predicate, the kernel is represented here *as data*: a
`DescriptiveComplexity.HornClause` bundles its guard, the list of its body atoms and its
optional head atom, and a `DescriptiveComplexity.HornProgram` is a list of clauses
sharing `k` universally quantified first-order variables. This is Grädel's
clausal normal form, and it is what a reduction consuming an SO-Horn definition
needs to see: the discharge of `DescriptiveComplexity.Problems.HornSat.Hardness` reads the
clause list directly, and emits one propositional Horn clause per clause and
per instantiation of the `k` variables.

`DescriptiveComplexity.SigmaSOHornDefinable` is the resulting definability notion,
the SO-Horn analogue of `DescriptiveComplexity.SigmaSODefinable`; it is closed under
(ordered) first-order reductions by
`DescriptiveComplexity.SecondOrderHornPull`, which is what makes it a
`DescriptiveComplexity.ComplexityClass` – the class `DescriptiveComplexity.PTIME` of
`DescriptiveComplexity.Hierarchy`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Horn programs -/

/-! ### Semantics -/

section Semantics

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {A : Type} [L.Structure A]

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

end Iso

/-! ### SO-Horn definability -/

end Lax794877Proofs.DescriptiveComplexity


