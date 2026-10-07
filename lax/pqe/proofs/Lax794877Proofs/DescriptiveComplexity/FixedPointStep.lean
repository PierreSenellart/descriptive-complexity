/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Lattice.Nat
import Lax794877Proofs.DescriptiveComplexity.FixedPoint
import Lax794877Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax794877Proofs.DescriptiveComplexity.OrderedComposition
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
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

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax794877Proofs.DescriptiveComplexity.SOBlock
end Lax794877Proofs.DescriptiveComplexity.SOBlock

namespace Lax794877Proofs.DescriptiveComplexity.StepDef
end Lax794877Proofs.DescriptiveComplexity.StepDef

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Simultaneous first-order inductions: one skeleton for IFP and PFP

The inflationary (FO(IFP)) and partial (FO(PFP)) fixed-point logics differ in
exactly one place – what one application of the step formulas does with the
previous stage. Everything else is shared: the data (a block of relation
variables, one first-order step formula per variable, an output sentence), the
notion of a stage, stabilization on finite structures, transport along
isomorphisms, and the pullback along a first-order interpretation. This file
provides that shared skeleton; the logics themselves are built on it in
`DescriptiveComplexity.FixedPointInflationary` and
`DescriptiveComplexity.FixedPointPartial`.

## The data

A `DescriptiveComplexity.StepDef` over `L` bundles a block `B` of relation
variables, one step *formula* per variable – a first-order formula over
`L.sum B.lang` whose free variables are the arguments of the variable – and an
output sentence over the same expanded vocabulary. This is one *simultaneous*
induction with a first-order output; nesting is treated by stratification, in
`DescriptiveComplexity.FixedPointInflationary`.

Unlike `DescriptiveComplexity.LFPDef`, whose rules are clausal *data* (the
library's Horn-program normal form), the step formulas here are unrestricted:
positivity is exactly what the inflationary and partial iterations dispense
with. `LFPDef` keeps its clausal form – the two are bridged in
`DescriptiveComplexity.FixedPointInflationary` (rules give a `StepDef`) and
`DescriptiveComplexity.FixedPointInflationaryLFP` (the converse translation).

## The two iterations

* `DescriptiveComplexity.StepDef.inflStage`: iterate
  `DescriptiveComplexity.StepDef.inflStep`, which *accumulates* the step
  formulas into the previous stage. The stages grow, so on a finite structure
  they reach a fixed point within the atom count
  (`DescriptiveComplexity.StepDef.isFixedPt_inflStep_card` – the height of the
  subset lattice, via
  `DescriptiveComplexity.exists_succ_eq_of_monotone_subset`), and their union
  `DescriptiveComplexity.StepDef.inflLimit` equals the stage at the atom count
  (`DescriptiveComplexity.StepDef.inflLimit_eq_stage_card`).
* `DescriptiveComplexity.StepDef.partStage`: iterate
  `DescriptiveComplexity.StepDef.next` itself, *replacing* the previous stage.
  Nothing grows, and the iteration may cycle forever; if some stage is a fixed
  point, all fixed stages are equal
  (`DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt`) and one is
  reached within `Nat.card` of the *assignment* type – the pigeonhole
  `DescriptiveComplexity.isFixedPt_iterate_card_iff`, exposed here as
  `DescriptiveComplexity.StepDef.exists_isFixedPt_partStage_iff`.

## Transport

Both iterations commute with transporting an assignment along an isomorphism
(`DescriptiveComplexity.StepDef.inflStage_map`,
`DescriptiveComplexity.StepDef.partStage_map`) and with the pullback of the
block through a first-order interpretation
(`DescriptiveComplexity.StepDef.inflStage_pull`,
`DescriptiveComplexity.StepDef.partStage_pull`, for the pulled definition
`DescriptiveComplexity.StepDef.pull`). Each is one commuting lemma about
`DescriptiveComplexity.StepDef.next` (`next_map`, `next_pull`) propagated along
the orbit; these are the lemmas isomorphism-invariance and closure under
reductions rest on, for every logic built on this skeleton.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### Assignments form a finite type -/

instance {B : Lax904597.SecondOrder.SOBlock} {A : Type} [Finite A] : Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))

/-! ### Realization transport with explicit structures

The structures a stage is read against are block expansions, which are not
instances; this is `FirstOrder.Language.StrongHomClass.realize_formula` with
the two structures passed explicitly, exactly as
`DescriptiveComplexity.realize_sentence_of_equiv` does at the sentence level. -/

/-! ### The data of a simultaneous induction -/

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

/-! ### Stabilization on finite structures -/

section Stab

end Stab

/-! ### Transport along isomorphisms -/

section Map

end Map

end StepDef

/-! ### Pullback through an interpretation -/

namespace StepDef

section Pull

end Pull

end StepDef

end Lax794877Proofs.DescriptiveComplexity


