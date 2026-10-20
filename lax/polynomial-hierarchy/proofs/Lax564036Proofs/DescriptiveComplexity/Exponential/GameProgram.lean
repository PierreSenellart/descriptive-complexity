/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Complexity
import Lax564036Proofs.DescriptiveComplexity.Composition
import Lax564036Proofs.DescriptiveComplexity.FixedPointStep
import Lax564036Proofs.DescriptiveComplexity.OrderedComposition
import Lax564036Proofs.DescriptiveComplexity.SecondOrderPull
import Lax564036Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Finite
import Lax564036Proofs.DescriptiveComplexity.Complexity
import Lax564036Proofs.DescriptiveComplexity.FixedPoint
import Lax564036Proofs.DescriptiveComplexity.FixedPointHorn
import Lax564036Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax564036Proofs.DescriptiveComplexity.Interpretation
import Lax564036Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax564036Proofs.DescriptiveComplexity.OrderWalk
import Lax564036Proofs.DescriptiveComplexity.Ordered
import Lax564036Proofs.DescriptiveComplexity.Padding
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat.Unsat
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Program
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Tape
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat.TseitinFormulas
import Lax564036Proofs.DescriptiveComplexity.SecondOrder
import Lax564036Proofs.DescriptiveComplexity.Vocabulary
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The six questions a machine playing a second-order game must answer

`DescriptiveComplexity.Exponential.AltQuant` and
`DescriptiveComplexity.Exponential.BlockClaim` are the two normal forms; this
file applies them to an `DescriptiveComplexity.SOGameSpec` and packages the
result as the interface a machine consumes.

## The six questions

A machine playing the game of a specification has to decide six sentences, not
four: the three one-copy sentences `won`, `univ`, `start`, the two-copy
sentence `move`, and the **negations** of `univ` and of `move`. The negations
are not a redundancy – a sentence is always used in the positive direction, an
existential branch that *proves* it and gets stuck otherwise, so refuting one
means proving another (`DescriptiveComplexity.GameQuestion`).

`DescriptiveComplexity.SOGameSpec.question` reads all six in the *same*
language, the two-copy one, the one-copy sentences traveling along
`FirstOrder.Language.LHom.sumInl`; that uniformity is what lets the machine's
tag be a plain product rather than a dependent sum.

## What the interface says

`DescriptiveComplexity.QuestionData` is what the machine's control needs about
one question:

* `vars` and `pol` – the length of the alternating prefix and whose turn each
  variable is, so a prefix phase is an index and a tuple coordinate;
* `atoms` – the occurrences of block atoms in the matrix, each an *address* on
  the tape;
* `sub` – for each vector of claimed truth values, the residual formula over
  the **base** vocabulary, which the interpretation writes into a transition
  guard.

`DescriptiveComplexity.QuestionData.Plays` states that this data decides the
sentence, and `DescriptiveComplexity.exists_questionData` produces it. The
matrix condition is stated as
`DescriptiveComplexity.QuestionData.MatrixHolds` – *there is a vector of
correct claims whose residual formula holds* – which is literally the round the
machine plays: the existential player claims the whole vector in one move, the
universal player challenges one claim by a tape lookup or lets the residual
formula be evaluated.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language BoundedFormula

/-! ### Reading a one-copy sentence in the two-copy language -/

section SumInl

end SumInl

/-! ### The six questions -/

/-- **The six sentences a machine playing a second-order game must decide.**
The two negations are separate questions because a machine only ever *proves*:
an existential branch that fails to prove its sentence runs out of transitions,
so refuting a sentence has to be proving another one. -/
inductive GameQuestion
  /-- The current position wins outright. -/
  | won
  /-- The current position belongs to the universal player. -/
  | univ
  /-- The current position belongs to the existential player. -/
  | notUniv
  /-- The move from the current position to the candidate is legal. -/
  | move
  /-- The move from the current position to the candidate is illegal. -/
  | notMove
  /-- The current position starts the game. -/
  | start
  deriving DecidableEq

instance : Fintype GameQuestion :=
  ⟨{.won, .univ, .notUniv, .move, .notMove, .start}, by intro x; cases x <;> simp⟩

namespace SOGameSpec

end SOGameSpec

/-! ### What the machine needs to know about one question -/

namespace QuestionData

end QuestionData

end Lax564036Proofs.DescriptiveComplexity


