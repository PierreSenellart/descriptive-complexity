/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexDef
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawInterp
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The clocked machine, written down

`DescriptiveComplexity.Draw.Data.reads_progFrom` says of a program that the
interpreted structure reads its table, and it says it of
`DescriptiveComplexity.Draw.Data.progFrom` – the program assembled from a
definable rule set, a start phase, an accepting predicate and an initial mark.
The clocked program is written by hand (`DescriptiveComplexity.Draw.Data.nexProg`),
so what is needed here is that the two are the *same program*: they differ in
one field only, the initial pointer, and there the file's first register carries
the least tuple, which is clear at every coordinate.

With that, the clocked machine is written down exactly as the space-bounded one
is: `nexInterp` is the interpretation and `reads_nexProg` the fact a reduction
hands the run layer. What is left to a reduction emitting it is its own
`DescriptiveComplexity.Draw.Data.VarArgs`, the obligation the space-bounded
reduction already meets.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} {dt : Data L}

variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] [Finite dt.KIx] [Nonempty dt.KIx]

/-- **The clocked program's phases.** -/
abbrev NexPF (dt : Data L) : Type := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)

/-! ### The interpretation, and what it reads

The clocked program's guess writes one bit per fixed-point variable of the
source, so the guessed data of its outer layer is `dt.d.B.ι → Bool`; that is the
rule names' second component, and the reduction supplies the two orders on the
names and the phases (any linear order will do – they are finite types). -/

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


