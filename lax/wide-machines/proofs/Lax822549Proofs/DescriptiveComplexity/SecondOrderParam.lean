/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrder
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

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

/-!
# A block with one argument more

Two constructions want the same operation on a block of relation variables: an
iteration run *at a parameter* (`DescriptiveComplexity.FixedPointParam`) gives
every variable the parameter as a further argument, and a kernel whose variables
must all have an argument
(`DescriptiveComplexity.Exponential.KernelArity`) gives them a dummy one. The
block, the symbol map and the way an assignment of the extended block is read at
one value of the extra argument are the same in both, and are here.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

/-- The block `B` with one extra argument on every relation variable: the
parameter the iteration is run at. -/
def SOBlock.withParam (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := B.ι
  arity i := B.arity i + 1

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (withParam)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

/-- A relation variable of the block, read at the extended block: one argument
more. -/
def SOBlock.paramSym (B : Lax904597.SecondOrder.SOBlock) {m : ℕ} (r : B.lang.Relations m) :
    B.withParam.lang.Relations (m + 1) :=
  ⟨r.1, congrArg (· + 1) r.2⟩

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (paramSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

variable {N : Type}

/-- An assignment of the extended block, read at one parameter. -/
def SOBlock.atParam (B : Lax904597.SecondOrder.SOBlock) (ρ : B.withParam.Assignment N) (c : N) : B.Assignment N :=
  fun i x => ρ i (Fin.cons c x)

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (atParam)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

variable {N : Type}

/-- **Reading a parameterized relation variable**: the extended variable at a
tuple whose first argument is the parameter is the original variable, read at
the assignment taken at that parameter. -/
theorem SOBlock.relMap_paramSym (B : Lax904597.SecondOrder.SOBlock) (ρ : B.withParam.Assignment N) (c : N) {m : ℕ}
    (b : B.lang.Relations m) (w : Fin (m + 1) → N) (hw : w 0 = c) :
    (@RelMap B.withParam.lang N (B.withParam.structure ρ) (m + 1) (B.paramSym b) w ↔
      @RelMap B.lang N (B.structure (B.atParam ρ c)) m b fun i => w i.succ) := by
  have hvec : (fun j => w (Fin.cast (congrArg (· + 1) b.2) j)) =
      Fin.cons c fun j => w (Fin.cast b.2 j).succ := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Fin.cons_zero]
      exact (congrArg w (Fin.ext rfl)).trans hw
    · rw [Fin.cons_succ]
      exact congrArg w (Fin.ext rfl)
  exact iff_of_eq (congrArg (ρ b.1) hvec)

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (relMap_paramSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

variable {N : Type}

end Lax822549Proofs.DescriptiveComplexity


