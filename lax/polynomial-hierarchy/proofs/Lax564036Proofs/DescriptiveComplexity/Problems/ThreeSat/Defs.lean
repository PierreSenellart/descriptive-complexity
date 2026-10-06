/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.OccurrenceOrder
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

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.ThreeSat
end Lax799700.ThreeSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax799700.ThreeSat (ThreeSatisfiable WidthAtMostThree)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax564036Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (OccIn)
end Lax564036Proofs.DescriptiveComplexity.SatOcc

/-!
# 3SAT: definition

The problem 3SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT: a
CNF structure is a yes-instance iff every clause has at most three literal
occurrences (`DescriptiveComplexity.WidthAtMostThree`) *and* the CNF is satisfiable
(`DescriptiveComplexity.ThreeSatisfiable`, bundled as `DescriptiveComplexity.ThreeSAT`).

Folding the width bound into the yes-instances (rather than into the
vocabulary) is what makes 3SAT a decision problem on arbitrary
`Language.sat`-structures; the bound “at most three” is expressed without
counting, as: among any four literal occurrences of a clause, two coincide.

The reductions to and from SAT, and NP-completeness, are in
`DescriptiveComplexity.Problems.ThreeSat`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

section ThreeSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end ThreeSat

section Iso

/-- Isomorphisms preserve literal occurrences. -/
private theorem occIn_map {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) {c x : A} {s : Bool} (h : Lax799700.Common.SatOcc.OccIn c x s) : Lax799700.Common.SatOcc.OccIn (e c) (e x) s := by
  obtain ⟨hc, hs⟩ := h
  constructor
  · exact (relMap_equiv₁ e Lax904597.Sat.satIsClause c).mp hc
  · cases s with
    | false => exact (relMap_equiv₂ e Lax904597.Sat.satNegIn c x).mp hs
    | true => exact (relMap_equiv₂ e Lax904597.Sat.satPosIn c x).mp hs

private theorem widthAtMostThree_of_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) (h : Lax799700.ThreeSat.WidthAtMostThree A) :
    Lax799700.ThreeSat.WidthAtMostThree B := by
  intro c x s hocc
  obtain ⟨i, j, hij, hx, hs⟩ :=
    h (e.symm c) (fun i => e.symm (x i)) s fun i => occIn_map e.symm (hocc i)
  refine ⟨i, j, hij, ?_, hs⟩
  have := congrArg e hx
  simpa using this

/-- The width bound is isomorphism-invariant. -/
theorem widthAtMostThree_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    Lax799700.ThreeSat.WidthAtMostThree A ↔ Lax799700.ThreeSat.WidthAtMostThree B :=
  ⟨widthAtMostThree_of_iso e, widthAtMostThree_of_iso e.symm⟩

end Iso

end Lax564036Proofs.DescriptiveComplexity


