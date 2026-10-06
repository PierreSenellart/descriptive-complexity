/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
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

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (HasSmallHittingSet HasSmallSetCover SSElem SSFam SSMarked SSMem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem ssElem ssFam ssMarked ssMem)
end FirstOrder.Language

/-!
# Set Cover and Hitting Set are transposes of each other

The inter-reduction inside the set family, the counterpart of the
complementation reductions of
`DescriptiveComplexity.Problems.CliqueFamily.Reductions`: the two problems are the
same condition read in the two directions of the incidence relation, so a
single interpretation of tag `Unit` and dimension 1
(`DescriptiveComplexity.transposeInterp`) – exchange the two unary marks, transpose
the incidence relation, keep the threshold – reduces each of them to the
other (`DescriptiveComplexity.setCover_fo_reduction_hittingSet` and
`DescriptiveComplexity.hittingSet_fo_reduction_setCover`), quantifier-free.

Set Packing has no such partner: its condition is not the transpose of
another problem of the family, and its hardness comes from graphs directly
(`DescriptiveComplexity.Problems.SetFamily.FromGraphs`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Set Cover and Hitting Set are transposes of each other -/

/-- The transposing interpretation: ground elements and sets of the family
exchange their marks, incidence is read backwards, the threshold is kept. -/
def transposeInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.SetFamily.setSystem Lax799700.SetFamily.setSystem Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .elem => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssFam (FirstOrder.Language.Term.var (0, 0))
    | _, .fam => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssElem (FirstOrder.Language.Term.var (0, 0))
    | _, .mem => fun _ => FirstOrder.Language.Relations.formula₂ Lax799700.SetFamily.ssMem (FirstOrder.Language.Term.var (1, 0)) (FirstOrder.Language.Term.var (0, 0))
    | _, .marked => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.SetFamily.ssMarked (FirstOrder.Language.Term.var (0, 0))

section TransposeCharacterizations

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A]

@[simp]
theorem transpose_elem (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssElem ![((), w)] ↔ RelMap Lax799700.SetFamily.ssFam ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_fam (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssFam ![((), w)] ↔ RelMap Lax799700.SetFamily.ssElem ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

@[simp]
theorem transpose_mem (w₁ w₂ : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssMem ![((), w₁), ((), w₂)] ↔
      RelMap Lax799700.SetFamily.ssMem ![w₂ 0, w₁ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₂]

@[simp]
theorem transpose_marked (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) Lax799700.SetFamily.ssMarked ![((), w)] ↔ RelMap Lax799700.SetFamily.ssMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]

end TransposeCharacterizations

section TransposeCorrectness

end TransposeCorrectness

end Lax280166Proofs.DescriptiveComplexity


