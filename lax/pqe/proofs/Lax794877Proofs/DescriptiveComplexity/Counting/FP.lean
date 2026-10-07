/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.QuantitativePull
import Lax794877Proofs.DescriptiveComplexity.FixedPoint
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax794877Proofs.DescriptiveComplexity.FPDefinable
end Lax794877Proofs.DescriptiveComplexity.FPDefinable

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (lfpAssign)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (FPDefinable)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation
export Lax859101.SubtractiveReductions.FOInterpretation (ordExtend)
end Lax904597.Interpretations.FOInterpretation

/-!
# The class FP

**FP** is the class of the *functions* computable in polynomial time. It is a
class of computations more than of counting: nothing in a function of FP has
to count anything. The library sees its natural-number-valued part, a
function from structures to numbers being what
`DescriptiveComplexity.CountingProblem` is, whether or not the number counts
solutions. This is the convention of the paper cited below, which defines FP
as the class of the functions `f : Σ* → ℕ` computable in polynomial time
(its Section 2.2), lists it among the “counting complexity classes”, and notes
that the value of a counting problem need not be a number of solutions.
Functions with other outputs (strings, structures, witnesses of a search
problem) are outside this formalization.

As a class of the library (`DescriptiveComplexity.FP`): the problems definable in
QFO(LFP), the first-order fragment of the quantitative logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive] over a Boolean layer of
least fixed points. That this logic captures FP over ordered structures is
their Theorem 4.4.

The class is closed under ordered parsimonious reductions
(`DescriptiveComplexity.FPDefinable.of_orderedParsimonious`): the least fixed
point pulls back through the interpretation as it does for PTIME
(`DescriptiveComplexity.lfpAssign_pull`), and the quantitative output as
`DescriptiveComplexity.QTerm.pull`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂}

/-- **FP is closed under ordered parsimonious reductions.** -/
theorem FPDefinable.of_orderedParsimonious (f : C ≤ᵖ[≤] D) (h : Lax366625.QuantitativeLogic.FPDefinable D) :
    Lax366625.QuantitativeLogic.FPDefinable C := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨⟨d.B.pull f.Tag f.dim, d.k * f.dim,
    HornProgram.pull f.toInterpretation.ordExtend d.rules,
    (d.out.pull (f.toInterpretation.ordExtend.extendSO d.B) Empty.elim).relabel
      fun p : Empty × Fin f.dim => p.1⟩, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [Lax366625.QuantitativeLogic.QLFPDef.value, Lax366625.QuantitativeLogic.QLFPDef.value, lfpAssign_pull f.toInterpretation.ordExtend d.rules]
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (Lax535992.LeastFixedPoint.lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (Lax535992.LeastFixedPoint.lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (Lax535992.LeastFixedPoint.lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  rw [← lfpAssign_map (f.toInterpretation.ordExtendLEquiv A) d.rules] at e₂
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    Lax904597.Interpretations.FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (Lax535992.LeastFixedPoint.lfpAssign d.rules))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (Lax535992.LeastFixedPoint.lfpAssign d.rules))
  have hout := QTerm.eval_equiv (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁)
    d.out ((f.toInterpretation.ordExtend.extendSO d.B).liftEnv Empty.elim
      (default : Empty × Fin f.dim → A))
  have hpull := QTerm.eval_pull (f.toInterpretation.ordExtend.extendSO d.B) (A := A) d.out
    Empty.elim (default : Empty × Fin f.dim → A)
  rw [Lax366625.QuantitativeLogic.QTerm.value, Lax366625.QuantitativeLogic.QTerm.value, QTerm.eval_relabel]
  have h1 : d.out.eval (A := f.toInterpretation.Map A) default =
      d.out.eval (⇑(e₂.comp e₁) ∘ (f.toInterpretation.ordExtend.extendSO d.B).liftEnv
        Empty.elim (default : Empty × Fin f.dim → A)) :=
    congrArg _ (Subsingleton.elim _ _)
  exact h1.trans (hout.trans (hpull.symm.trans (congrArg _ (Subsingleton.elim _ _))))

end Closure

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.FPDefinable

export Lax794877Proofs.DescriptiveComplexity.FPDefinable (of_orderedParsimonious)

end Lax366625.QuantitativeLogic.FPDefinable

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂}

end Closure

/-- **The class FP**, in its natural-number-valued part: the functions from
structures to numbers definable in QFO(LFP), i.e., computable in polynomial
time
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4). It is
closed under parsimonious reductions. -/
noncomputable def FP : CountingClass :=
  .ofMem (fun C => Lax366625.QuantitativeLogic.FPDefinable C)
    (fun f h => h.of_orderedParsimonious f)
    (fun h => ⟨fpDefinable_congr h, fpDefinable_congr fun A _ _ => (h A).symm⟩)

end Lax794877Proofs.DescriptiveComplexity


