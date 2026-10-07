/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting
import Lax794877Proofs.DescriptiveComplexity.RelComposition
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

namespace Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem RelOrderedParsimoniousReduction)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Relativized parsimonious reductions

The counting counterpart of `DescriptiveComplexity.RelOrderedFOReduction`: an ordered
parsimonious reduction through a *relativized* interpretation, whose target
universe is the definable subset a domain formula carves out of `Tag × A^dim`
(`DescriptiveComplexity.RelOrderedParsimoniousReduction`, notation `C ≤ʳᵖ[≤] D`).

It is needed for the same reason as on the decision side. A counting problem
whose solutions *span* the universe – the Hamilton circuits of a graph – cannot
be the target of an ordinary interpretation: the tagged tuples that stand for
nothing would each have to lie on every circuit. With a definable domain they
are simply not there.

* `DescriptiveComplexity.OrderedParsimoniousReduction.toRel`: an ordinary ordered
  parsimonious reduction is a relativized one, with domain `⊤`;
* `DescriptiveComplexity.RelOrderedParsimoniousReduction.trans`: transitivity, by the
  guarded composition of `DescriptiveComplexity.RelComposition`;
* `DescriptiveComplexity.RelOrderedParsimoniousReduction.toRelOrderedFOReduction`: it
  is a relativized reduction between the supports.

Parsimonious hardness for the counting classes of
`DescriptiveComplexity.Counting.Class` is hardness under these reductions, as hardness
for the decision classes is hardness under `≤ʳᶠᵒ[≤]`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 C:51 " ≤ʳᵖ[≤] " D:51 => Lax366625.CountingProblems.RelOrderedParsimoniousReduction C D

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- The relativized universe of the output of a reduction is nonempty on
nonempty finite ordered inputs. -/
theorem RelOrderedParsimoniousReduction.mapRel_nonempty (f : C ≤ʳᵖ[≤] D) (A : Type)
    [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (f.toRelInterpretation.MapRel A) :=
  let ⟨t, w, h⟩ := f.dom_nonempty A
  ⟨⟨(t, w), h⟩⟩

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (mapRel_nonempty)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- An ordinary ordered parsimonious reduction is a relativized one with `⊤`
domain. -/
def OrderedParsimoniousReduction.toRel (f : C ≤ᵖ[≤] D) : C ≤ʳᵖ[≤] D :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toInterpretation.toRel
    dom_nonempty := fun A => ⟨Classical.arbitrary f.Tag, fun _ => Classical.arbitrary A,
      Formula.realize_top.mpr trivial⟩
    correct := fun A => (f.correct A).trans (D.iso_invariant (f.toInterpretation.toRelLEquiv A)) }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction (toRel)

end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- Replacing the target of a relativized parsimonious reduction by a counting
problem with the same values on finite structures. -/
def RelOrderedParsimoniousReduction.congrTarget {D' : Lax366625.CountingProblems.CountingProblem L'}
    (h : ∀ (A : Type) [L'.Structure A] [Finite A], D A = D' A) (g : C ≤ʳᵖ[≤] D) :
    C ≤ʳᵖ[≤] D' :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    correct := fun A _ _ _ _ =>
      haveI := g.toRelInterpretation.mapRel_finite A
      (g.correct A).trans (h (g.toRelInterpretation.MapRel A)) }

end Basic

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (congrTarget)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

end Basic

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- **Transitivity of relativized parsimonious reductions.** The intermediate
definable structure is ordered by the lexicographic order on tagged tuples,
restricted to the domain. -/
noncomputable def RelOrderedParsimoniousReduction.trans (g : C ≤ʳᵖ[≤] D) (f : D ≤ʳᵖ[≤] E) :
    C ≤ʳᵖ[≤] E :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toRelInterpretation := f.toRelInterpretation.compRel g.toRelInterpretation.ordExtendRel
    dom_nonempty := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      obtain ⟨y⟩ := f.mapRel_nonempty (g.toRelInterpretation.MapRel A)
      obtain ⟨⟨t, w⟩, hw⟩ := (e2.comp e3).symm y
      exact ⟨t, w, hw⟩
    correct := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toRelInterpretation.MapRel A)
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      exact (h1.trans h2).trans (E.iso_invariant (e2.comp e3)).symm }

end Trans

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (trans)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

end Trans

end Lax794877Proofs.DescriptiveComplexity


