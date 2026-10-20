/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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

namespace Lax280166Proofs.DescriptiveComplexity.DominatesOn
end Lax280166Proofs.DescriptiveComplexity.DominatesOn

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.DominatingSet
end Lax799700.DominatingSet

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.DominatingSet (DominatesOn HasSmallDominatingSet)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Dominating Set: the problem

DOMINATING SET: is there a set of vertices, at most as large as the marked
set, such that every vertex is in it or adjacent to it? The vocabulary is
`FirstOrder.Language.markedGraph`, the one Vertex Cover and Clique already use: a
graph together with a marked set whose cardinality is the threshold
(`DescriptiveComplexity.Numbers.Unary`).

Domination differs from the covering properties of the clique family in one
respect that matters for reductions: its condition ranges over *every* element
of the universe, so a reduction into it cannot leave junk tuples behind – each
of them has to be dominated too. The reduction of
`DescriptiveComplexity.Problems.DominatingSet.Reduction` handles this by making the
junk adjacent to the vertices that a solution always contains.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A : Type}

variable {B : Type}

/-- `DominatesOn` transports along an equivalence commuting with the two
predicates. -/
theorem DominatesOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.DominatingSet.DominatesOn AdjB KB) : Lax799700.DominatingSet.DominatesOn AdjA KA := by
  obtain ⟨D, hdom, hcard⟩ := h
  refine ⟨fun a => D (u.symm a), fun v => ?_, ?_⟩
  · rcases hdom (u.symm v) with h' | ⟨w, hw, hadjw⟩
    · exact Or.inl h'
    · refine Or.inr ⟨u w, by simpa using hw, ?_⟩
      have := (hadj w (u.symm v)).mp hadjw
      simpa using this
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u D]
    exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.DominatingSet.DominatesOn

export Lax280166Proofs.DescriptiveComplexity.DominatesOn (of_equiv)

end Lax799700.DominatingSet.DominatesOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

private theorem dom_symm_hUn {PB : B → Prop} {PA : A → Prop} (u : B ≃ A)
    (hP : ∀ b, PB b ↔ PA (u b)) (a : A) : PA a ↔ PB (u.symm a) := by
  rw [hP]
  simp

private theorem dom_symm_hBin {MB : B → B → Prop} {MA : A → A → Prop} (u : B ≃ A)
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (a a' : A) :
    MA a a' ↔ MB (u.symm a) (u.symm a') := by
  rw [hM]
  simp

/-- `DominatesOn` transports along an equivalence, iff version. -/
theorem DominatesOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.DominatingSet.DominatesOn AdjB KB ↔ Lax799700.DominatingSet.DominatesOn AdjA KA :=
  ⟨DominatesOn.of_equiv u hadj hK,
    DominatesOn.of_equiv u.symm (dom_symm_hBin u hadj) (dom_symm_hUn u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.DominatingSet.DominatesOn

export Lax280166Proofs.DescriptiveComplexity.DominatesOn (equiv_iff)

end Lax799700.DominatingSet.DominatesOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B]

/-- The domination threshold property is isomorphism-invariant. -/
theorem hasSmallDominatingSet_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.DominatingSet.HasSmallDominatingSet A ↔ Lax799700.DominatingSet.HasSmallDominatingSet B :=
  and_congr e.toEquiv.finite_iff
    (DominatesOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a b)
      fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

end Iso

/-- DOMINATING SET, as a problem on marked graphs: is there a set of vertices
at most as large as the marked set that dominates every vertex? -/
def DominatingSet : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.DominatingSet.HasSmallDominatingSet A inst
  iso_invariant := fun e => hasSmallDominatingSet_iso e

end Lax280166Proofs.DescriptiveComplexity


