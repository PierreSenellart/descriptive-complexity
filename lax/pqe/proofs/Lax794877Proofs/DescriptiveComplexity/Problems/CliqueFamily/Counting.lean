/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax794877Proofs.DescriptiveComplexity.Block
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax794877Proofs.DescriptiveComplexity.SecondOrder
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Lax794877Proofs.DescriptiveComplexity.Counting.SharpP
import Lax794877Proofs.DescriptiveComplexity.OrderedComposition
import Lax794877Proofs.DescriptiveComplexity.SecondOrderLift
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
import Lax794877Proofs.DescriptiveComplexity.Counting.Class
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

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax794877Proofs.DescriptiveComplexity.CliqueOfSize
end Lax794877Proofs.DescriptiveComplexity.CliqueOfSize

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CliqueOfSize)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# #Clique: counting the cliques of the threshold size

The counting version of `DescriptiveComplexity.Clique`: the number of cliques having
*exactly* as many vertices as the marked set (`DescriptiveComplexity.CliqueOfSize`).
Its support is Clique, a clique at least as large as the threshold containing
one of exactly that size.

Membership in `#P` (`DescriptiveComplexity.sharpClique_mem_sharpP`) is the first in the
catalog whose kernel reads the order of the instance. The `Σ₁` definition of
Clique certifies the threshold by an injection of the marked set into the
clique, and a clique has many; even for the exact size, a bijection is one
among `k!`. The counting kernel asks for the *monotone* one, which exists and
is unique on a finite linear order. That argument is generic
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), and what this file supplies is
the order-free part: a set is a clique (`DescriptiveComplexity.cliqueSelKernel`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

variable {A} {B : Type} [Lax799700.CliqueFamily.markedGraph.Structure B]

/-- Cliques of the threshold size transport along an isomorphism. -/
theorem CliqueOfSize.map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) {S : A → Prop}
    (h : Lax280166.CountingCliques.CliqueOfSize A S) : Lax280166.CountingCliques.CliqueOfSize B fun b => S (e.toEquiv.symm b) := by
  obtain ⟨hfin, hcl, hcard⟩ := h
  refine ⟨Finite.of_equiv A e.toEquiv, fun x y hx hy hxy => ?_, ?_⟩
  · have h' := (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj (e.toEquiv.symm x) (e.toEquiv.symm y)).mp
      (hcl _ _ hx hy fun h => hxy (e.toEquiv.symm.injective h))
    have hx' : e (e.toEquiv.symm x) = x := e.toEquiv.apply_symm_apply x
    have hy' : e (e.toEquiv.symm y) = y := e.toEquiv.apply_symm_apply y
    rw [hx', hy'] at h'
    exact h'
  · exact ((ncard_setOf_symm e.toEquiv S).symm.trans hcard).trans
      (ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

end Solutions

end Lax794877Proofs.DescriptiveComplexity

namespace Lax280166.CountingCliques.CliqueOfSize

export Lax794877Proofs.DescriptiveComplexity.CliqueOfSize (map)

end Lax280166.CountingCliques.CliqueOfSize

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

variable {A} {B : Type} [Lax799700.CliqueFamily.markedGraph.Structure B]

end Solutions

/-! ### The order-free kernel -/

/-! ### The counting problem -/

/-- **#Clique**: the number of cliques with exactly as many vertices as the
marked set. -/
noncomputable def SharpClique : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax280166.CountingCliques.CliqueOfSize A inst S}
  iso_invariant := fun {A B} _ _ e => by
    refine Nat.card_congr
      { toFun := fun S => ⟨fun b => S.1 (e.toEquiv.symm b), S.2.map e⟩
        invFun := fun T => ⟨fun a => T.1 (e.toEquiv a), ?_⟩
        left_inv := fun S => Subtype.ext (funext fun a => by simp)
        right_inv := fun T => Subtype.ext (funext fun b => by simp) }
    have h := T.2.map e.symm
    exact h

theorem sharpClique_apply (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpClique A = Nat.card {S : A → Prop // Lax280166.CountingCliques.CliqueOfSize A S} :=
  rfl

end Lax794877Proofs.DescriptiveComplexity


