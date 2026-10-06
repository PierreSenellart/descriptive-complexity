/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Vocabulary
import Lax280166Proofs.DescriptiveComplexity.Numbers.BinRel
import Lax280166Proofs.DescriptiveComplexity.Interpretation
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Knapsack (BWBit BWItem BWLe BWPosn BWTarget BWTgt BWWeight HasSubsetSum)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Knapsack (binWeights bwBit bwItem bwLe bwPosn bwTgt)
end FirstOrder.Language

/-!
# Binary-weighted instances, and Karp's Knapsack

This file opens the **binary encoding** of
`DescriptiveComplexity.Numbers.BinRel`, the one the last four problems of
Karp's list need: numbers that must be *exponential* in the size of the
instance, hence written in binary. Under the unary encoding of
`DescriptiveComplexity.Numbers.Unary` these problems are solvable in polynomial
time by dynamic programming, so they are simply not NP-hard there – the
representation is not a detail of the encoding but part of the statement.

## The vocabulary

`FirstOrder.Language.binWeights` carries

* `item` and `posn`, the items and the bit positions;
* `bit i p`, “the weight of the item `i` has bit 1 at the position `p`”;
* `tgt p`, the bits of the target;
* `le`, a linear order – on the positions it fixes the place values, and on
  the items it is what the `Σ₁` definition walks along when it verifies the
  arithmetic.

Being a linear order is not automatic for a relation symbol, so it is folded
into the yes-instances (`DescriptiveComplexity.IsLinOrd`), exactly as 3SAT folds its
width bound in.

## The decoding

`DescriptiveComplexity.bitRank` is the rank of a position – how many positions lie
strictly below it – and `DescriptiveComplexity.binNum` decodes a set of positions as
`∑ 2 ^ rank`. Both are defined for an *arbitrary* relation `Le`, with no
well-formedness assumption, which keeps them total and makes
isomorphism-invariance a plain transport statement; when `Le` is a linear
order they agree with `DescriptiveComplexity.binValue` of the numbers layer.

The sum ranges over a set rather than a `Finset`, via `finsum`, so that no
finiteness assumption is needed to *state* the value; on an infinite universe
it is `0`, which no yes-instance ever looks at since finiteness is part of the
problem.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax799700.Knapsack.binWeights.Structure A]

end Shorthands

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.Knapsack.binWeights.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B]

private theorem hasSubsetSum_of_iso (e : A ≃[Lax799700.Knapsack.binWeights] B)
    (h : Lax799700.Knapsack.HasSubsetSum A) : Lax799700.Knapsack.HasSubsetSum B := by
  obtain ⟨hfin, hlin, S, hSi, hsum⟩ := h
  have hle : ∀ a a' : A, Lax799700.Knapsack.BWLe a a' ↔ Lax799700.Knapsack.BWLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.Knapsack.bwLe a a'
  have hposn : ∀ a : A, Lax799700.Knapsack.BWPosn a ↔ Lax799700.Knapsack.BWPosn (e a) := fun a => relMap_equiv₁ e Lax799700.Knapsack.bwPosn a
  have hitem : ∀ a : A, Lax799700.Knapsack.BWItem a ↔ Lax799700.Knapsack.BWItem (e a) := fun a => relMap_equiv₁ e Lax799700.Knapsack.bwItem a
  have htgt : ∀ a : A, Lax799700.Knapsack.BWTgt a ↔ Lax799700.Knapsack.BWTgt (e a) := fun a => relMap_equiv₁ e Lax799700.Knapsack.bwTgt a
  have hbit : ∀ a a' : A, Lax799700.Knapsack.BWBit a a' ↔ Lax799700.Knapsack.BWBit (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.Knapsack.bwBit a a'
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => S (e.toEquiv.symm b), fun b hb => ?_, ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hitem _).mp (hSi _ hb)
  · have hw : ∀ a : A, Lax799700.Knapsack.BWWeight a = Lax799700.Knapsack.BWWeight (e a) := fun a =>
      binNum_equiv e.toEquiv hle hposn (hbit a)
    have htarget : Lax799700.Knapsack.BWTarget A = Lax799700.Knapsack.BWTarget B := binNum_equiv e.toEquiv hle hposn htgt
    rw [← htarget, ← hsum]
    refine (finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a).symm
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha

/-- Being a yes-instance of Knapsack is isomorphism-invariant. -/
theorem hasSubsetSum_iso (e : A ≃[Lax799700.Knapsack.binWeights] B) :
    Lax799700.Knapsack.HasSubsetSum A ↔ Lax799700.Knapsack.HasSubsetSum B :=
  ⟨hasSubsetSum_of_iso e, hasSubsetSum_of_iso e.symm⟩

end Iso

/-- KNAPSACK, as a problem on binary-weighted instances: is there a set of
items whose weights sum exactly to the target? The weights are written in
*binary*, which is what makes the problem NP-hard rather than
polynomial-time. -/
def Knapsack : Lax904597.Problems.DecisionProblem Lax799700.Knapsack.binWeights where
  Holds := fun A inst => @Lax799700.Knapsack.HasSubsetSum A inst
  iso_invariant := fun e => hasSubsetSum_iso e

end Lax280166Proofs.DescriptiveComplexity


