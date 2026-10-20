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

namespace Lax799700.ZeroOneIP
end Lax799700.ZeroOneIP

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
export Lax799700.ZeroOneIP (HasZeroOneSolution IPCoef IPCoefVal IPCol IPLe IPPosn IPRhs IPRhsVal IPRow)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.ZeroOneIP (ipCoef ipCol ipLe ipPosn ipRhs ipRow zeroOneIP)
end FirstOrder.Language

/-!
# 0-1 integer programming: definition

0-1 INTEGER PROGRAMMING ([Karp 1972][karp1972reducibility]): given a matrix
`C` and a vector `d`, is there a `0-1` vector `x` with `C x = d`? It is the
multi-row form of Knapsack, and like it is written in **binary**
(`DescriptiveComplexity.Numbers.BinRel`), since under the unary encoding the
problem is solvable in polynomial time by dynamic programming and is therefore
not NP-hard at all.

## The vocabulary

`FirstOrder.Language.zeroOneIP` carries

* `col j`, `row r` and `posn p`, the columns (the `0-1` variables), the rows
  (the equations) and the bit positions;
* `coef r j p`, “the entry of row `r` in column `j` has bit 1 at position
  `p`”, the only ternary symbol of the catalog;
* `rhs r p`, the bits of the right-hand side of row `r`;
* `le`, a linear order fixing the place values, folded into the yes-instances
  (`DescriptiveComplexity.IsLinOrd`) as everywhere in the binary encoding.

Entries are **natural numbers**: Karp states the problem over the integers,
and the restriction formalized here is the one his reduction produces – a
special case, so its NP-hardness gives his problem's a fortiori, while
membership in NP for signed entries would need the two sides of each equation
weighed separately and is not claimed.
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

variable {A : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A]

end Shorthands

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A] [Lax799700.ZeroOneIP.zeroOneIP.Structure B]

private theorem hasZeroOneSolution_of_iso (e : A ≃[Lax799700.ZeroOneIP.zeroOneIP] B)
    (h : Lax799700.ZeroOneIP.HasZeroOneSolution A) : Lax799700.ZeroOneIP.HasZeroOneSolution B := by
  obtain ⟨hfin, hlin, x, hxc, hsum⟩ := h
  have hle : ∀ a a' : A, Lax799700.ZeroOneIP.IPLe a a' ↔ Lax799700.ZeroOneIP.IPLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.ZeroOneIP.ipLe a a'
  have hposn : ∀ a : A, Lax799700.ZeroOneIP.IPPosn a ↔ Lax799700.ZeroOneIP.IPPosn (e a) := fun a => relMap_equiv₁ e Lax799700.ZeroOneIP.ipPosn a
  have hcol : ∀ a : A, Lax799700.ZeroOneIP.IPCol a ↔ Lax799700.ZeroOneIP.IPCol (e a) := fun a => relMap_equiv₁ e Lax799700.ZeroOneIP.ipCol a
  have hrow : ∀ a : A, Lax799700.ZeroOneIP.IPRow a ↔ Lax799700.ZeroOneIP.IPRow (e a) := fun a => relMap_equiv₁ e Lax799700.ZeroOneIP.ipRow a
  have hcoef : ∀ a b c : A, Lax799700.ZeroOneIP.IPCoef a b c ↔ Lax799700.ZeroOneIP.IPCoef (e a) (e b) (e c) := fun a b c =>
    relMap_equiv₃ e Lax799700.ZeroOneIP.ipCoef a b c
  have hrhs : ∀ a b : A, Lax799700.ZeroOneIP.IPRhs a b ↔ Lax799700.ZeroOneIP.IPRhs (e a) (e b) := fun a b => relMap_equiv₂ e Lax799700.ZeroOneIP.ipRhs a b
  have hcv : ∀ r j : A, Lax799700.ZeroOneIP.IPCoefVal r j = Lax799700.ZeroOneIP.IPCoefVal (e r) (e j) := fun r j =>
    binNum_equiv e.toEquiv hle hposn (hcoef r j)
  have hrv : ∀ r : A, Lax799700.ZeroOneIP.IPRhsVal r = Lax799700.ZeroOneIP.IPRhsVal (e r) := fun r =>
    binNum_equiv e.toEquiv hle hposn (hrhs r)
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => x (e.toEquiv.symm b), fun b hb => ?_, fun r hr => ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hcol _).mp (hxc _ hb)
  · have hsymm : ∀ b : B, e (e.toEquiv.symm b) = b := fun b => e.toEquiv.apply_symm_apply b
    have hr' : Lax799700.ZeroOneIP.IPRow (e.toEquiv.symm r) := by
      rw [hrow, hsymm]
      exact hr
    have hbij : Set.BijOn e.toEquiv {j : A | x j} {b : B | x (e.toEquiv.symm b)} := by
      refine ⟨fun j hj => ?_, e.toEquiv.injective.injOn,
        fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
      simpa using hj
    have hstep : ∀ j : A, Lax799700.ZeroOneIP.IPCoefVal (e.toEquiv.symm r) j = Lax799700.ZeroOneIP.IPCoefVal r (e j) := by
      intro j
      rw [hcv (e.toEquiv.symm r) j, hsymm]
    have hrhs' : Lax799700.ZeroOneIP.IPRhsVal (e.toEquiv.symm r) = Lax799700.ZeroOneIP.IPRhsVal r := by
      rw [hrv (e.toEquiv.symm r), hsymm]
    rw [← finsum_mem_eq_of_bijOn e.toEquiv hbij fun j _ => hstep j, hsum _ hr', hrhs']

/-- Being a yes-instance of 0-1 integer programming is
isomorphism-invariant. -/
theorem hasZeroOneSolution_iso (e : A ≃[Lax799700.ZeroOneIP.zeroOneIP] B) :
    Lax799700.ZeroOneIP.HasZeroOneSolution A ↔ Lax799700.ZeroOneIP.HasZeroOneSolution B :=
  ⟨hasZeroOneSolution_of_iso e, hasZeroOneSolution_of_iso e.symm⟩

end Iso

/-- 0-1 INTEGER PROGRAMMING, as a problem on 0-1 integer programs: is there a
set of columns whose entries sum, row by row, exactly to the right-hand
sides? The entries are written in *binary*, which is what makes the problem
NP-hard rather than polynomial-time. -/
def ZeroOneIP : Lax904597.Problems.DecisionProblem Lax799700.ZeroOneIP.zeroOneIP where
  Holds := fun A inst => @Lax799700.ZeroOneIP.HasZeroOneSolution A inst
  iso_invariant := fun e => hasZeroOneSolution_iso e

end Lax280166Proofs.DescriptiveComplexity


