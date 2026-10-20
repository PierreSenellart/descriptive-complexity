/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.SecondOrderLift
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize soLang)
end Lax480241Proofs.DescriptiveComplexity

/-!
# Merging a quantifier prefix into a single second-order block

A second-order sentence with `k` alternating blocks quantifies over a list of
blocks `Bs`, and its kernel lives over the iterated expansion
`DescriptiveComplexity.soLang L Bs`. Constructions that must *read* the kernel – above all
the Tseitin translation of `DescriptiveComplexity.Problems.Sat.Tseitin`, which turns it
into a CNF instance – are stated for a single block, over `L.sum B.lang`.

This file bridges the two: `DescriptiveComplexity.mergeBlocks` collects a list of blocks
into one block whose relation variables are the disjoint union of theirs, and
`DescriptiveComplexity.mergeHom` transports the kernel accordingly. The alternation is
*not* lost – it moves from the block list to
`DescriptiveComplexity.altAssign`, which quantifies the components of a merged assignment
alternately – so `DescriptiveComplexity.sorealize_iff_altAssign` rewrites alternating
second-order satisfaction as an alternating quantification over the pieces of
a single assignment, with a single-block kernel.

The only mathematical content is the re-association
`(L ⊕ B) ⊕ M ≅ L ⊕ (B ⊕ M)` of `DescriptiveComplexity.mergeStep`, applied once per block.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Merging blocks -/

/-- Prepending a block to another: the relation variables are the disjoint
union of both families. Reducible, so that `(SOBlock.cons B M).ι` unfolds to a
sum type when elaborating index literals. -/
@[reducible]
def SOBlock.cons (B M : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := B.ι ⊕ M.ι
  arity := Sum.elim B.arity M.arity

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (cons)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The single block merging a whole list of blocks: one relation variable per
relation variable of one of the blocks. -/
def mergeBlocks : List Lax904597.SecondOrder.SOBlock → Lax904597.SecondOrder.SOBlock
  | [] => SOBlock.trivial
  | B :: Bs => SOBlock.cons B (mergeBlocks Bs)

/-- An assignment of the merged block `SOBlock.cons B M`, assembled from an
assignment of `B` and one of `M`. -/
def consAssign {A : Type} {B M : Lax904597.SecondOrder.SOBlock} (ρ : B.Assignment A) (μ : M.Assignment A) :
    (SOBlock.cons B M).Assignment A
  | Sum.inl i => ρ i
  | Sum.inr i => μ i

/-- The unique assignment of the merged block of the empty list. -/
def nilAssign (A : Type) : (mergeBlocks []).Assignment A :=
  fun i => Empty.elim (i : Empty)

/-! ### Re-associating an expansion -/

/-! ### Transporting the kernel -/

/-! ### Alternating quantification over a merged assignment -/

/-! ### The merging theorem -/

/-! ### Enlarging the innermost block

The Tseitin translation of a kernel introduces auxiliary *gate* variables,
which have to be quantified together with the relation variables of the
innermost block. The constructions below enlarge the last block of a prefix by
a further block `Gt`, and show that quantifying the enlarged prefix is
quantifying the original one with an extra quantifier – of the *innermost*
polarity – over `Gt` inside. Lists are given as a head and a tail, so that
“nonempty” is built into the syntax and the recursion has no overlapping
patterns. -/

/-- Splitting and reassembling an assignment of a merged pair of blocks. -/
theorem consAssign_split {A : Type} {B C : Lax904597.SecondOrder.SOBlock}
    (ρ : (SOBlock.cons B C).Assignment A) :
    consAssign (fun i => ρ (Sum.inl i)) (fun j => ρ (Sum.inr j)) = ρ := by
  funext i
  rcases i with i | i <;> rfl

/-! ### The converse transport

For *stating* that a problem is second-order definable one needs to go the
other way: a kernel written over the single merged block has to be turned into
a kernel over the iterated expansion. The morphisms below invert those above,
and give the same theorem read from right to left
(`DescriptiveComplexity.sorealize_unmerge`). -/

end Lax480241Proofs.DescriptiveComplexity


