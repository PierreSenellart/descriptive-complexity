/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.SecondOrderLift
import Lax175070.CountDefinability
import Lax175070.SelectedSat
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax175070Proofs.DescriptiveComplexity.SOBlock
end Lax175070Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize soLang)
end Lax175070Proofs.DescriptiveComplexity

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

namespace Lax175070Proofs.DescriptiveComplexity

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

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (cons)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- An assignment of the merged block `SOBlock.cons B M`, assembled from an
assignment of `B` and one of `M`. -/
def consAssign {A : Type} {B M : Lax904597.SecondOrder.SOBlock} (ρ : B.Assignment A) (μ : M.Assignment A) :
    (SOBlock.cons B M).Assignment A
  | Sum.inl i => ρ i
  | Sum.inr i => μ i

/-! ### Re-associating an expansion -/

/-- Re-association of language expansions: expanding `L` by a block `B` and
then by a block `M` is expanding `L` by the merged block `SOBlock.cons B M`. -/
def mergeStep (L : Language.{0, 0}) (B M : Lax904597.SecondOrder.SOBlock) :
    (L.sum B.lang).sum M.lang →ᴸ L.sum (SOBlock.cons B M).lang where
  onFunction := fun {_} f =>
    match f with
    | Sum.inl (Sum.inl f) => Sum.inl f
    | Sum.inl (Sum.inr f) => isEmptyElim f
    | Sum.inr f => isEmptyElim f
  onRelation := fun {_} r =>
    match r with
    | Sum.inl (Sum.inl r) => Sum.inl r
    | Sum.inl (Sum.inr r) => Sum.inr ⟨Sum.inl r.1, r.2⟩
    | Sum.inr r => Sum.inr ⟨Sum.inr r.1, r.2⟩

/-- The re-association is an expansion: it does not change how any symbol is
interpreted, when the two block assignments on one side are assembled into a
single merged assignment on the other. -/
theorem mergeStep_isExpansionOn (L : Language.{0, 0}) {A : Type} (instL : L.Structure A)
    (B M : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A) (μ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (mergeStep L B M) A
      (@sumStructure (L.sum B.lang) M.lang A
        (@sumStructure L B.lang A instL (B.structure ρ)) (M.structure μ))
      (@sumStructure L (SOBlock.cons B M).lang A instL
        ((SOBlock.cons B M).structure (consAssign ρ μ))) := by
  let := instL
  let := B.structure ρ
  let := M.structure μ
  let := (SOBlock.cons B M).structure (consAssign ρ μ)
  refine ⟨?_, ?_⟩
  · intro n f x
    rcases f with f | f
    · rcases f with f | f
      · rfl
      · exact isEmptyElim f
    · exact isEmptyElim f
  · intro n r x
    rcases r with r | r
    · rcases r with r | r
      · rfl
      · rfl
    · rfl

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

/-! ### The converse transport

For *stating* that a problem is second-order definable one needs to go the
other way: a kernel written over the single merged block has to be turned into
a kernel over the iterated expansion. The morphisms below invert those above,
and give the same theorem read from right to left
(`DescriptiveComplexity.sorealize_unmerge`). -/

end Lax175070Proofs.DescriptiveComplexity


