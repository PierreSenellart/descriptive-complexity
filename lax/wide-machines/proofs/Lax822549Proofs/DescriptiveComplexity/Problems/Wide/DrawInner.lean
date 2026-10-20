/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Blocks
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Fold
import Lax822549Proofs.DescriptiveComplexity.OrderWalk
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMSetLe)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The fold on a final segment of the blocks

`DescriptiveComplexity.Problems.Wide.Bridge` joins the fold to the address
increment when the block index type is the whole of `Fin n`. The inner loop of
the EXPSPACE program is not like that: its register enumerates the valuations
of the step formula's quantifier prefix, which live in the **last** `q` blocks
of the address – the `Kin` half of the argument tags – while every other block
of the register stays empty. So the join is restated here for an arbitrary
family of block indices `ι : Fin q → T`, assumed to be an *order embedding onto
a final segment* of the tag order:

* the embedding hypotheses are `DescriptiveComplexity.Draw.IxSeg`;
* `DescriptiveComplexity.Draw.exists_carry_ix` – an increment of the address
  whose image blocks are not all full has its carry **inside** the image (every
  tag after an image tag is an image tag, so the last non-full block cannot
  escape), and decomposes there;
* `DescriptiveComplexity.Draw.foldFrom_carry_of_ix` /
  `foldFrom_above_of_ix` / `foldFrom_below_of_ix` – the three fold rules, at
  the family `DescriptiveComplexity.Draw.ixBlk` of image blocks;
* `DescriptiveComplexity.Draw.foldFrom_bot_of_ix` /
  `foldFrom_top_of_ix` – the two ends: empty image blocks start the sweep at
  the matrix, full ones finish it at the whole prefix.

Everything is about the product order `DescriptiveComplexity.lexRel` on
`T × V`; joining it to the machine's own order is the instance's `le` field, as
everywhere in the layer.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

section Inner

variable {T V : Type} {LeT : T → T → Prop} {LeV : V → V → Prop} {q : ℕ}

/-- **A final segment of the blocks**: an order embedding of `Fin q` into the
tags whose image is upward closed – every tag strictly above an image tag is an
image tag. The `Kin` half of the argument tags is one. -/
structure IxSeg (LeT : T → T → Prop) (ι : Fin q → T) : Prop where
  /-- The embedding is strictly monotone, in both directions. -/
  mono : ∀ j j' : Fin q, WMLt LeT (ι j) (ι j') ↔ j < j'
  /-- The image is a final segment of the tag order. -/
  final : ∀ (j : Fin q) (t : T), WMLt LeT (ι j) t → ∃ j' : Fin q, t = ι j'

/-- **The image blocks of an address**, as a valuation of the fold. -/
def ixBlk (ι : Fin q → T) (s : T × V → Prop) : Fin q → V → Prop := fun j => wmBlk s (ι j)

variable {ι : Fin q → T} {s s' : T × V → Prop}

/-! ### The fold rules at the image blocks -/

variable {pol : ℕ → Bool} {P : (Fin q → (V → Prop)) → Prop} [Finite V]

/-! ### The two ends of the enumeration -/

/-- **Full image blocks finish the sweep at the whole prefix**: every leaf has
been seen. -/
theorem foldFrom_top_of_ix (hV : Lax904597.Machines.IsLinOrd LeV)
    (hfull : ∀ (j : Fin q) (v : V), wmBlk s (ι j) v) {j : ℕ} :
    foldFrom pol P (Lax822549.WideMachines.WMSetLe LeV) j (ixBlk ι s) ↔ altQuantFrom pol P j (ixBlk ι s) :=
  foldFrom_top (j₀ := 0) (isLinOrd_wmSetLe hV)
    (fun i _ a => wmSetLe_of_full hV (hfull i) a) (Nat.zero_le j)

end Inner

/-! ### The fold along a tuple loop

The element loops of the atom subroutines enumerate tuples of *source
elements* in the control, stepping by the lexicographic successor
`DescriptiveComplexity.TupSucc` – whose components are exactly the hypotheses
of the fold's three step rules, at value type the source structure itself.
These are the control-scale twins of the rules above; the two ends need no
twin, `DescriptiveComplexity.foldFrom_bot` / `foldFrom_top` apply as they
stand at an all-minimal / all-maximal tuple. -/

section TupLoop

variable {A : Type} [LinearOrder A] {e : ℕ} {pol : ℕ → Bool} {P : (Fin e → A) → Prop}

/-- The strict form of the order relation the fold reads is the strict
order. -/
theorem wmLt_le_iff {a b : A} : WMLt (· ≤ ·) a b ↔ a < b :=
  ⟨fun h => lt_of_le_not_ge h.1 h.2, fun h => ⟨le_of_lt h, not_le_of_gt h⟩⟩

end TupLoop

end Draw

end Lax822549Proofs.DescriptiveComplexity


