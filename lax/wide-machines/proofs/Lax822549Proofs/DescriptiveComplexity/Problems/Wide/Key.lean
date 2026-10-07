/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Blocks
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Fold
import Lax822549Proofs.DescriptiveComplexity.OrderedComposition
import Lax822549Proofs.DescriptiveComplexity.Numbers.BinRel
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The order key a reduction writes is the block-major one

The address layer of a wide machine reads an address over a universe `T × V`
ordered by `DescriptiveComplexity.lexRel` – block index first, coordinate second
(`DescriptiveComplexity.Problems.Wide.Blocks`). A reduction's universe is a
*tagged tuple* `Tag × (Fin d → A)`, and the only order on it that a first-order
interpretation can define is the one the library already has,
`DescriptiveComplexity.tagTupleLe`, whose defining formula is
`DescriptiveComplexity.lexLeF`.

They are the same order:

> `DescriptiveComplexity.Wide.tagTupleLe_iff_lexRel` – the definable order on a tagged
> tuple universe **is** `lexRel` of the tag order and the lexicographic order on
> coordinates.

So a reduction writes `DescriptiveComplexity.lexLeF` for `wmLe`, takes its tag
type to be `Fin n` – one index per variable of its kernel, plus the scratch – and
the whole of `Blocks`, `Bridge` and the fold applies to the instance it has drawn.
This is the last thing that has to be checked before a program is written: it is
what makes the layout *definable* rather than merely convenient.

The two linearity facts come with it, since every lemma of the address layer asks
for them: `DescriptiveComplexity.Wide.isLinOrd_tagTupleLe`, transported from the
`LinearOrder` the library builds by `DescriptiveComplexity.tagTupleOrder`, and
`DescriptiveComplexity.Wide.isLinOrd_tupLeLex`, which is the same statement with no
tag at all.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Wide

section Key

variable {Tag : Type} [LinearOrder Tag] {d : ℕ} {A : Type} [LinearOrder A]

/-- **The lexicographic order on tagged tuples is a linear order**, as a plain
relation: transported from `DescriptiveComplexity.tagTupleOrder`, which is the
same comparison read as a `LinearOrder`. -/
theorem isLinOrd_tagTupleLe : Lax904597.Machines.IsLinOrd (tagTupleLe (Tag := Tag) (d := d) (A := A)) :=
  isLinOrd_of_key
    (LeK := (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le)
    ⟨fun a => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_refl a,
      fun a b c => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_trans a b c,
      fun a b => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_antisymm a b,
      fun a b => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_total a b⟩
    id Function.injective_id fun p q => tagTupleLe_iff_le p q

/-- **The lexicographic order on tuples is a linear order**: the previous
statement with a single tag. -/
theorem isLinOrd_tupLeLex : Lax904597.Machines.IsLinOrd (tupLeLex (A := A) (d := d)) :=
  isLinOrd_of_key (isLinOrd_tagTupleLe (Tag := Unit)) (fun x => ((), x))
    (fun _ _ h => congrArg Prod.snd h)
    (fun x y => by
      rw [tagTupleLe]
      simp)

/-- **The definable order on a tagged tuple universe is the block-major order.**
A reduction's `wmLe` is `DescriptiveComplexity.lexLeF`, whose meaning is
`DescriptiveComplexity.tagTupleLe`; the address layer of a wide machine reads
`DescriptiveComplexity.lexRel`; and this says the two agree, so an address over
the universe the reduction draws decomposes into one block per tag. -/
theorem tagTupleLe_iff_lexRel (p q : Tag × (Fin d → A)) :
    tagTupleLe p q ↔ lexRel (· ≤ · : Tag → Tag → Prop) (tupLeLex (A := A) (d := d)) p q := by
  rw [tagTupleLe, lexRel]
  exact or_congr lt_iff_le_and_ne Iff.rfl

end Key

/-! ### The index a clocked program lays its file out by

A program with no clock gives every element of the universe a register; a
clocked one cannot, since the only stretches it can walk are a fixed number of
tuple roll-overs long and the universe is `|Tag|` of those. What it can afford
is one register per **block and tuple**, which is also all that a register's
contents ever depend on. Its order is the lexicographic product of the block
order and the tuples' (`DescriptiveComplexity.lexRel`), and the block order is
written down rather than borrowed: it has to be the one under which a block's
tag is monotone, so that a mark on the file counts in the same order as the
address it stands for (`DescriptiveComplexity.ixAddr`). -/

section Blk

end Blk

end Wide

end Lax822549Proofs.DescriptiveComplexity


