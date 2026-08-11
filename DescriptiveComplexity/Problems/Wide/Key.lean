/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Bridge
import DescriptiveComplexity.OrderedComposition

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

namespace DescriptiveComplexity

/- The declarations of this file live in the `Wide` namespace, as those of
`DescriptiveComplexity.Problems.Wide.Expansion` do: `Problems/Machine/Tape.lean`
already carries a copy of the linearity fact specialized to its own tag type, and
unifying the two is a change to a file the SAT machine depends on. -/
namespace Wide

section Key

variable {Tag : Type} [LinearOrder Tag] {d : ℕ} {A : Type} [LinearOrder A]

/-- **The lexicographic order on tagged tuples is a linear order**, as a plain
relation: transported from `DescriptiveComplexity.tagTupleOrder`, which is the
same comparison read as a `LinearOrder`. -/
theorem isLinOrd_tagTupleLe : IsLinOrd (tagTupleLe (Tag := Tag) (d := d) (A := A)) :=
  isLinOrd_of_key
    (LeK := (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le)
    ⟨fun a => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_refl a,
      fun a b c => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_trans a b c,
      fun a b => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_antisymm a b,
      fun a b => (tagTupleOrder : LinearOrder (Tag × (Fin d → A))).le_total a b⟩
    id Function.injective_id fun p q => tagTupleLe_iff_le p q

/-- **The lexicographic order on tuples is a linear order**: the previous
statement with a single tag. -/
theorem isLinOrd_tupLeLex : IsLinOrd (tupLeLex (A := A) (d := d)) :=
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

/-- The block-major order on a tagged tuple universe is a linear order – either
by `DescriptiveComplexity.isLinOrd_lexRel` from its two factors, or by transport
along the previous theorem. -/
theorem isLinOrd_lexRel_tagTuple :
    IsLinOrd (lexRel (· ≤ · : Tag → Tag → Prop) (tupLeLex (A := A) (d := d))) :=
  isLinOrd_lexRel isLinOrd_le isLinOrd_tupLeLex

end Key

end Wide

end DescriptiveComplexity
