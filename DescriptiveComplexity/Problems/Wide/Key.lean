/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Bridge
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.Numbers.BinRel

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

variable (K A : Type) [LinearOrder K] [Finite K] [LinearOrder A] (dd : ℕ)

/-- **The index of the file a clocked program lays out**: a block of the
argument inventory – or none, for the registers that belong to no block – and a
tuple of the instance. -/
abbrev BlkIx : Type := Option K × (Fin dd → A)

/-- **The order of the blocks**: the blockless registers first, then the blocks
in their own order. Which order this is matters: it is the one under which the
tag of a block (`DescriptiveComplexity.blkTag`) is monotone, so that the marks a
program keeps on its file count in the same order as the addresses they stand
for (`DescriptiveComplexity.ixAddr`). It is a relation and not an instance,
because `Option` carries an order of its own and two paths to one notation are
worse than none. -/
def blkTagLe : Option K → Option K → Prop
  | none, _ => True
  | some _, none => False
  | some k, some k' => k ≤ k'

omit [Finite K] [LinearOrder A] in
/-- **The block order is linear.** -/
theorem isLinOrd_blkTagLe : IsLinOrd (blkTagLe K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (_ | a)
    · exact trivial
    · exact le_refl a
  · rintro (_ | a) (_ | b) (_ | c) h₁ h₂ <;> first
      | exact trivial
      | exact h₁.elim
      | exact h₂.elim
      | exact le_trans h₁ h₂
  · rintro (_ | a) (_ | b) h₁ h₂ <;> first
      | rfl
      | exact h₁.elim
      | exact h₂.elim
      | exact congrArg some (le_antisymm h₁ h₂)
  · rintro (_ | a) (_ | b) <;> first
      | exact Or.inl trivial
      | exact Or.inr trivial
      | exact (le_total a b).imp id id

/-- The order the registers are laid out in: block-major, then the tuple's own
lexicographic order. -/
noncomputable def blkLe : BlkIx K A dd → BlkIx K A dd → Prop :=
  lexRel (blkTagLe K) tupLeLex

omit [Finite K] in
/-- **The layout order is linear**, by the same lemma the universe's own order
is proved from. -/
theorem isLinOrd_blkLe : IsLinOrd (blkLe K A dd) :=
  isLinOrd_lexRel (isLinOrd_blkTagLe K) isLinOrd_tupLeLex

omit [LinearOrder K] [LinearOrder A] in
/-- **How many registers the file has**: one per block, one more for the
blockless ones, times the tuples. -/
theorem card_blkIx : Nat.card (BlkIx K A dd) = (Nat.card K + 1) * Nat.card (Fin dd → A) := by
  let := Fintype.ofFinite K
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Option K), Nat.card_eq_fintype_card (α := K),
    Fintype.card_option]

end Blk

end Wide

end DescriptiveComplexity
