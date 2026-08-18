/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Key
import DescriptiveComplexity.Problems.Wide.DrawRules

/-!
# What a wide machine cannot do: name its own elements

A wide machine's *positions* are the addresses of its universe – the sets of
elements – and the only way a program has of recording one is a **register
file**: a stretch of consecutive cells, one register per element, each holding
one bit of the address. A file that is to be *faithful*, i.e., to tell two
addresses apart the way a scan of it does
(`DescriptiveComplexity.ixAddr_ixMark`), needs one register per element, and its
registers have to be told apart by the **names** the file records at them
(`DescriptiveComplexity.Draw.Layout.NameSep`).

The theorem below is the counting fact that follows, and it is what forbids a
program from *laying* such a file. A state's payload carries one element of the
universe's base type per control flag **and** one per slot, all inside a
`dd`-tuple – that is `DescriptiveComplexity.Draw.Prog.payload_le` – so the
control's value space is `|A| ^ #flags` with `#flags < dd`, while the elements
number `|Tag| · |A| ^ dd`. **The control cannot hold a name that separates the
registers**, and a sweep laying a file has nowhere else to hold one: at the cell
it is about to write, the region is blank, and no rule can read the head's
address.

So a clocked program cannot build its own register file over its own universe,
however the file is indexed and however wide the reduction makes the dimension:
the two constraints move together. What is left to a program is a file it is
*handed* – the input channel's, whose geometry is the model's
(`DescriptiveComplexity.wmSeg`) and not the reduction's – or an evaluation that
never records an address at all.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section Counting

variable {A Q W R P K : Type} [Finite A] [Finite Q] [Finite W]
variable [Finite R] [Finite P] [Finite K] {dd : ℕ}

omit [Finite A] in
/-- **A wide machine's control has fewer values than the universe has
elements**: the payload of a state holds one element per control flag and one
per slot inside a `dd`-tuple, so the flags are strictly fewer than `dd` as soon
as there is one slot, and the elements are at least `|A| ^ dd`.

This is the counting behind the rule that a program's register file comes from
its input channel or not at all (stated in
`DescriptiveComplexity.Problems.Wide`): a program that lays a register file has
to write, at each register, a name that separates it from the others, and the
only place a name can come from is the control. -/
theorem card_ctl_lt_card_univ [Nonempty W]
    (hpl : Nat.card Q + Nat.card W ≤ dd) (hA : 2 ≤ Nat.card A) :
    Nat.card (Q → A) < Nat.card (Univ A R P K dd) := by
  have hQW : Nat.card Q < dd := by
    have : 1 ≤ Nat.card W := Nat.one_le_iff_ne_zero.mpr (by
      simpa using Nat.card_pos (α := W).ne')
    omega
  have hfun : Nat.card (Q → A) = Nat.card A ^ Nat.card Q := by
    rw [Nat.card_fun]
  have htup : Nat.card (Fin dd → A) = Nat.card A ^ dd := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin dd), Fintype.card_fin]
  have hlt : Nat.card A ^ Nat.card Q < Nat.card A ^ dd :=
    Nat.pow_lt_pow_right hA hQW
  have huniv : Nat.card (Univ A R P K dd) =
      Nat.card (Tag R P K) * Nat.card (Fin dd → A) := Nat.card_prod _ _
  have htag : 1 ≤ Nat.card (Tag R P K) := by
    have : Nonempty (Tag R P K) := ⟨Tag.sym⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := Tag R P K)).ne'
  calc Nat.card (Q → A) = Nat.card A ^ Nat.card Q := hfun
    _ < Nat.card A ^ dd := hlt
    _ = 1 * Nat.card (Fin dd → A) := by rw [htup, one_mul]
    _ ≤ Nat.card (Tag R P K) * Nat.card (Fin dd → A) :=
        Nat.mul_le_mul_right _ htag
    _ = Nat.card (Univ A R P K dd) := huniv.symm

/-- **No naming of the elements by the control**: there is no injection from the
universe into the control's value space, so no program can hold, at each of its
registers, a name that tells that register from every other. -/
theorem not_injective_ctl_name [Nonempty W]
    (hpl : Nat.card Q + Nat.card W ≤ dd) (hA : 2 ≤ Nat.card A)
    (nm : Univ A R P K dd → (Q → A)) : ¬Function.Injective nm := by
  intro hinj
  exact absurd (Nat.card_le_card_of_injective nm hinj)
    (not_le_of_gt (card_ctl_lt_card_univ (Q := Q) (W := W) (R := R) (P := P)
      (K := K) hpl hA))

end Counting

end Draw

end DescriptiveComplexity
