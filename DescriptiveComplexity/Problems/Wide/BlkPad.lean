/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.BlkFile

/-!
# A file whose registers are named by encoded points

The registers of `DescriptiveComplexity.blkFile` are indexed by a block and a
tuple, and the tuple is as wide as the universe's. That is one width too many
for a program to *lay*: a wide machine's state carries one element per control
flag and one per slot, all inside a `dd`-tuple, so it can never hold a whole
`dd`-tuple – the sweep that writes the file would need `dd` control flags and
`Fintype.card (CtlIx ⊕ SlotIx) ≤ dd` forbids it.

What a state *can* hold is an **encoded point**: `dd₀` coordinates, with
`dd₀ < dd`, which is what the space-bounded program's control holds and what a
register's `name` slots record. So the file a clocked program lays is indexed by
`(block, Fin dd₀ → A)`, and the element a register stands for is that tuple
**padded**.

This file is the order theory of that indexing: padding is injective, it
preserves the lexicographic comparison in both directions – beyond `dd₀` the two
padded tuples agree, so the first difference is inside `dd₀` – and therefore a
padded register file is laid out in the same order as a full one. Nothing here
mentions a machine.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Pad

variable {A : Type} [LinearOrder A] {d dd : ℕ} {zero : A}

omit [LinearOrder A] in
/-- **A padded tuple at an encoded coordinate is that coordinate.** -/
theorem pad_apply (hle : d ≤ dd) (w : Fin d → A) (i : Fin d) :
    Draw.pad (dd := dd) zero w ⟨(i : ℕ), lt_of_lt_of_le i.isLt hle⟩ = w i := by
  have h := Draw.pad_of_lt (c := d) (zero := zero) (w := w)
    (⟨(i : ℕ), lt_of_lt_of_le i.isLt hle⟩ : Fin dd) i.isLt
  rw [h]

omit [LinearOrder A] in
/-- **A padded tuple beyond the encoded width is clear.** -/
theorem pad_apply_ge (w : Fin d → A) (j : Fin dd) (h : ¬((j : ℕ) < d)) :
    Draw.pad (dd := dd) zero w j = zero :=
  Draw.pad_of_ge (c := d) j (Nat.le_of_not_lt h)

/-- **Padding preserves the lexicographic order**: beyond the encoded width the
two tuples agree, so the position that decides the comparison is one of the
encoded coordinates. -/
theorem tupLeLex_pad_iff (hle : d ≤ dd) (w w' : Fin d → A) :
    tupLeLex (Draw.pad (dd := dd) zero w) (Draw.pad (dd := dd) zero w') ↔
      tupLeLex w w' := by
  constructor
  · rintro (heq | ⟨j, hagree, hlt⟩)
    · refine Or.inl (funext fun i => ?_)
      have h := congrFun heq ⟨(i : ℕ), lt_of_lt_of_le i.isLt hle⟩
      rwa [pad_apply hle w i, pad_apply hle w' i] at h
    · have hjd : (j : ℕ) < d := by
        by_contra hc
        rw [pad_apply_ge w j hc, pad_apply_ge w' j hc] at hlt
        exact absurd hlt (lt_irrefl _)
      refine Or.inr ⟨⟨(j : ℕ), hjd⟩, fun i hi => ?_, ?_⟩
      · have h := hagree ⟨(i : ℕ), lt_of_lt_of_le i.isLt hle⟩ hi
        rwa [pad_apply hle w i, pad_apply hle w' i] at h
      · have h := hlt
        rwa [Draw.pad_of_lt (c := d) j hjd, Draw.pad_of_lt (c := d) j hjd] at h
  · rintro (rfl | ⟨j, hagree, hlt⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨⟨(j : ℕ), lt_of_lt_of_le j.isLt hle⟩, fun i hi => ?_, ?_⟩
      · by_cases hid : (i : ℕ) < d
        · have h := hagree ⟨(i : ℕ), hid⟩ hi
          rw [Draw.pad_of_lt (c := d) i hid, Draw.pad_of_lt (c := d) i hid]
          simpa using h
        · rw [pad_apply_ge w i hid, pad_apply_ge w' i hid]
      · rw [pad_apply hle w j, pad_apply hle w' j]
        exact hlt

omit [LinearOrder A] in
/-- **Padding is injective**, the encoded coordinates being kept. -/
theorem pad_injective (hle : d ≤ dd) :
    Function.Injective (Draw.pad (dd := dd) (c := d) zero) := by
  intro w w' h
  funext i
  have h' := congrFun h ⟨(i : ℕ), lt_of_lt_of_le i.isLt hle⟩
  rwa [pad_apply hle w i, pad_apply hle w' i] at h'

end Pad

section PadFile

variable {A R P K : Type} [LinearOrder A] [Finite A] [Finite R] [Finite P]
variable [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite K] {d dd : ℕ}
variable [Language.wide.Structure (Draw.Univ A R P K dd)]

variable (R P dd) in
/-- **The element a register of a padded file holds the bit of**: its block's
tag, and its encoded tuple padded to the universe's width. -/
noncomputable def blkIxEltPad (zero : A) (u : Wide.BlkIx K A d) :
    Draw.Univ A R P K dd :=
  (blkTag R P K u.1, Draw.pad zero u.2)

omit [Finite R] [Finite P] [Finite A] [Finite K] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Draw.Univ A R P K dd)] in
/-- **Distinct registers of a padded file hold the bits of distinct
elements.** -/
theorem blkIxEltPad_injective {zero : A} (hle : d ≤ dd) :
    Function.Injective (blkIxEltPad (K := K) R P dd (d := d) zero) := by
  rintro ⟨b, w⟩ ⟨b', w'⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h
  exact Prod.ext (blkTag_injective R P K h1) (pad_injective hle h2)

omit [Finite R] [Finite P] [Finite A] [Finite K]
  [Language.wide.Structure (Draw.Univ A R P K dd)] in
/-- **The padded register order is the element order.** -/
theorem blkLePad_iff_tagTupleLe {zero : A} (hle : d ≤ dd)
    (u u' : Wide.BlkIx K A d) :
    Wide.blkLe K A d u u' ↔
      tagTupleLe (blkIxEltPad (K := K) R P dd zero u)
        (blkIxEltPad (K := K) R P dd zero u') := by
  rw [Wide.blkLe, lexRel, tagTupleLe]
  refine or_congr blkTag_lt_iff (Iff.trans ?_ (and_congr_left fun _ =>
    ⟨fun h => congrArg (blkTag R P K) h, fun h => blkTag_injective R P K h⟩))
  exact and_congr_right fun _ => (tupLeLex_pad_iff hle _ _).symm

omit [Finite R] [Finite P] [Finite A] [Finite K] in
/-- **The padded register order is the element order**, strictly: the file a
clocked program lays is laid out in the order of the addresses it stands
for. -/
theorem blkIxEltPad_mono {zero : A} (hle : d ≤ dd)
    (hord : ∀ x y : Draw.Univ A R P K dd, WMLe x y ↔ tagTupleLe x y)
    (u u' : Wide.BlkIx K A d) :
    WMLt (Wide.blkLe K A d) u u' ↔
      WMLt WMLe (blkIxEltPad (K := K) R P dd zero u)
        (blkIxEltPad (K := K) R P dd zero u') := by
  unfold WMLt
  rw [blkLePad_iff_tagTupleLe (R := R) (P := P) (dd := dd) hle u u',
    blkLePad_iff_tagTupleLe (R := R) (P := P) (dd := dd) hle u' u, hord, hord]

end PadFile

end DescriptiveComplexity
