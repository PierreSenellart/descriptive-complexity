/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpGeom
import DescriptiveComplexity.Padding

/-!
# The layout's geometry is the padding layer's, so its formulas are written

The bridge the defining formulas of the EXPSPACE reduction are read through.
`DescriptiveComplexity.Padding` already carries the shape formulas every
tagged-tuple interpretation in this library needs – a coordinate is the least
element (`DescriptiveComplexity.botF`), a tuple is canonically padded
(`DescriptiveComplexity.canonF`), two tuples are equal
(`DescriptiveComplexity.eqTupF`), they agree below a length
(`DescriptiveComplexity.agreeF`), one is the padded reading of the other
through an index map (`DescriptiveComplexity.padTupF`) – each with its
realization lemma. The EXPSPACE layout speaks of the same objects under its own
names (`DescriptiveComplexity.Pfp.pad`, `DescriptiveComplexity.Pfp.unpad`,
`DescriptiveComplexity.Pfp.IsPad`), and this file says they are the same:

* `DescriptiveComplexity.Pfp.pad_eq_pad` and
  `DescriptiveComplexity.Pfp.unpad_eq_pref` – the two paddings and the two
  readings are one definition;
* `DescriptiveComplexity.Pfp.isPad_iff_canon` – being canonically padded *is*
  being canonical, once the designated `zero` is the order's least element,
  which is the choice a reduction into
  `DescriptiveComplexity.DWideAcceptSpace` makes anyway (an interpretation
  cannot name an arbitrary element, and the two designated ones have to be
  `⊥` and `⊤`);
* `DescriptiveComplexity.Pfp.realize_canonF_isPad` and
  `DescriptiveComplexity.Pfp.realize_padTupF_pad` – the two realizations in the
  layout's own vocabulary, which is the form the eleven defining formulas will
  cite.

So the *shape* half of the interpretation is already written. What is not, and
what the remaining work is, is the **rule** half: a transition's guard and what
it writes are arbitrary functions in
`DescriptiveComplexity.Pfp.Rule`, and each kit owes a syntactic counterpart —
a quantifier-free formula over the payload slots for the guard, and per-slot
“copy this slot or write this constant” for the destination and the written
symbol.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

section Geometry

variable {A : Type} {c dd : ℕ}

/-- **The layout's padding is the padding layer's**: one definition under two
names. -/
theorem pad_eq_pad (zero : A) (w : Fin c → A) :
    pad (dd := dd) zero w = _root_.DescriptiveComplexity.pad (D := dd) zero w := rfl

/-- **And its reading back is the prefix.** -/
theorem unpad_eq_pref (hc : c ≤ dd) (v : Fin dd → A) :
    unpad hc v = _root_.DescriptiveComplexity.pref hc v :=
  funext fun _ => congrArg v (Fin.ext rfl)

variable [PartialOrder A]

/-- **Being canonically padded is being canonical**, once the designated
element is a least one: `DescriptiveComplexity.IsBot` and “equal to `zero`”
are the same condition on a coordinate, by antisymmetry. -/
theorem isPad_iff_canon {zero : A} (h₀ : IsBot zero) (v : Fin dd → A) :
    IsPad c zero v ↔ _root_.DescriptiveComplexity.Canon c v := by
  refine forall_congr' fun j => imp_congr Iff.rfl ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
    exact fun b => h₀ b
  · exact le_antisymm (h zero) (h₀ (v j))

end Geometry

/-! ### The two realizations, in the layout's own terms -/

section Realize

variable {L : Language.{0, 0}} {A : Type} [L.Structure A] [LinearOrder A]
variable {γ : Type} {dd : ℕ} {v : γ → A}

/-- **A tuple of the interpreted universe is canonically padded**, as a
formula: `DescriptiveComplexity.canonF` read at the layout's `IsPad`, with
the least element for `zero`. This is what the defining formula of a
transition, of an accepting state and of the blank all begin with — the
condition that gives an element one spelling, and so the emitted machine its
determinism. -/
theorem realize_canonF_isPad {zero : A} (h₀ : IsBot zero) {c : ℕ}
    {x : Fin dd → γ} :
    (_root_.DescriptiveComplexity.canonF (L := L) c x).Realize v ↔
      IsPad c zero fun j => v (x j) :=
  _root_.DescriptiveComplexity.realize_canonF.trans (isPad_iff_canon h₀ _).symm

/-- **A tuple of the interpreted universe is a padded payload read off another
one**, as a formula: `DescriptiveComplexity.padTupF` at the layout's `pad` and
`unpad`. This is the shape of `Src`, `Dst`, `Read` and `Write` — the tag of the
target is decided when the formula is built, and what is left of each is that
its coordinates are the padded reading of the transition's. -/
theorem realize_padTupF_pad {zero : A} (h₀ : IsBot zero) {c : ℕ}
    (hc : c ≤ dd) {u x : Fin dd → γ} :
    (_root_.DescriptiveComplexity.padTupF (L := L)
        (fun j : Fin c => Fin.castLE hc j) u x).Realize v ↔
      (fun j => v (x j)) = pad zero (unpad hc fun j => v (u j)) := by
  rw [_root_.DescriptiveComplexity.realize_padTupF]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [pad_eq_pad, unpad_eq_pref]
    exact _root_.DescriptiveComplexity.eq_pad_of_padTup h₀ h
  · rw [h, pad_eq_pad, unpad_eq_pref]
    exact _root_.DescriptiveComplexity.padTup_pad h₀ _ _

end Realize

end Pfp

end DescriptiveComplexity
