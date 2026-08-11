/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTags

/-!
# The alphabet: coordinates as tracks

A symbol of the emitted machine is an *element* of the interpreted universe, so it
is a tagged tuple `(sym, c)` with `c : Fin dd → A`. What a program needs of its
symbols is a constant number of independent **tracks** – the two stage bits, the
working-cell marker, the register digits, the mark that says "this cell is a
register" – and the discipline that gives it them is the obvious one:

> one **coordinate** of the tuple per track, holding one of two designated
> elements of `A`.

The two elements are the reduction's choice; in the instance it draws they are the
least and the greatest of the ordered source structure, both first-order
definable, which is why the degenerate one-element structure has to be gated
first-order as it is elsewhere in the catalog.

`DescriptiveComplexity.Pfp.withBit` writes a track and
`DescriptiveComplexity.Pfp.bitAt` reads one, and the lemmas below are everything a
program uses about them: a track reads back what was written, writing a track
leaves the others alone, and the two designated elements being distinct is the
only hypothesis any of it needs.

Nothing here mentions the machine. These are facts about tuples, and they are what
turns `DescriptiveComplexity.regBit_congr` – "changing a track moves the tape only
at that track's cell" – into a statement about the symbols a program actually
writes: its tape is `fun r => (sym, withBit … (regBit m r))`, so the coherence
condition every register pass asks for is `congrArg` applied to that.
-/

namespace DescriptiveComplexity

namespace Pfp

section Alphabet

variable {A : Type} {dd : ℕ}

/-- **Reading a track**: the coordinate carries the designated element `one`. -/
def bitAt (one : A) (c : Fin dd → A) (j : Fin dd) : Prop := c j = one

open Classical in
/-- **Writing a track**: the tuple with one coordinate set to `one` or to `zero`
according to a proposition, and every other coordinate left alone. -/
noncomputable def withBit (zero one : A) (j : Fin dd) (c : Fin dd → A) (P : Prop) : Fin dd → A :=
  Function.update c j (if P then one else zero)

variable {zero one : A} {j k : Fin dd} {c : Fin dd → A} {P : Prop}

/-- A track written `True` holds the designated `one`. -/
theorem withBit_self_pos (hP : P) : withBit zero one j c P j = one := by
  simp [withBit, hP]

/-- A track written `False` holds the designated `zero`. -/
theorem withBit_self_neg (hP : ¬P) : withBit zero one j c P j = zero := by
  simp [withBit, hP]

/-- **Writing a track leaves the others alone**, which is what makes the tracks
independent and lets a program keep several at once. -/
@[simp]
theorem withBit_of_ne (h : k ≠ j) : withBit zero one j c P k = c k := by
  simp [withBit, h]

/-- **A track reads back what was written.** The only hypothesis is that the two
designated elements differ – which is why a reduction has to gate the
one-element structure. -/
theorem bitAt_withBit (hne : zero ≠ one) : bitAt one (withBit zero one j c P) j ↔ P := by
  by_cases hp : P
  · exact iff_of_true (by rw [bitAt, withBit_self_pos hp]) hp
  · refine iff_of_false ?_ hp
    rw [bitAt, withBit_self_neg hp]
    exact hne

/-- **Reading a track other than the one written** gives what was there. -/
@[simp]
theorem bitAt_withBit_of_ne (h : k ≠ j) :
    bitAt one (withBit zero one j c P) k ↔ bitAt one c k := by
  rw [bitAt, bitAt, withBit_of_ne h]

/-- **A symbol determines its tracks.** Two symbols carrying different bits at a
coordinate are different elements, whatever else they hold. This is what a
transition table needs twice over: to read a track off the symbol under the head,
and to be *deterministic*, since two transitions distinguished only by the track
they read must apply to different symbols. -/
theorem withBit_inj (hne : zero ≠ one) {c' : Fin dd → A} {Q : Prop}
    (h : withBit zero one j c P = withBit zero one j c' Q) : P ↔ Q := by
  have h1 : bitAt one (withBit zero one j c P) j ↔ bitAt one (withBit zero one j c' Q) j := by
    rw [h]
  exact ((bitAt_withBit hne).symm.trans h1).trans (bitAt_withBit hne)

/-- **Symbols differing in a track are distinct elements**, the contrapositive of
`DescriptiveComplexity.Pfp.withBit_inj` and the form a distinctness obligation
comes in. -/
theorem withBit_ne_of_not_iff (hne : zero ≠ one) {c' : Fin dd → A} {Q : Prop}
    (h : ¬(P ↔ Q)) : withBit zero one j c P ≠ withBit zero one j c' Q :=
  fun hc => h (withBit_inj hne hc)

/-- **A write is determined by the bit it writes.** This is the form
`DescriptiveComplexity.regBit_congr` is consumed in: a program's tape is
`fun r => (sym, withBit … (regBit m r))`, so moving to a track that agrees off one
element moves the tape only at that element's cell, by `congrArg` through this. -/
theorem withBit_congr {Q : Prop} (h : P = Q) :
    withBit zero one j c P = withBit zero one j c Q :=
  congrArg _ h

end Alphabet

end Pfp

end DescriptiveComplexity
