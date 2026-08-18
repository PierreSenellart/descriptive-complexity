/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.LowFile
import DescriptiveComplexity.Problems.Wide.Key
import DescriptiveComplexity.Problems.Wide.DrawTable
import DescriptiveComplexity.Problems.Wide.IxAddr

/-!
# The file a clocked program lays out

A space-bounded program gives every element of its universe a register
(`DescriptiveComplexity.segFile`), and laying that file out costs one sweep of
it. A program on a clock cannot pay that: a rule sees the control and the cell
under the head and nothing else, so the only stretches it can walk are a fixed
number of **tuple roll-overs** long, and the universe is `|Tag|` of those with
`|Tag|` the program's own rule count.

What it can afford is one register per **block and tuple**, which is also all
that a register's contents ever depend on: the block one-hot goes through
`DescriptiveComplexity.Draw.tagBlk` alone and the name slots are the tuple, so
nothing of a tag beyond its block is ever read back
(`DescriptiveComplexity.Draw.Data.ixBack`). This file is that file:
`DescriptiveComplexity.blkFile`, one register per
`DescriptiveComplexity.Wide.BlkIx`, laid out on a stretch of consecutive
addresses in the block-major order `DescriptiveComplexity.Wide.blkLe`.

Everything it needs is already general – the interface
(`DescriptiveComplexity.IxFile`), the walks over it, the construction on a
stretch (`DescriptiveComplexity.ixSegFile`) and the background
(`DescriptiveComplexity.Draw.Data.ixBack`) – so all that is added here is the
instantiation and the two numbers a caller has to check: how many registers
there are, and that the stretch fits.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section BlkFile

variable {A K : Type} [LinearOrder A] [Finite A] [LinearOrder K] [Finite K] (U : Type)
variable [Language.wide.Structure U] [Finite U]

variable (A K) in
/-- **The file a clocked program lays out**: one register per block and tuple,
on the stretch of consecutive addresses whose ranks start at `base`. -/
noncomputable def blkFile (dd : ℕ) (h : IsLinOrd (WMLe (A := U))) {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx K A dd) ≤
      Nat.card {p : WPoint U // (wideData U).Posn p}) :
    IxFile U (Wide.BlkIx K A dd) (Wide.blkLe K A dd) :=
  ixSegFile (Wide.blkLe K A dd) h (Wide.isLinOrd_blkLe K A dd) hpos hbase

omit [LinearOrder A] [LinearOrder K] [Finite U] [Language.wide.Structure U] [Finite A] in
/-- **How many registers the file has**: one per block, one more for the
blockless ones, times the tuples. This is the number the stretch has to fit, and
the number of tuple roll-overs the laying sweep runs for. -/
theorem card_blkFile (dd : ℕ) :
    Nat.card (Wide.BlkIx K A dd) = (Nat.card K + 1) * Nat.card (Fin dd → A) :=
  Wide.card_blkIx K A dd

/-! ### Walking the file: the pointer's advance and its two ends

The sweep that lays the file out carries the register it is at in the machine's
control, and a rule advances it: `dstSt` is a *function* of the control, so the
next register has to be a function of the current one, not merely to exist.
These three are that function and the two ends its walk runs between; nothing
here is computed – a rule's fields are semantic – so the choice off
`DescriptiveComplexity.exists_ixSucc` is the definition, and its
characterization is what a caller discharges the walk with. -/

section BlkWalk

variable {A K : Type} [LinearOrder A] [Finite A] [LinearOrder K] [Finite K] (dd : ℕ)

open Classical in
variable (A K) in
/-- **The next register**: the successor of an index in the layout order, and
the index itself at the top of it. -/
noncomputable def blkNext (u : Wide.BlkIx K A dd) : Wide.BlkIx K A dd :=
  if h : ∃ v : Wide.BlkIx K A dd, WMLt (Wide.blkLe K A dd) u v then
    (exists_ixSucc (Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd) h).choose
  else u

variable (A K) in
/-- **The advance is the layout order's successor**, wherever there is one. -/
theorem ixSucc_blkNext {u : Wide.BlkIx K A dd}
    (hne : ∃ v : Wide.BlkIx K A dd, WMLt (Wide.blkLe K A dd) u v) :
    IxSucc (Wide.blkLe K A dd) u (blkNext A K dd u) := by
  classical
  rw [blkNext, dif_pos hne]
  exact (exists_ixSucc (Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd) hne).choose_spec

variable (A K) in
/-- **The advance stops at the top**, which is what makes the sweep's last round
recognizable without a second test. -/
theorem blkNext_of_top {u : Wide.BlkIx K A dd}
    (htop : ∀ v : Wide.BlkIx K A dd, Wide.blkLe K A dd v u) :
    blkNext A K dd u = u := by
  classical
  refine dif_neg fun hc => ?_
  obtain ⟨v, -, hne⟩ := hc
  exact hne (htop v)

variable (A K) in
/-- **The first register**: least in the layout order, where the laying sweep's
pointer starts. -/
noncomputable def blkBot [Nonempty A] : Wide.BlkIx K A dd :=
  (exists_least (Le := Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd)
    (P := fun _ => True) ⟨(none, fun _ => Classical.arbitrary A), trivial⟩).choose

variable (A K) in
/-- **The last register**: greatest in the layout order, where it stops. -/
noncomputable def blkTop [Nonempty A] : Wide.BlkIx K A dd :=
  (exists_greatest (Le := Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd)
    (P := fun _ => True) ⟨(none, fun _ => Classical.arbitrary A), trivial⟩).choose

variable (A K) in
/-- The first register is below every register. -/
theorem blkLe_blkBot [Nonempty A] (v : Wide.BlkIx K A dd) :
    Wide.blkLe K A dd (blkBot A K dd) v :=
  (exists_least (Le := Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd)
    (P := fun _ => True) ⟨(none, fun _ => Classical.arbitrary A), trivial⟩).choose_spec.2 v trivial

variable (A K) in
/-- Every register is below the last. -/
theorem blkLe_blkTop [Nonempty A] (v : Wide.BlkIx K A dd) :
    Wide.blkLe K A dd v (blkTop A K dd) :=
  (exists_greatest (Le := Wide.blkLe K A dd) (Wide.isLinOrd_blkLe K A dd)
    (P := fun _ => True) ⟨(none, fun _ => Classical.arbitrary A), trivial⟩).choose_spec.2 v trivial

variable (A K) in
/-- **The advance stops exactly at the last register**, so the walk's stop test
is the pointer reaching `DescriptiveComplexity.blkTop`. -/
theorem ixSucc_blkNext_of_ne [Nonempty A] {u : Wide.BlkIx K A dd}
    (hu : u ≠ blkTop A K dd) :
    IxSucc (Wide.blkLe K A dd) u (blkNext A K dd u) :=
  ixSucc_blkNext A K dd ⟨blkTop A K dd, blkLe_blkTop A K dd u, fun hc => hu
    ((Wide.isLinOrd_blkLe K A dd).2.2.1 u (blkTop A K dd) (blkLe_blkTop A K dd u) hc)⟩

variable (A) in
/-- **The last tuple**: greatest in the tuples' own lexicographic order. A
pointer holding it is at the last register of its block, which is what a
roll-over's guard reads. -/
noncomputable def tupTop [Nonempty A] : Fin dd → A :=
  (exists_greatest (Le := tupLeLex (A := A) (d := dd)) Wide.isLinOrd_tupLeLex
    (P := fun _ => True) ⟨fun _ => Classical.arbitrary A, trivial⟩).choose

variable (A) in
/-- Every tuple is below the last. -/
theorem tupLeLex_tupTop [Nonempty A] (v : Fin dd → A) : tupLeLex v (tupTop A dd) :=
  (exists_greatest (Le := tupLeLex (A := A) (d := dd)) Wide.isLinOrd_tupLeLex
    (P := fun _ => True) ⟨fun _ => Classical.arbitrary A, trivial⟩).choose_spec.2 v trivial

variable (A K) in
/-- **The next block**: the block of the register after the last of this one.
A destination phase is a constant, so a roll-over rule needs the next block as a
function of the current one alone, and this is it. -/
noncomputable def blkNextB [Nonempty A] (b : Option K) : Option K :=
  (blkNext A K dd (b, tupTop A dd)).1

variable (A K) in
/-- **Within a block the advance stays in it**: below the last tuple the next
register is the same block's, so the stepping rule keeps its phase and only the
roll-over changes it. -/
theorem blkNext_fst_of_ne_tupTop [Nonempty A] {u : Wide.BlkIx K A dd}
    (hu : u.2 ≠ tupTop A dd) : (blkNext A K dd u).1 = u.1 := by
  classical
  have hlt : WMLt (Wide.blkLe K A dd) u (u.1, tupTop A dd) := by
    refine ⟨Or.inr ⟨rfl, tupLeLex_tupTop A dd u.2⟩, ?_⟩
    rintro (⟨-, hc⟩ | ⟨-, hc⟩)
    · exact hc rfl
    · exact hu ((Wide.isLinOrd_tupLeLex (A := A) (d := dd)).2.2.1 _ _
        (tupLeLex_tupTop A dd u.2) hc)
  have hs := ixSucc_blkNext A K dd ⟨(u.1, tupTop A dd), hlt⟩
  have hle : Wide.blkLe K A dd (blkNext A K dd u) (u.1, tupTop A dd) :=
    hs.2 (u.1, tupTop A dd) hlt
  rcases hle with ⟨hb1, hb2⟩ | ⟨hb, -⟩
  · rcases hs.1.1 with ⟨h1, h2⟩ | ⟨h, -⟩
    · exact absurd ((Wide.isLinOrd_blkTagLe K).2.2.1 _ _ h1 hb1) h2
    · exact h.symm
  · exact hb

variable (A K) in
/-- **The last register's tuple is the last tuple**: the order is block-major,
so the greatest index is the greatest tuple of the greatest block. This is what
makes the sweep's stop test – the pointer holds the last tuple *and* the last
register – fire at one place. -/
theorem snd_blkTop [Nonempty A] : (blkTop A K dd).2 = tupTop A dd := by
  have hle := blkLe_blkTop A K dd ((blkTop A K dd).1, tupTop A dd)
  rcases hle with ⟨-, hb⟩ | ⟨-, hb⟩
  · exact absurd rfl hb
  · exact (Wide.isLinOrd_tupLeLex (A := A) (d := dd)).2.2.1 _ _
      (tupLeLex_tupTop A dd (blkTop A K dd).2) hb

end BlkWalk

end BlkFile

/-! ### The stretch fits

The one arithmetic fact a caller of `DescriptiveComplexity.blkFile` owes: the
file has fewer registers than the universe has elements – a block and a tuple
*is* an element of the universe, the blockless register taking the alphabet tag
– and the addresses are `2 ^` that, so a stretch based at `1` always fits. -/

section Fits

variable {A R P K : Type} [LinearOrder A] [Finite A] [Finite R] [Finite P]
variable [LinearOrder K] [Finite K] (dd : ℕ)

variable (R P K) in
/-- The blockless register and each block, as tags: the alphabet tag stands for
the blockless one. -/
def blkTag : Option K → Draw.Tag R P K
  | none => .sym
  | some k => .arg k

variable (R P K) in
omit [Finite R] [Finite P] [LinearOrder K] [Finite K] [LinearOrder A] [Finite A] in
theorem blkTag_injective : Function.Injective (blkTag R P K) := by
  rintro (_ | k) (_ | k') h
  · rfl
  · exact absurd h (by simp [blkTag])
  · exact absurd h (by simp [blkTag])
  · exact congrArg some (by injection h)

end Fits

section IxAddr

variable {A R P K : Type} [LinearOrder A] [Finite A] [Finite R] [Finite P]
variable [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite K] (dd : ℕ)
variable [Language.wide.Structure (Draw.Univ A R P K dd)]

/-! ### The address a clocked file's marks stand for

A mark on the file is an address of the tape (`DescriptiveComplexity.ixAddr`),
and the correspondence is what lets a program hold an address it cannot see –
the one under its head – on registers it can. It is only used on the **argument**
registers, and the two conditions of `DescriptiveComplexity.wmIncr_ixAddr` hold
of exactly those: the argument tags are the greatest ones
(`DescriptiveComplexity.Draw.lt_arg`), so nothing the file has no register for
lies above an argument element, and the block order was chosen to make
`DescriptiveComplexity.blkTag` monotone.
-/

variable (R P) in
/-- **The element a register holds the bit of.** -/
def blkIxElt (u : Wide.BlkIx K A dd) : Draw.Univ A R P K dd := (blkTag R P K u.1, u.2)

variable (A K) in
/-- **The registers an address uses**: the argument blocks, the blockless ones
standing for the alphabet tag and never entering a logical address. -/
def BlkIxUse (u : Wide.BlkIx K A dd) : Prop := ∃ k : K, u.1 = some k

omit [Finite R] [Finite P] [Finite A] [Finite K]
  [Language.wide.Structure (Draw.Univ A R P K dd)] in
/-- **A block is below another exactly when its tag is**: the block order was
built for this, the blockless registers taking the alphabet tag, which the
argument tags all sit above. -/
theorem blkTag_lt_iff {b b' : Option K} :
    (Wide.blkTagLe K b b' ∧ b ≠ b') ↔ blkTag R P K b < blkTag R P K b' := by
  match b, b' with
  | none, none => exact ⟨fun h => absurd rfl h.2, fun h => absurd h (lt_irrefl _)⟩
  | none, some k =>
    exact ⟨fun _ => Draw.lt_arg (Draw.Tag.sym) k (by rintro j ⟨⟩),
      fun _ => ⟨trivial, by rintro ⟨⟩⟩⟩
  | some k, none =>
    exact ⟨fun h => h.1.elim, fun h =>
      absurd (h.trans (Draw.lt_arg (Draw.Tag.sym) k (by rintro j ⟨⟩))) (lt_irrefl _)⟩
  | some k, some k' =>
    refine ⟨fun h => (Draw.lt_arg_arg k k').mpr (lt_of_le_of_ne h.1 fun hc =>
      h.2 (congrArg some hc)), fun h => ⟨le_of_lt ((Draw.lt_arg_arg k k').mp h), ?_⟩⟩
    intro hc
    exact absurd ((Draw.lt_arg_arg k k').mp h) (by
      rw [show k = k' from Option.some.inj hc]; exact lt_irrefl _)

omit [Finite R] [Finite P] [Finite A] [Finite K]
  [Language.wide.Structure (Draw.Univ A R P K dd)] in
/-- **The register order is the element order**: the block order was built
for it. -/
theorem blkLe_iff_tagTupleLe (u u' : Wide.BlkIx K A dd) :
    Wide.blkLe K A dd u u' ↔ tagTupleLe (blkIxElt R P dd u) (blkIxElt R P dd u') := by
  rw [Wide.blkLe, lexRel, tagTupleLe]
  exact or_congr blkTag_lt_iff (and_congr_left fun _ =>
    ⟨fun h => congrArg (blkTag R P K) h, fun h => blkTag_injective R P K h⟩)

omit [Finite R] [Finite P] [Finite A] [Finite K] in
/-- **The register order is the element order**, strictly. -/
theorem blkIxElt_mono
    (hord : ∀ x y : Draw.Univ A R P K dd, WMLe x y ↔ tagTupleLe x y)
    (u u' : Wide.BlkIx K A dd) :
    WMLt (Wide.blkLe K A dd) u u' ↔ WMLt WMLe (blkIxElt R P dd u) (blkIxElt R P dd u') := by
  unfold WMLt
  rw [blkLe_iff_tagTupleLe (R := R) (P := P) dd u u',
    blkLe_iff_tagTupleLe (R := R) (P := P) dd u' u, hord, hord]

omit [Finite R] [Finite P] [Finite A] [Finite K] in
/-- **Nothing without a register lies above an argument element**: the argument
tags come last, so the elements the file names are upward closed and the
addresses over them are an initial interval of the tape. -/
theorem blkIxElt_up
    (hord : ∀ x y : Draw.Univ A R P K dd, WMLe x y ↔ tagTupleLe x y)
    {u : Wide.BlkIx K A dd} (hu : BlkIxUse A K dd u) {x : Draw.Univ A R P K dd}
    (hlt : WMLt WMLe (blkIxElt R P dd u) x) :
    ∃ u' : Wide.BlkIx K A dd, BlkIxUse A K dd u' ∧ blkIxElt R P dd u' = x := by
  obtain ⟨k, hk⟩ := hu
  have hle : tagTupleLe (blkIxElt R P dd u) x := (hord _ _).mp hlt.1
  have hfst : (blkIxElt R P dd u).1 = Draw.Tag.arg k := by
    change blkTag R P K u.1 = _; rw [hk]; rfl
  have harg : ∃ k' : K, x.1 = Draw.Tag.arg k' := by
    by_contra hc
    push Not at hc
    have hlt' : x.1 < Draw.Tag.arg k := Draw.lt_arg x.1 k hc
    rcases hle with hb | ⟨hb, -⟩
    · rw [hfst] at hb
      exact absurd (hb.trans hlt') (lt_irrefl _)
    · rw [hfst] at hb
      exact absurd (hb ▸ hlt') (lt_irrefl _)
  obtain ⟨k', hk'⟩ := harg
  exact ⟨(some k', x.2), ⟨k', rfl⟩, Prod.ext hk'.symm rfl⟩

end IxAddr

end DescriptiveComplexity
