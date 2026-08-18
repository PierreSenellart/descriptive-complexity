/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.BlkFile
import DescriptiveComplexity.Problems.Wide.DrawName

/-!
# The layout of a clocked program's file

`DescriptiveComplexity.blkFile` gives a program one register per block and
tuple. This file reads that as a `DescriptiveComplexity.Draw.LaidFile`, which is
what the background (`DescriptiveComplexity.Draw.Data.ixBack`) and the loops
run against, and checks the two properties a navigation *by name* asks of a
layout.

**The width is `dd`, not `dd₀`, and that is what a seek needs.** A mark carries
`dd₀` coordinates, so a *name* is a block and `dd₀` coordinates, and a scan by
name only ever stops at a canonically padded register – which would make a file
of `dd₀`-tuples enough for the copy loops. It is not enough for the mirror: the
mirror and the target of a seek are held one bit per register, and the addresses
a seek passes through are every logical address below its target, which mark
argument elements of *every* tuple. So the index is `Option K × (Fin dd → A)`,
the register's tuple is its index's, and the named registers are those the
padding pins – exactly the ones inside it.

The two properties are then:

* `DescriptiveComplexity.Draw.Layout.NameSep` – a block and the named
  coordinates spell at most one register: the index *is* the pair, the
  coordinates below `dd₀` are the name's, and those above are `zero` on both
  sides because a scan by name asks its registers to be canonically padded.
* `DescriptiveComplexity.Draw.Layout.HasName` – and at least one, for every
  block and every name, the register being the name padded.

Together they are the stopping condition of a scan by name
(`DescriptiveComplexity.Draw.Data.nameGF_unique_addr`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section BlkLayout

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite (Univ A R' P' dt.KIx dt.dd)]

namespace Data

/-- **The file a clocked program lays out, with its layout**: the registers of
`DescriptiveComplexity.blkFile`, in the block-major order, each naming its own
block and its own tuple. -/
noncomputable def blkLaid
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p}) :
    LaidFile dt A R' P' (Wide.BlkIx dt.KIx A dt.dd) where
  cell := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).cell
  le := Wide.blkLe dt.KIx A dt.dd
  blk := Prod.fst
  arg := Prod.snd
  strictMono := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).strictMono
  cell_nonempty := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).cell_nonempty

variable {dt}

omit [Finite R'] [Finite P'] in
/-- **The layout order of a clocked program's file is linear.** -/
theorem isLinOrd_blkLaid_le
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p}) :
    IsLinOrd (dt.blkLaid h hpos hbase).le :=
  Wide.isLinOrd_blkLe dt.KIx A dt.dd

omit [Finite R'] [Finite P'] in
/-- **The marks tell a clocked program's registers apart**: a register *is* its
block and its tuple, the named coordinates are given and the ones above `dd₀`
are `zero` on both sides, which is what a scan by name asks of the registers it
may stop at. -/
theorem nameSep_blkLaid (zero : A)
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    (hdd : dt.dd0 ≤ dt.dd) :
    (dt.blkLaid h hpos hbase).toLayout.NameSep zero hdd := by
  intro b u u' hb hb' hp hp' hn
  refine Prod.ext (hb.trans hb'.symm) (funext fun j => ?_)
  by_cases hj : (j : ℕ) < dt.dd0
  · have h := hn ⟨j, hj⟩
    change u.2 (Fin.castLE hdd ⟨j, hj⟩) = u'.2 (Fin.castLE hdd ⟨j, hj⟩) at h
    exact (congrArg u.2 (Fin.ext rfl)).symm.trans (h.trans (congrArg u'.2 (Fin.ext rfl)))
  · exact (hp j (by omega)).trans (hp' j (by omega)).symm

omit [Finite R'] [Finite P'] in
/-- **A clocked program's file has a register for every name**: its index ranges
over every block and every tuple, so the name's own padding is one of them. -/
theorem hasName_blkLaid (zero : A)
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p}) :
    (dt.blkLaid h hpos hbase).toLayout.HasName zero :=
  fun b c => ⟨(some (toLex b), padTup zero c), rfl, rfl⟩

omit [Finite R'] [Finite P'] in
/-- **A named register of a clocked program's file stands for the element it
names**: the `heltP` coherence every layer of the evaluation asks of a file, at
the laid one. The register is the name padded (`hasName_blkLaid`), and the
element it stands for is that block's tag over that tuple. -/
theorem blkIxElt_reg_blkLaid (zero : A)
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    (hhas : (dt.blkLaid h hpos hbase).toLayout.HasName zero)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    blkIxElt R' P' dt.dd ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c) =
      dt.blkElt b (pad zero c) := by
  have hb : ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c).1 = some b :=
    Layout.blk_reg hhas b c
  have ha : ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c).2 = padTup zero c :=
    Layout.arg_reg hhas b c
  refine Prod.ext ?_ ha
  change blkTag R' P' dt.KIx
    ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c).1 = _
  rw [hb]
  rfl

omit [Finite R'] [Finite P'] in
/-- **A register's block is the block of the element it stands for**: the
`hblkP` coherence, at the laid file. Both sides are the register's own index –
one read off the layout, the other off the tag it names. -/
theorem blk_blkLaid_eq_tagBlk
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    (u : Wide.BlkIx dt.KIx A dt.dd) :
    (dt.blkLaid h hpos hbase).blk u = tagBlk (blkIxElt R' P' dt.dd u).1 := by
  obtain ⟨b, t⟩ := u
  cases b <;> rfl

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **A logical address is held by the file's registers**: every argument
element is the element of the register that names it, and that register is one
of the used ones. This is the `hvh` the legs ask for. -/
theorem ixHolds_blkLaid {s : Univ A R' P' dt.KIx dt.dd → Prop}
    (harg : ∀ x, s x → ∃ i : dt.KIx, x.1 = Tag.arg i) :
    IxHolds (blkIxElt R' P' dt.dd) (BlkIxUse A dt.KIx dt.dd) s := by
  intro x hx
  obtain ⟨i, hi⟩ := harg x hx
  exact ⟨(some i, x.2), ⟨i, rfl⟩, Prod.ext hi.symm rfl⟩

omit [Finite R'] [Finite P'] in
/-- **A named register is a used one**: it belongs to a block, and the blockless
registers are the only unused ones. This is the `hxdUse` the stage atom's
destination registers ask for. -/
theorem blkIxUse_reg_blkLaid (zero : A)
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    (hhas : (dt.blkLaid h hpos hbase).toLayout.HasName zero)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    BlkIxUse A dt.KIx dt.dd
      ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c) :=
  ⟨toLex b, Layout.blk_reg hhas b c⟩

/-! ### The widths of the laid file

Every walk of the evaluation is charged against a width, and at the laid file
each of them is bounded by the stretch the file occupies: the base, the number
of registers, and – for what walks the *tape* rather than the file – the number
of addresses. These are the `hgap`, `hcostR`, `hwP`, `hwR` and `hwK` the legs
ask for, none of them computed. -/

section Widths

variable (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
variable {base : ℕ} (hpos : 0 < base)
variable (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
  Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
    (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})

omit [Finite R'] [Finite P'] in
/-- **A register's rank is its index's, above the base.** -/
theorem wideRank_blkLaid_cell (u : Wide.BlkIx dt.KIx A dt.dd) :
    wideRank ((dt.blkLaid h hpos hbase).cell u) =
      base + ixRank (Wide.blkLe dt.KIx A dt.dd) u :=
  wideRank_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase u

omit [Finite R'] [Finite P'] in
/-- **The file lies inside its stretch**: no register's rank passes the base and
the number of registers. -/
theorem wideRank_blkLaid_cell_lt (u : Wide.BlkIx dt.KIx A dt.dd) :
    wideRank ((dt.blkLaid h hpos hbase).cell u) <
      base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) := by
  rw [dt.wideRank_blkLaid_cell h hpos hbase u]
  exact Nat.add_lt_add_left (ixRank_lt_card _ u) base

omit [Finite R'] [Finite P'] in
/-- **Consecutive registers are consecutive addresses**, so the gap width of the
laid file is one. -/
theorem gap_blkLaid {u u' : Wide.BlkIx dt.KIx A dt.dd}
    (hs : IxSucc (dt.blkLaid h hpos hbase).le u u') :
    wideRank ((dt.blkLaid h hpos hbase).cell u') -
        wideRank ((dt.blkLaid h hpos hbase).cell u) ≤ 1 :=
  blkFile_gap A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase hs

omit [Finite R'] [Finite P'] in
/-- **A walk to a named register costs the stretch**: the `hcostR` width, at the
laid file and whatever the marker. -/
theorem costR_blkLaid (zero : A)
    (hhas : (dt.blkLaid h hpos hbase).toLayout.HasName zero)
    (v : Univ A R' P' dt.KIx dt.dd → Prop)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    2 * (wideRank ((dt.blkLaid h hpos hbase).cell
        ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c)) - wideRank v) + 2 ≤
      2 * (base + Nat.card (Wide.BlkIx dt.KIx A dt.dd)) + 2 := by
  have := dt.wideRank_blkLaid_cell_lt h hpos hbase
    ((dt.blkLaid h hpos hbase).toLayout.reg hhas b c)
  omega

variable [Nonempty A]

omit [Finite R'] [Finite P'] in
/-- **A sweep of the file costs the stretch twice**: the `hwP` width, at the
laid file's own top and bottom and the gap width one. -/
theorem wP_blkLaid :
    wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) + 2 +
        ((ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
          ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 + 1) +
        wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)) ≤
      2 * base + 3 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 3 := by
  have htop := dt.wideRank_blkLaid_cell_lt h hpos hbase (blkTop A dt.KIx dt.dd)
  have hbot := dt.wideRank_blkLaid_cell_lt h hpos hbase (blkBot A dt.KIx dt.dd)
  have hr := ixRank_lt_card (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd)
  omega

omit [Finite R'] [Finite P'] in
/-- **A reset costs the working area**: the `hwR` width. A reset scans from the
marker down to the empty address, and the marker is *below the file* – which is
where a program that lays its file above its data has put it – so the walk is
the stretch and not the tape. -/
theorem wR_blkLaid (s : Univ A R' P' dt.KIx dt.dd → Prop)
    (hs : WMSetLt WMLe s ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd))) :
    wideRank s + 4 ≤ base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 4 := by
  have h1 : wideRank s < wideRank ((dt.blkLaid h hpos hbase).cell
      (blkBot A dt.KIx dt.dd)) := (wideRank_lt_iff h _ _).mpr hs
  have h2 := dt.wideRank_blkLaid_cell_lt h hpos hbase (blkBot A dt.KIx dt.dd)
  omega

omit [Finite R'] [Finite P'] in
/-- **A seek costs the working area once per bit of its target**: the `hwK`
width, the coarsest of them. Both the target and the marker lie below the file,
so every factor is the stretch. -/
theorem wK_blkLaid (T : Univ A R' P' dt.KIx dt.dd → Prop)
    (hT : WMSetLt WMLe T ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd))) :
    wideRank T *
        (1 + (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) + 3 +
            (ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
              ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 +
            wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd))) +
          (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) +
            ((ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
              ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 + 1) +
            wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)) + 4)) + 1 +
      (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) + 3 +
        (ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
          ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 +
        wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd))) ≤
    (base + Nat.card (Wide.BlkIx dt.KIx A dt.dd)) *
        (4 * (base + Nat.card (Wide.BlkIx dt.KIx A dt.dd)) +
          2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 9) +
      2 * (base + Nat.card (Wide.BlkIx dt.KIx A dt.dd)) +
      Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 4 := by
  have htop := dt.wideRank_blkLaid_cell_lt h hpos hbase (blkTop A dt.KIx dt.dd)
  have hbot := dt.wideRank_blkLaid_cell_lt h hpos hbase (blkBot A dt.KIx dt.dd)
  have hr := ixRank_lt_card (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd)
  have hTlt : wideRank T < wideRank ((dt.blkLaid h hpos hbase).cell
      (blkBot A dt.KIx dt.dd)) := (wideRank_lt_iff h _ _).mpr hT
  have hmul := Nat.mul_le_mul (le_of_lt (show wideRank T <
      base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) by omega))
    (show 1 + (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) + 3 +
          (ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
            ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 +
          wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd))) +
        (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) +
          ((ixRank (Wide.blkLe dt.KIx A dt.dd) (blkTop A dt.KIx dt.dd) -
            ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd)) * 1 + 1) +
          wideRank ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)) + 4) ≤
      4 * (base + Nat.card (Wide.BlkIx dt.KIx A dt.dd)) +
        2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + 9 from by omega)
  omega

omit [Finite R'] [Finite P'] [Nonempty A] in
/-- **The program's data lies below its file**: an address at or below the
logical top is below every register, as soon as the file is based above the
logical top. This is the `hwork` the legs ask for, at a file the program lays
itself: at the input channel's ladder the criterion is that the address misses
the least element, and here it is where the base was put – the working region is
an initial stretch and the file sits above it. -/
theorem work_blkLaid
    (hlog : wideRank (logicalTop (R := R') (P := P') (K := dt.KIx)
      (V := Fin dt.dd → A)) < base)
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hlogr : WMSetLe WMLe r (logicalTop (R := R') (P := P') (K := dt.KIx)
      (V := Fin dt.dd → A)))
    (u : Wide.BlkIx dt.KIx A dt.dd) :
    WMSetLt WMLe r ((dt.blkLaid h hpos hbase).cell u) := by
  refine (wideRank_lt_iff h _ _).mp ?_
  have h1 : wideRank r ≤ wideRank (logicalTop (R := R') (P := P') (K := dt.KIx)
    (V := Fin dt.dd → A)) := wideRank_mono h hlogr
  have h2 := dt.wideRank_blkLaid_cell h hpos hbase u
  omega

omit [Finite R'] [Finite P'] in
/-- **Below the file nothing is a register**: the registers start at the base,
so an address below the first of them is nobody's. This is what lets the entry
state's background be read off `ixBack_of_not_reg` there. -/
theorem not_reg_blkLaid_of_lt
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : WMSetLt WMLe r ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    (u : Wide.BlkIx dt.KIx A dt.dd) :
    r ≠ (dt.blkLaid h hpos hbase).cell u := by
  have h1 : wideRank r < wideRank ((dt.blkLaid h hpos hbase).cell
      (blkBot A dt.KIx dt.dd)) := (wideRank_lt_iff h _ _).mpr hr
  have h2 := dt.wideRank_blkLaid_cell h hpos hbase (blkBot A dt.KIx dt.dd)
  have h3 := dt.wideRank_blkLaid_cell h hpos hbase u
  have h4 : ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd) = 0 :=
    ixRank_of_bot (Wide.isLinOrd_blkLe dt.KIx A dt.dd) (blkLe_blkBot A dt.KIx dt.dd)
  intro hc
  rw [hc] at h1
  omega

omit [Finite R'] [Finite P'] [Nonempty A] in
/-- **Above the stretch nothing is a register either**: the last register sits
one short of the stretch's end. -/
theorem not_reg_blkLaid_of_not_lt_top
    (hlt : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base))
    (u : Wide.BlkIx dt.KIx A dt.dd) :
    r ≠ (dt.blkLaid h hpos hbase).cell u := by
  have hle : WMSetLe WMLe (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) r := by
    rcases (isLinOrd_wmSetLe h).2.2.2 (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) r with
      hc | hc
    · exact hc
    · have hEq : r = ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base := by
        by_contra hne
        exact hr ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩)
      exact hEq ▸ (isLinOrd_wmSetLe h).1 r
  have h1 : wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) ≤ wideRank r :=
    wideRank_mono h hle
  have h2 := wideRank_ixSegTop (I := Wide.BlkIx dt.KIx A dt.dd) h hlt
  have h3 := dt.wideRank_blkLaid_cell h hpos hbase u
  have h4 := ixRank_lt_card (Wide.blkLe dt.KIx A dt.dd) u
  intro hc
  rw [hc] at h1
  omega

omit [Nonempty A] in
/-- **`hwork` in the form the legs ask for it**: an address every element of
which is *argument*-tagged – a logical address, which is what the stage atom
proves of the TARGET it builds – lies below every register. The two steps are
`DescriptiveComplexity.Draw.wmSetLe_logicalTop` (a logical address is at or below
the last one) and `work_blkLaid` (and the last one is below the file, the base
having been put above it). -/
theorem workArg_blkLaid
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    (hlog : wideRank (logicalTop (R := R') (P := P') (K := dt.KIx)
      (V := Fin dt.dd → A)) < base)
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (harg : ∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (u : Wide.BlkIx dt.KIx A dt.dd) :
    WMSetLt WMLe r ((dt.blkLaid h hpos hbase).cell u) := by
  have hrel : (WMLe : Univ A R' P' dt.KIx dt.dd → Univ A R' P' dt.KIx dt.dd → Prop) =
      lexRel (· ≤ · : Tag R' P' dt.KIx → Tag R' P' dt.KIx → Prop)
        (tupLeLex (A := A) (d := dt.dd)) :=
    funext fun x => funext fun y => propext
      ((hord x y).trans (Wide.tagTupleLe_iff_lexRel x y))
  refine dt.work_blkLaid h hpos hbase hlog ?_ u
  rw [hrel]
  refine wmSetLe_logicalTop Wide.isLinOrd_tupLeLex fun τ hτ v hc => ?_
  obtain ⟨i, hi⟩ := harg (τ, v) hc
  exact hτ i hi

end Widths

end Data

end BlkLayout

end Draw

end DescriptiveComplexity
