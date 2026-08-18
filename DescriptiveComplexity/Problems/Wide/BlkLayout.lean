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

variable [Nonempty A]

end Widths

end Data

end BlkLayout

end Draw

end DescriptiveComplexity
