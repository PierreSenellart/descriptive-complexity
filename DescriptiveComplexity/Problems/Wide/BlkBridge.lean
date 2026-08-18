/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxPack
import DescriptiveComplexity.Problems.Wide.BlkLayout

/-!
# The two bridges at the file a clocked program lays

`DescriptiveComplexity.Problems.Wide.DrawIxPack` proves the gates' bridge and the
inner gates' at *any* file whose registers stand for elements and whose tuples
are their elements'. The file a clocked program lays
(`DescriptiveComplexity.Draw.Data.blkLaid`) is such a file – a register **is**
a block and a tuple, so its tuple is its element's by `rfl` – and this file says
so: `gateEnc_blkLaid` and `passEnc_blkLaid` are `hgateEnc` and `hpassEnc`
discharged there, which is what a leg of the spine carries as a hypothesis.

The register file the gates' bridge reads the elementwise trichotomy at is
`DescriptiveComplexity.wmSegFile`, the ladder of initial segments: it is a
device of the proof, not of the program, and the order alone builds it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

section BlkBridge

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [Nonempty A]
variable [L.IsRelational] [L.Structure A]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite (Univ A R' P' dt.KIx dt.dd)]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
variable {base : ℕ} (hpos : 0 < base)
variable (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
  Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
    (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [Nonempty A] [L.IsRelational]
  [L.Structure A] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- **The registers of the laid file stand for distinct elements.** -/
theorem blkIxElt_injective :
    Function.Injective (blkIxElt (A := A) (K := dt.KIx) R' P' dt.dd) :=
  fun _ _ hu => blkIxElt_inj (h := hu)

omit [Finite R'] [Finite P'] [L.IsRelational] in
variable {dt} in
/-- **The inner gates' bridge at the laid file**: `hpassEnc`, discharged. A
register's tuple is its element's by construction, which is all this bridge
asks. -/
theorem passEnc_blkLaid (hzo : PR.zero ≠ PR.one)
    (vi : dt.VarIx)
    (stV : TapeSt dt A R' P' (Wide.BlkIx dt.KIx A dt.dd))
    (ℓ : Fin (dt.nIn vi)) :
    dt.ixIGPassP (elt := blkIxElt R' P' dt.dd) (dt.blkLaid h hpos hbase)
        PR.zero PR.one vi stV ℓ ↔
      IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr (blkIxElt R' P' dt.dd) stV.val)
        (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R' P' dt.KIx)) :=
  dt.ixIGPassP_iff_isEnc (F := dt.blkLaid h hpos hbase) blkIxElt_injective
    (isLinOrd_blkLaid_le h hpos hbase) (dt.blk_blkLaid_eq_tagBlk h hpos hbase)
    (fun _ => rfl) hzo vi stV ℓ

omit [Finite R'] [Finite P'] [L.IsRelational] in
variable {dt} in
/-- **The gates' bridge at the laid file**: `hgateEnc`, discharged. -/
theorem gateEnc_blkLaid (hzo : PR.zero ≠ PR.one)
    (j : Fin dt.nv) (st : TapeSt dt A R' P' (Wide.BlkIx dt.KIx A dt.dd)) :
    dt.ixGatedAt (PR := PR) (elt := blkIxElt R' P' dt.dd)
        (F := dt.blkLaid h hpos hbase) j st ↔
      ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        IsEnc dt.ly PR.zero PR.one
          (wmBlk (ixAddr (blkIxElt R' P' dt.dd) st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) : Tag R' P' dt.KIx)) :=
  dt.ixGatedAt_iff_isEnc (F := dt.blkLaid h hpos hbase) blkIxElt_injective
    (isLinOrd_blkLaid_le h hpos hbase) (dt.blk_blkLaid_eq_tagBlk h hpos hbase)
    (wmSegFile h) (fun _ => rfl) hzo h j st

end BlkBridge

end Data

end Draw

end DescriptiveComplexity
