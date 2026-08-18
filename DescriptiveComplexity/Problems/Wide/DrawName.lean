/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawBack
import DescriptiveComplexity.Problems.Wide.DrawGate

/-!
# The cell of an encoded tuple: what one leaf read reads

Every atom subroutine of the EXPSPACE program bottoms out in the same
operation: *ask one membership question of the block value held in an
argument block of a register*. The machine asks it by scanning to a cell –
the register cell of the element whose tag is that block and whose
coordinates spell the tuple – and reading the register's track there. This
file is the joint between the two descriptions:

* `DescriptiveComplexity.Draw.Data.blkElt` – the element an encoded tuple
  is, in a given argument block, and `encCoord` – its coordinates, computed
  from the control's slots (the `cf` of
  `DescriptiveComplexity.Draw.Data.nameGF`);
* `DescriptiveComplexity.Draw.Data.encG_iff` – the leaf read's guard holds
  at **exactly** that cell, which is what a navigation-by-name scan needs of
  its stopping condition, and what makes the trip's arrival known;
* `DescriptiveComplexity.Draw.Data.blk_encAsgTup_iff` and
  `blk_encTagTup_iff` – the digit found there: at a block holding the
  encoding of a point, a member tuple's question is **one bit of the point's
  assignment** – with no tag to match, the member codes carrying none – and a
  tag witness's question is the point's **tag test**
  (`DescriptiveComplexity.Draw.mem_encPt_asg`, `mem_encPt_tag`).

What makes the scans stop at the encodings' cells at all is that an encoded
tuple is *canonically padded* (`encTup_isPad`): the layout inhabits the first
`dd₀` coordinates only, which is the budget
`DescriptiveComplexity.Draw.Data.lyLt` fixes.

The same padding is what carries all of this to a **coarse** file, where a
register is not an element: `DescriptiveComplexity.Draw.Data.ixEncG_iff` says
the read stops at the register the layout names by the encoded tuple's
coordinates, and `elt_reg_encCoord` says that register's address is the cell the
elementwise read would have gone to.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

/-! ### The element an encoded tuple is -/

/-- **The cell of a tuple in an argument block**: the block's tag with the
tuple as its coordinates. Reading a register's track at this cell is asking
whether the tuple belongs to the block value the register holds. -/
def blkElt (b : Fin dt.ko ⊕ Fin dt.ki) (v : Fin dt.dd → A) :
    Univ A R' P' dt.KIx dt.dd :=
  (Tag.arg (toLex b), v)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
@[simp]
theorem tagBlk_blkElt (b : Fin dt.ko ⊕ Fin dt.ki) (v : Fin dt.dd → A) :
    tagBlk (dt.blkElt (R' := R') (P' := P') b v).1 = some b := rfl

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
@[simp]
theorem blkElt_coord (b : Fin dt.ko ⊕ Fin dt.ki) (v : Fin dt.dd → A)
    (j : Fin dt.dd) : (dt.blkElt (R' := R') (P' := P') b v).2 j = v j := rfl

/-! ### The coordinates of an encoded tuple -/

variable (zero one : A)

/-- **The coordinates a leaf read compares against**: the encoded tuple of a
fixed discrete datum over a payload the control supplies, cut down to the
name slots' width. -/
noncomputable def encCoord {Q : Type} (c : PtCode dt.X)
    (pay : (Q → A) → Fin (blockArityBound dt.X.B) → A) (fc : Q → A)
    (j : Fin dt.dd0) : A :=
  encTup dt.ly zero one c (pay fc) (Fin.castLE dt.dd0Le j)

variable {dt zero one}

omit [LinearOrder A] in
/-- **An encoded tuple is canonically padded.** The layout puts its code and
payload coordinates among the first `dd₀`, so beyond them the tuple carries
the designated `zero`: encoded tuples live in the cells the marks name, which
is what lets the machine scan to them. -/
theorem encTup_isPad (c : PtCode dt.X) (pay : Fin (blockArityBound dt.X.B) → A)
    (j : Fin dt.dd) (hj : dt.dd0 ≤ (j : ℕ)) :
    encTup dt.ly zero one c pay j = zero :=
  encTup_of_ne c pay
    (fun q hq => absurd (dt.lyLt j (Or.inl ⟨q, hq⟩)) (Nat.not_lt.mpr hj))
    (fun p hp => absurd (dt.lyLt j (Or.inr ⟨p, hp⟩)) (Nat.not_lt.mpr hj))

section Enc

variable [L.Structure A]

/-- **An encoding's members are canonically padded**, so a block value that
encodes a point is decided by the questions the machine can ask: the cells it
can scan to are exactly the padded ones. -/
theorem isPad_of_encMap {p : dt.X.Map A} {v : Fin dt.dd → A}
    (h : encMap dt.ly zero one p v) (j : Fin dt.dd) (hj : dt.dd0 ≤ (j : ℕ)) :
    v j = zero := by
  rcases h with h | ⟨i, w, -, h⟩
  · rw [h]
    exact encTup_isPad _ _ j hj
  · rw [h]
    exact encTup_isPad _ _ j hj

end Enc

/-! ### The cell the guard identifies -/

section Guard

variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable {st : TapeStD dt A R' P'}
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A leaf read stops at exactly the encoded tuple's cell.** The guard of
the trip – the block one-hot, the padding mark and the name slots against the
coordinates the control computes – holds at a register cell precisely when
that cell is the cell of the encoded tuple. -/
theorem encG_iff (hzo : zero ≠ one)
    {cell : Univ A R' P' dt.KIx dt.dd → (Univ A R' P' dt.KIx dt.dd → Prop)}
    (hinj : Function.Injective cell)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (c : PtCode dt.X)
    (pay : (Q → A) → Fin (blockArityBound dt.X.B) → A) (fc : Q → A)
    (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameGF one b (dt.encCoord zero one c pay) fc
        (dt.back cell zero one dt.dd0Le st (cell u)) ↔
      u = dt.blkElt b (encTup dt.ly zero one c (pay fc)) := by
  rw [dt.nameGF_cell hzo hinj]
  constructor
  · rintro ⟨hb, hp, hn⟩
    refine eq_of_slotMark_name (hdd := dt.dd0Le) (hb.trans (dt.tagBlk_blkElt b _).symm)
      hb (fun j => hn j) hp (fun j hj => encTup_isPad c (pay fc) j hj)
  · rintro rfl
    exact ⟨dt.tagBlk_blkElt b _, fun j hj => encTup_isPad c (pay fc) j hj,
      fun _ => rfl⟩

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A coordinate-loop trip stops at exactly the padded cell of the tuple
the control holds.** The comparison and copy loops enumerate tuples of `dd₀`
coordinates and visit the canonically padded cell of each, in whichever block
they are reading. -/
theorem nameG_iff (hzo : zero ≠ one)
    {cell : Univ A R' P' dt.KIx dt.dd → (Univ A R' P' dt.KIx dt.dd → Prop)}
    (hinj : Function.Injective cell)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q) (fc : Q → A)
    (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameG one b coord fc (dt.back cell zero one dt.dd0Le st (cell u)) ↔
      u = dt.blkElt b (pad zero fun j => fc (coord j)) := by
  rw [dt.nameG_cell hzo hinj]
  constructor
  · rintro ⟨hb, hp, hn⟩
    refine eq_of_slotMark_name (hdd := dt.dd0Le)
      (hb.trans (dt.tagBlk_blkElt b _).symm) hb (fun j => ?_) hp (fun j hj => ?_)
    · rw [hn j, dt.blkElt_coord]
      exact (pad_of_lt (c := dt.dd0) (zero := zero) (w := fun j' => fc (coord j'))
        (Fin.castLE dt.dd0Le j) j.isLt).symm
    · rw [dt.blkElt_coord]
      exact pad_of_ge j hj
  · rintro rfl
    refine ⟨dt.tagBlk_blkElt b _, fun j hj => ?_, fun j => ?_⟩
    · rw [dt.blkElt_coord]
      exact pad_of_ge j hj
    · rw [dt.blkElt_coord]
      exact pad_of_lt (c := dt.dd0) (zero := zero) (w := fun j' => fc (coord j'))
        (Fin.castLE dt.dd0Le j) j.isLt

end Guard

/-! ### The register an encoded tuple is, at an arbitrary file -/

section IxEnc

variable {I : Type} {lay : Layout dt A R' P' I} {stI : TapeSt dt A R' P' I}
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A leaf read at a coarse file stops at exactly one register**: the one the
layout names by the encoded tuple's coordinates. The elementwise
`DescriptiveComplexity.Draw.Data.encG_iff` read at a file whose registers are
not elements – the trips of an expansion atom ask which register they stopped
at, and the answer is a name the layout knows. -/
theorem ixEncG_iff (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    (hsep : lay.NameSep zero dt.dd0Le) (hhas : lay.HasName zero)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (c : PtCode dt.X)
    (pay : (Q → A) → Fin (blockArityBound dt.X.B) → A) (fc : Q → A) (u : I) :
    dt.nameGF one b (dt.encCoord zero one c pay) fc
        (dt.ixBack lay zero one dt.dd0Le stI (lay.cell u)) ↔
      u = lay.reg hhas b (dt.encCoord zero one c pay fc) :=
  dt.ixNameGF_iff hzo hinj hsep hhas b _ fc u

omit [LinearOrder A] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The coordinates of an encoded tuple are the tuple, cut down**: what the
control computes for a leaf read is the payload the layout stores, so padding it
back gives the encoded tuple itself. -/
theorem pad_encCoord {Q : Type} (c : PtCode dt.X)
    (pay : (Q → A) → Fin (blockArityBound dt.X.B) → A) (fc : Q → A) :
    pad zero (dt.encCoord zero one c pay fc) = encTup dt.ly zero one c (pay fc) :=
  pad_unpad dt.dd0Le fun j hj => encTup_isPad c (pay fc) j hj

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The register a leaf read names holds the encoded tuple**: with the file's
names coherent with the encoding, the address of that register is the
elementwise cell the same read would have gone to. This is the one place the
coarse file and the encoding have to agree, and
`DescriptiveComplexity.Draw.Data.pad_encCoord` is why they do. -/
theorem elt_reg_encCoord {elt : I → Univ A R' P' dt.KIx dt.dd} (hhas : lay.HasName zero)
    (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (w : Fin dt.dd0 → A),
      elt (lay.reg hhas b w) = dt.blkElt b (pad zero w))
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (c : PtCode dt.X)
    (pay : (Q → A) → Fin (blockArityBound dt.X.B) → A) (fc : Q → A) :
    elt (lay.reg hhas b (dt.encCoord zero one c pay fc)) =
      dt.blkElt b (encTup dt.ly zero one c (pay fc)) := by
  rw [helt, dt.pad_encCoord c pay fc]

end IxEnc

/-! ### What the trip finds there -/

section Read

variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] in
/-- **A register's digit at the cell of a tuple is the block value's
membership question**: the track holds a bit per element, and the elements of
one argument block are that block's tuples. -/
theorem regBit_blkElt (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (m : Univ A R' P' dt.KIx dt.dd → Prop) (b : Fin dt.ko ⊕ Fin dt.ki)
    (v : Fin dt.dd → A) :
    regBit m (wmSeg (dt.blkElt b v)) ↔
      wmBlk m (Tag.arg (toLex b) : Tag R' P' dt.KIx) v :=
  regBit_wmSeg hlin m _

variable [L.Structure A]

omit [LinearOrder R'] [LinearOrder P'] in
/-- **One leaf read is one bit of the assignment**: at a block holding the
encoding of a point, the register's digit at a member tuple's cell says that
the point carries the tuple's tag and its assignment holds of the payload.
This is `DescriptiveComplexity.Draw.mem_encPt_asg` with the machine's cell in
place of the membership question. -/
theorem blk_encAsgTup_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {m : Univ A R' P' dt.KIx dt.dd → Prop} {b : Fin dt.ko ⊕ Fin dt.ki}
    {p : dt.X.Map A}
    (hp : wmBlk m (Tag.arg (toLex b) : Tag R' P' dt.KIx) =
      encMap dt.ly zero one p)
    (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A) :
    regBit m (wmSeg (dt.blkElt b (encAsgTup dt.ly zero one i w))) ↔ p.1.2 i w := by
  rw [dt.regBit_blkElt hlin, hp]
  exact mem_encPt_asg dt.ly hzo p.1 i w

omit [LinearOrder R'] [LinearOrder P'] in
/-- **A tag witness's question is the point's tag test.** -/
theorem blk_encTagTup_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {m : Univ A R' P' dt.KIx dt.dd → Prop} {b : Fin dt.ko ⊕ Fin dt.ki}
    {p : dt.X.Map A}
    (hp : wmBlk m (Tag.arg (toLex b) : Tag R' P' dt.KIx) =
      encMap dt.ly zero one p)
    (t : dt.X.Tag) :
    regBit m (wmSeg (dt.blkElt b (encTagTup dt.ly zero one t))) ↔ p.1.1 = t := by
  rw [dt.regBit_blkElt hlin, hp]
  exact mem_encPt_tag dt.ly hzo p.1 t

end Read

end Data

end Draw

end DescriptiveComplexity
