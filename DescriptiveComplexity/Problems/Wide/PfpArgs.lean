/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpAccCtl
import DescriptiveComplexity.Problems.Wide.PfpKindRule
import DescriptiveComplexity.Problems.Wide.PfpProg
import DescriptiveComplexity.Problems.Wide.PfpName
import DescriptiveComplexity.Problems.Wide.PfpExp

/-!
# The semantic parameters, filled in: the comparison atoms

The rule shapes of the program were closed before a single semantic choice
was made, the content riding in parameter packs
(`DescriptiveComplexity.Pfp.StageArgs` and friends). This file begins filling
them, at the kind whose loop is simplest: a **comparison** – an equality or
an order atom between two levels of the prefix.

What the machine does there, and what the packs say (the anchor is
`DescriptiveComplexity.Problems.Wide.PfpCmp`): walk the canonically padded
cells of the two argument blocks in the lexicographic order of their `dd₀`
coordinates, reading **one bit from each block per cell** – which is why
these are element loops and not file tests – and keep three bits of
bookkeeping: whether every cell so far agreed, whether a difference has been
seen, and, at the *first* difference, whether it was the second block that
held the cell. An equality atom's verdict is the first bit; an order atom's
is «agreed throughout, or the first difference went the right way».

Where a level's point lives is fixed here too
(`DescriptiveComplexity.Pfp.PfpData.lvBlk` / `lvTrack`), in the dictionary of
`DescriptiveComplexity.Problems.Wide.PfpLeaf`: the free levels in the outer
blocks of the MIRROR register – the working address – and the quantified ones
in the inner blocks of VAL.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A : Type}

/-! ### Where a level's point lives -/

/-- **The argument block a level's point occupies**: an outer block – of the
working address – below the variable's arity, an inner one – of the VAL
register – above it. -/
noncomputable def lvBlk (v : dt.VarIx) (j : Fin (dt.nOf v)) :
    Fin dt.ko ⊕ Fin dt.ki :=
  if h : (j : ℕ) < dt.arOf v then Sum.inl ⟨(j : ℕ), lt_of_lt_of_le h (dt.arOf_le_ko v)⟩
    else Sum.inr ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki v)⟩

/-- **The register a level's point is read from**: MIRROR for a free level,
VAL for a quantified one. -/
noncomputable def lvTrack (v : dt.VarIx) (j : Fin (dt.nOf v)) : dt.SlotIx :=
  if (j : ℕ) < dt.arOf v then Slot.mir else Slot.val

/-! ### The comparison loops' bookkeeping -/

/-- **Every cell so far agreed.** -/
noncomputable def cmpAccC : dt.CtlIx := dt.scratchC 1

/-- **A difference has been seen.** -/
noncomputable def cmpDecC : dt.CtlIx := dt.scratchC 2

/-- **At the first difference, the second block held the cell.** -/
noncomputable def cmpValC : dt.CtlIx := dt.scratchC 3

/-- The two paired reads of a comparison's round. -/
noncomputable def cmpRdC (hnf : 2 ≤ dt.nfDim) (k : Fin 2) : dt.CtlIx :=
  dt.rdfC (Fin.castLE hnf k)

variable {dt}

theorem cmpAccC_ne_cmpDecC : dt.cmpAccC ≠ dt.cmpDecC :=
  fun h => absurd (congrArg Fin.val (dt.scratchC_injective h)) (by decide)

theorem cmpAccC_ne_cmpValC : dt.cmpAccC ≠ dt.cmpValC :=
  fun h => absurd (congrArg Fin.val (dt.scratchC_injective h)) (by decide)

theorem cmpDecC_ne_cmpValC : dt.cmpDecC ≠ dt.cmpValC :=
  fun h => absurd (congrArg Fin.val (dt.scratchC_injective h)) (by decide)

theorem cmpDecC_ne_cmpAccC : dt.cmpDecC ≠ dt.cmpAccC := cmpAccC_ne_cmpDecC.symm

theorem cmpValC_ne_cmpAccC : dt.cmpValC ≠ dt.cmpAccC := cmpAccC_ne_cmpValC.symm

theorem cmpValC_ne_cmpDecC : dt.cmpValC ≠ dt.cmpDecC := cmpDecC_ne_cmpValC.symm

theorem lvC_ne_cmpAccC (j : Fin dt.dd0) : dt.lvC j ≠ dt.cmpAccC := fun h => nomatch h

theorem lvC_ne_cmpDecC (j : Fin dt.dd0) : dt.lvC j ≠ dt.cmpDecC := fun h => nomatch h

theorem lvC_ne_cmpValC (j : Fin dt.dd0) : dt.lvC j ≠ dt.cmpValC := fun h => nomatch h

theorem cmpRdC_ne_cmpAccC (hnf : 2 ≤ dt.nfDim) (k : Fin 2) :
    dt.cmpRdC hnf k ≠ dt.cmpAccC := fun h => nomatch h

theorem cmpRdC_ne_cmpDecC (hnf : 2 ≤ dt.nfDim) (k : Fin 2) :
    dt.cmpRdC hnf k ≠ dt.cmpDecC := fun h => nomatch h

theorem cmpRdC_ne_cmpValC (hnf : 2 ≤ dt.nfDim) (k : Fin 2) :
    dt.cmpRdC hnf k ≠ dt.cmpValC := fun h => nomatch h

variable (dt) (zero one : A)

/-! ### One round of a comparison -/

/-- **The bookkeeping of one round**: the pair of bits just read is folded
into the three flags – agreement so far, a difference has been seen, and the
verdict at the *first* difference, which is why the last is written only
while none has been seen. -/
noncomputable def cmpFold (hnf : 2 ≤ dt.nfDim) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one dt.cmpAccC
      (dt.ctlBit one f dt.cmpAccC ∧
        (dt.ctlBit one f (dt.cmpRdC hnf 0) ↔ dt.ctlBit one f (dt.cmpRdC hnf 1)))
    (dt.setCtl zero one dt.cmpDecC
      (dt.ctlBit one f dt.cmpDecC ∨
        ¬(dt.ctlBit one f (dt.cmpRdC hnf 0) ↔ dt.ctlBit one f (dt.cmpRdC hnf 1)))
      (dt.setCtl zero one dt.cmpValC
        ((dt.ctlBit one f dt.cmpDecC ∧ dt.ctlBit one f dt.cmpValC) ∨
          (¬dt.ctlBit one f dt.cmpDecC ∧
            ¬dt.ctlBit one f (dt.cmpRdC hnf 0) ∧ dt.ctlBit one f (dt.cmpRdC hnf 1)))
        f))

/-- **What a comparison concludes**: an equality atom holds when every cell
agreed; an order atom when they did, or when the first difference was the
second block's. -/
noncomputable def cmpVerdict (isEq : Bool) (f : dt.CtlIx → A) : Prop :=
  if isEq = true then dt.ctlBit one f dt.cmpAccC
    else (dt.ctlBit one f dt.cmpAccC ∨ dt.ctlBit one f dt.cmpValC)

/-- **The loop's first round starts from agreement**: nothing differs yet, no
difference has been seen, and the tuple is the least. -/
noncomputable def cmpInit (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one dt.cmpAccC True
    (dt.setCtl zero one dt.cmpDecC False
      (dt.setCtl zero one dt.cmpValC False f))

variable {dt zero one}

/-! ### The read-backs a run cites -/

theorem ctlBit_cmpAccC_cmpFold (hzo : zero ≠ one) (hnf : 2 ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.cmpFold zero one hnf f) dt.cmpAccC ↔
      (dt.ctlBit one f dt.cmpAccC ∧
        (dt.ctlBit one f (dt.cmpRdC hnf 0) ↔ dt.ctlBit one f (dt.cmpRdC hnf 1))) := by
  rw [cmpFold, ctlBit_setCtl_self hzo]

theorem ctlBit_cmpDecC_cmpFold (hzo : zero ≠ one) (hnf : 2 ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.cmpFold zero one hnf f) dt.cmpDecC ↔
      (dt.ctlBit one f dt.cmpDecC ∨
        ¬(dt.ctlBit one f (dt.cmpRdC hnf 0) ↔ dt.ctlBit one f (dt.cmpRdC hnf 1))) := by
  rw [cmpFold, ctlBit_setCtl_of_ne cmpDecC_ne_cmpAccC, ctlBit_setCtl_self hzo]

theorem ctlBit_cmpValC_cmpFold (hzo : zero ≠ one) (hnf : 2 ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.cmpFold zero one hnf f) dt.cmpValC ↔
      ((dt.ctlBit one f dt.cmpDecC ∧ dt.ctlBit one f dt.cmpValC) ∨
        (¬dt.ctlBit one f dt.cmpDecC ∧
          ¬dt.ctlBit one f (dt.cmpRdC hnf 0) ∧ dt.ctlBit one f (dt.cmpRdC hnf 1))) := by
  rw [cmpFold, ctlBit_setCtl_of_ne cmpValC_ne_cmpAccC,
    ctlBit_setCtl_of_ne cmpValC_ne_cmpDecC, ctlBit_setCtl_self hzo]

/-- The loop element rides along the bookkeeping, so a round may fold and
advance in one step. -/
theorem readLv_cmpFold (hnf : 2 ≤ dt.nfDim) (f : dt.CtlIx → A) :
    dt.readLv (dt.cmpFold zero one hnf f) = dt.readLv f := by
  funext j
  rw [readLv, readLv, cmpFold, setCtl_of_ne (lvC_ne_cmpAccC (dt := dt) j),
    setCtl_of_ne (lvC_ne_cmpDecC (dt := dt) j),
    setCtl_of_ne (lvC_ne_cmpValC (dt := dt) j)]

theorem ctlBit_cmpAccC_cmpInit (hzo : zero ≠ one) (f : dt.CtlIx → A) :
    dt.ctlBit one (dt.cmpInit zero one f) dt.cmpAccC :=
  (ctlBit_setCtl_self hzo _ _ _).mpr trivial

theorem ctlBit_cmpDecC_cmpInit (hzo : zero ≠ one) (f : dt.CtlIx → A) :
    ¬dt.ctlBit one (dt.cmpInit zero one f) dt.cmpDecC := by
  rw [cmpInit, ctlBit_setCtl_of_ne cmpDecC_ne_cmpAccC, ctlBit_setCtl_self hzo]
  exact id

theorem ctlBit_cmpValC_cmpInit (hzo : zero ≠ one) (f : dt.CtlIx → A) :
    ¬dt.ctlBit one (dt.cmpInit zero one f) dt.cmpValC := by
  rw [cmpInit, ctlBit_setCtl_of_ne cmpValC_ne_cmpAccC,
    ctlBit_setCtl_of_ne cmpValC_ne_cmpDecC, ctlBit_setCtl_self hzo]
  exact id

/-! ### The pack -/

variable (dt zero one)

/-- **The parameters of a comparison atom's loop**: the two paired reads –
one in each level's block, at the padded cell of the control's narrow tuple –
the three bookkeeping flags, and the narrow tuple enumeration. The verdict
lands in the atom's own slot. -/
noncomputable def cmpArgs [LinearOrder A] [Finite A] [Nonempty A]
    (v : dt.VarIx) (a : Fin dt.natMax) (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
    (j₁ j₂ : Fin (dt.nOf v)) : ElemArgs A dt.CtlIx dt.SlotIx 2 where
  rdTrack := fun k => if k = 0 then dt.lvTrack v j₁ else dt.lvTrack v j₂
  MatchOf := fun k =>
    dt.nameG one (if k = 0 then dt.lvBlk v j₁ else dt.lvBlk v j₂) dt.lvC
  setFlag := fun k b f _ => dt.setCtl zero one (dt.cmpRdC hnf k) (b = true) f
  initEl := fun f _ => dt.cmpInit zero one (dt.initLvN f)
  advEl := fun f _ => dt.advLvN (dt.cmpFold zero one hnf f)
  exitSt := fun f _ =>
    dt.setCtl zero one (dt.avC a)
      (dt.cmpVerdict one isEq (dt.cmpFold zero one hnf f))
      (dt.cmpFold zero one hnf f)
  IsMaxEl := dt.IsMaxLvN

/-- **A comparison's exit reads the control alone**: the atom's verdict is
folded out of the flags, not off the tape. -/
theorem cmpArgs_exitSt_congr [LinearOrder A] [Finite A] [Nonempty A]
    (v : dt.VarIx) (a : Fin dt.natMax) (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
    (j₁ j₂ : Fin (dt.nOf v)) (f : dt.CtlIx → A) (g g' : dt.SlotIx → A) :
    (dt.cmpArgs zero one v a hnf isEq j₁ j₂).exitSt f g =
      (dt.cmpArgs zero one v a hnf isEq j₁ j₂).exitSt f g' := rfl

/-! ### The tag witnesses of an expansion atom

An expansion atom must know the **tags** of its argument points before it can
pick the defining sentence to run: it reads, for each argument position and
each tag, whether that tag's witness cell belongs to the position's block
(`DescriptiveComplexity.Pfp.PfpData.blk_encTagTup_iff` – the read is the
point's tag test), and files the answer in a flag. The branch checkpoint then
dispatches on the whole tuple, which the flags decode **one-hot**: that is
what makes its dispatches exclusive, and it is the only hypothesis
`DescriptiveComplexity.Pfp.tagSep` asks for. -/

section Tags

/-- The tag inventory as a `Fintype`, so that positions and tags can be
numbered together. -/
noncomputable instance : Fintype dt.X.Tag := Fintype.ofFinite _

/-- **The flag of one witness read**: argument position `ℓ`, tag `t`. -/
noncomputable def tagIx {k : ℕ} (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (ℓ : Fin k) (t : dt.X.Tag) : dt.CtlIx :=
  dt.tgfC (Fin.castLE hk (finProdFinEquiv (ℓ, (Fintype.equivFin dt.X.Tag) t)))

variable {dt}

theorem tagIx_injective {k : ℕ} (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    {ℓ ℓ' : Fin k} {t t' : dt.X.Tag} (h : dt.tagIx hk ℓ t = dt.tagIx hk ℓ' t') :
    ℓ = ℓ' ∧ t = t' := by
  have h1 := dt.tgfC_injective h
  have h2 : (finProdFinEquiv (ℓ, (Fintype.equivFin dt.X.Tag) t) :
      Fin (k * Fintype.card dt.X.Tag)) =
      finProdFinEquiv (ℓ', (Fintype.equivFin dt.X.Tag) t') :=
    Fin.ext (by simpa using congrArg Fin.val h1)
  have h3 := finProdFinEquiv.injective h2
  exact ⟨(Prod.ext_iff.mp h3).1,
    (Fintype.equivFin dt.X.Tag).injective (Prod.ext_iff.mp h3).2⟩

variable (dt) (zero one : A)

/-- **What the flags say**: the tuple of tags they decode, read as a one-hot
family – position by position, exactly the tag of that position is
flagged. -/
def TagsAre {k : ℕ} (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (τ : Fin k → dt.X.Tag) (f : dt.CtlIx → A) : Prop :=
  ∀ (ℓ : Fin k) (t : dt.X.Tag), dt.ctlBit one f (dt.tagIx hk ℓ t) ↔ t = τ ℓ

/-- **The witness read's guard**: the tag witness cell of the tag `t` in the
block of the level the position reads. Its digit is the point's tag test. -/
noncomputable def tagMatch (v : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf v))
    (ℓ : Fin k) (t : dt.X.Tag) : (dt.CtlIx → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one (dt.lvBlk v (ts ℓ))
    (dt.encCoord zero one (Sum.inl t) fun _ _ => zero)

variable {dt zero one}

/-- **The decoding is exclusive**: a one-hot family determines its tuple, so
the branch checkpoint's dispatches never co-fire. This is the hypothesis
`DescriptiveComplexity.Pfp.tagSep` carries. -/
theorem tagsAre_unique {k : ℕ} (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (τ τ' : Fin k → dt.X.Tag) (f : dt.CtlIx → A)
    (h : dt.TagsAre one hk τ f) (h' : dt.TagsAre one hk τ' f) : τ = τ' :=
  funext fun ℓ => (h' ℓ (τ ℓ)).mp ((h ℓ (τ ℓ)).mpr rfl)

end Tags

/-! ### The read leaves of an expansion atom

A round of an expansion atom's element loop makes one trip per **block atom**
of the defining sentence's matrix: the atom names a copy – which argument
point – a relation variable of that point's block, and the levels its payload
reads. The trip goes to the cell of that member tuple, in the block the copy's
level occupies, and its digit is the assignment bit
(`DescriptiveComplexity.Pfp.PfpData.blk_encAsgTup_self`). -/

section Exp

variable [L.IsRelational]

variable {dt}

/-- **The data of the `r`-th read leaf**: the block atom's variable – a copy
of the block, so an argument position paired with one of the point's
relation variables – and the levels its payload reads. -/
noncomputable def relLeafData {k : ℕ} (e : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ)) :
    (i : (dt.X.B.replicate k).ι) ×
      (Fin ((dt.X.B.replicate k).arity i) → Fin (dt.relPk e τ).n) :=
  let h : isBlkAtom ((blkAtoms (dt.relPk e τ).mat).get r) = true :=
    isBlkAtom_of_mem_blkAtoms (List.get_mem _ _)
  ⟨(exists_blkA_of_isBlkAtom h).choose,
    (exists_blkA_of_isBlkAtom h).choose_spec.choose⟩

/-- **The leaf is that block atom**: what the trip's digit has to mean. -/
theorem blkAtom?_relLeafData {k : ℕ} (e : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ)) :
    blkAtom? ((blkAtoms (dt.relPk e τ).mat).get r) =
      some (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2) :=
  (exists_blkA_of_isBlkAtom
    (isBlkAtom_of_mem_blkAtoms (List.get_mem _ _))).choose_spec.choose_spec

variable (dt)

/-- **The payload a read leaf spells**: the block atom's levels, read out of
the loop's wide tuple and padded to the block's arity bound – which is
exactly the payload of the member tuple
`DescriptiveComplexity.Pfp.encAsgTup`. -/
noncomputable def expPay {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (r : Fin (dt.relNr e τ)) (hn : (dt.relPk e τ).n ≤ dt.eDim)
    (f : dt.CtlIx → A) : Fin (blockArityBound dt.X.B) → A :=
  pad zero fun q : Fin (dt.X.B.arity (relLeafData e τ r).1.2) =>
    f (dt.lvE (Fin.castLE hn ((relLeafData e τ r).2 q)))

/-- **The track a read leaf reads**: the register the copy's level lives
in. -/
noncomputable def expRdTrack {k : ℕ} (v : dt.VarIx) (ts : Fin k → Fin (dt.nOf v))
    (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ)) :
    dt.SlotIx :=
  dt.lvTrack v (ts (relLeafData e τ r).1.1)

/-- **The cell a read leaf goes to**: the member tuple of the copy's point,
in the block that point occupies. -/
noncomputable def expMatch {k : ℕ} (v : dt.VarIx) (ts : Fin k → Fin (dt.nOf v))
    (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ))
    (hn : (dt.relPk e τ).n ≤ dt.eDim) :
    (dt.CtlIx → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one (dt.lvBlk v (ts (relLeafData e τ r).1.1))
    (dt.encCoord zero one (Sum.inr (relLeafData e τ r).1.2)
      (dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn)))

/-- **Where a read leaf files its bit**: the leaf-read flag of its index. -/
noncomputable def expSetFlag {k : ℕ} (e : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ))
    (hrd : dt.relNr e τ ≤ dt.nfDim) (b : Bool) (f : dt.CtlIx → A)
    (_g : dt.SlotIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one (dt.rdfC (Fin.castLE hrd r)) (b = true) f

/-! ### The leaf of a branch, as the control computes it -/

variable [LinearOrder A] [L.Structure A]

/-- **The value of a branch's matrix, from the control alone**: its block
atoms are the leaf-read flags the round has just filed, its base atoms are
guards – equalities, base relations and order comparisons on the loop's own
tuple, which the transition table evaluates where they stand. -/
noncomputable def expLeafVal {k : ℕ} (e : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (hn : (dt.relPk e τ).n ≤ dt.eDim)
    (hrd : dt.relNr e τ ≤ dt.nfDim) (f : dt.CtlIx → A) : Prop :=
  qfValue (dt.relPk e τ).mat fun a =>
    if isBlkAtom a = true then
      (∃ r : Fin (dt.relNr e τ), (blkAtoms (dt.relPk e τ).mat).get r = a ∧
        dt.ctlBit one f (dt.rdfC (Fin.castLE hrd r)))
    else (blkAtom? a).elim False
      (BlkAtom.holds (L := L) (B := dt.X.B.replicate k) (fun _ _ => False)
        fun j => f (dt.lvE (Fin.castLE hn j)))

/-- **What the control computes is the branch's leaf.** Given that every
leaf-read flag holds its block atom's value – which
`DescriptiveComplexity.Pfp.PfpData.regBit_expMatch` is what the trip
delivers – the Boolean function of the flags and the guards is the leaf
predicate `DescriptiveComplexity.Pfp.PfpData.expLeaf` of
`DescriptiveComplexity.Problems.Wide.PfpExp`. -/
theorem expLeafVal_iff {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (hn : (dt.relPk e τ).n ≤ dt.eDim) (hrd : dt.relNr e τ ≤ dt.nfDim)
    (ρs : Fin k → dt.X.B.Assignment A) (f : dt.CtlIx → A)
    (hav : ∀ r : Fin (dt.relNr e τ),
      dt.ctlBit one f (dt.rdfC (Fin.castLE hrd r)) ↔
        BlkAtom.holds (L := L) (B := dt.X.B.replicate k)
          (dt.X.B.replicateAssign ρs) (fun j => f (dt.lvE (Fin.castLE hn j)))
          (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2)) :
    dt.expLeafVal one e τ hn hrd f ↔
      dt.expLeaf e τ ρs fun j => f (dt.lvE (Fin.castLE hn j)) := by
  refine qfValue_congr _ _ _ fun a ha => ?_
  by_cases hb : isBlkAtom a = true
  · rw [if_pos hb]
    have hmem : a ∈ blkAtoms (dt.relPk e τ).mat := List.mem_filter.mpr ⟨ha, hb⟩
    obtain ⟨r, hr⟩ : ∃ r : Fin (dt.relNr e τ),
        (blkAtoms (dt.relPk e τ).mat).get r = a := List.mem_iff_get.mp hmem
    have hkind : blkAtom? a =
        some (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2) :=
      hr ▸ blkAtom?_relLeafData e τ r
    rw [hkind]
    constructor
    · rintro ⟨r', hr', hbit⟩
      have hkind' : blkAtom? a =
          some (.blkA (relLeafData e τ r').1 (relLeafData e τ r').2) :=
        hr' ▸ blkAtom?_relLeafData e τ r'
      have hsame := Option.some.inj (hkind'.symm.trans hkind)
      exact hsame ▸ (hav r').mp hbit
    · intro hh
      exact ⟨r, hr, (hav r).mpr hh⟩
  · rw [if_neg hb]
    obtain ⟨κ, hκ⟩ :=
      Option.isSome_iff_exists.mp (isSome_blkAtom?_of_mem_qfAtoms (dt.relPk e τ).mat a ha)
    rw [hκ]
    match κ with
    | .eqA _ _ => exact Iff.rfl
    | .ordA _ _ => exact Iff.rfl
    | .baseA _ _ => exact Iff.rfl
    | .blkA _ _ => exact absurd (isBlkAtom_of_blkA hκ) hb

/-! ### A branch's loop, wired -/

variable [Finite A] [Nonempty A]

/-- **A branch's loop, started**: the wide tuple at the least, the sub-fold's
accumulators at the polarity's units. -/
noncomputable def expInit {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.initSac zero one (dt.relPk e τ).pol (dt.initLvE f)

/-- **A branch's round, folded and advanced**: the leaf the round just
computed is filed, the accumulators fold at the coordinate the tuple carries
(`DescriptiveComplexity.Pfp.tupCarry`), and the tuple steps. -/
noncomputable def expAdv {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (hn : (dt.relPk e τ).n ≤ dt.eDim) (hrd : dt.relNr e τ ≤ dt.nfDim)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.advLvE
    (dt.carrySac zero one (dt.relPk e τ).pol (tupCarry (dt.readLvE f))
      (dt.setSubLeaf zero one (dt.expLeafVal one e τ hn hrd f) f))

/-- **A branch's last round**: the final leaf is filed and the sub-fold's
verdict lands in the atom's slot. -/
noncomputable def expExit {k : ℕ} (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag)
    (hn : (dt.relPk e τ).n ≤ dt.eDim) (hrd : dt.relNr e τ ≤ dt.nfDim)
    (a : Fin dt.natMax) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one (dt.avC a)
    (dt.sacVerdict one (dt.relPk e τ).pol
      (dt.setSubLeaf zero one (dt.expLeafVal one e τ hn hrd f) f))
    (dt.setSubLeaf zero one (dt.expLeafVal one e τ hn hrd f) f)

/-- **The witness reads of an expansion atom, numbered**: one per argument
position and tag. -/
noncomputable def wIx {k : ℕ} (i : Fin (k * Fintype.card dt.X.Tag)) :
    Fin k × dt.X.Tag :=
  ((finProdFinEquiv.symm i).1, (Fintype.equivFin dt.X.Tag).symm (finProdFinEquiv.symm i).2)

/-- **The parameter pack of an expansion atom's machinery**: the tag
witnesses and their one-hot decoding, then, per branch, the read leaves of
the defining sentence and the sub-fold over its prefix. -/
noncomputable def expArgs {k : ℕ} (v : dt.VarIx) (ts : Fin k → Fin (dt.nOf v))
    (e : dt.X.E.Relations k) (a : Fin dt.natMax)
    (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ τ : Fin k → dt.X.Tag, (dt.relPk e τ).n ≤ dt.eDim)
    (hrd : ∀ τ : Fin k → dt.X.Tag, dt.relNr e τ ≤ dt.nfDim) :
    TagArgs A dt.CtlIx dt.SlotIx (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
      (dt.relNr e) where
  rdTrackT := fun i => dt.lvTrack v (ts (dt.wIx i).1)
  MatchT := fun i => dt.tagMatch zero one v ts (dt.wIx i).1 (dt.wIx i).2
  setTagFlag := fun i b f _ =>
    dt.setCtl zero one (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (b = true) f
  TagsAre := fun τ => dt.TagsAre one hk τ
  hTags := fun τ τ' f h h' => tagsAre_unique hk τ τ' f h h'
  rdTrackE := fun τ r => dt.expRdTrack v ts e τ r
  MatchE := fun τ r => dt.expMatch zero one v ts e τ r (hn τ)
  setFlagE := fun τ r b f g => dt.expSetFlag zero one e τ r (hrd τ) b f g
  initEl := fun τ f _ => dt.expInit zero one e τ f
  advEl := fun τ f _ => dt.expAdv zero one e τ (hn τ) (hrd τ) f
  exitSt := fun τ f _ => dt.expExit zero one e τ (hn τ) (hrd τ) a f
  IsMaxEl := fun _ => dt.IsMaxLvE

/-- **An expansion atom's exit reads the control alone.** -/
theorem expArgs_exitSt_congr {k : ℕ} (v : dt.VarIx)
    (ts : Fin k → Fin (dt.nOf v)) (e : dt.X.E.Relations k) (a : Fin dt.natMax)
    (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ τ : Fin k → dt.X.Tag, (dt.relPk e τ).n ≤ dt.eDim)
    (hrd : ∀ τ : Fin k → dt.X.Tag, dt.relNr e τ ≤ dt.nfDim)
    (τ : Fin k → dt.X.Tag) (f : dt.CtlIx → A) (g g' : dt.SlotIx → A) :
    (dt.expArgs zero one v ts e a hk hn hrd).exitSt τ f g =
      (dt.expArgs zero one v ts e a hk hn hrd).exitSt τ f g' := rfl

variable {dt zero one}

/-! ### The gates

A gate asks of one **outer** block of the working address – held in MIRROR –
that it encode a point: which tag its witness carries, that every member is
well-shaped for that tag, and that the tag's domain sentence hold of the
decoded assignment (`DescriptiveComplexity.Pfp.isEnc_iff_parts`). The last is
the element loop again, at the domain pack, and all of its read leaves go to
the *same* block – the domain sentence is over the un-replicated block, so
every block atom is about the gated point itself. -/

section Gate

variable (dt zero one)

/-- **The tag-witness guard of a block**: the cell of the tag's witness
tuple. -/
noncomputable def tagWitnessMatch (b : Fin dt.ko ⊕ Fin dt.ki) (t : dt.X.Tag) :
    (dt.CtlIx → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one b (dt.encCoord zero one (Sum.inl t) fun _ _ => zero)

/-- **A gate's tag flag**: one per tag of the block it gates. -/
noncomputable def gateTagC (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (t : dt.X.Tag) : dt.CtlIx :=
  dt.tgfC (Fin.castLE hc (Fintype.equivFin dt.X.Tag t))

/-- **What a gate's flags say**: the tag they decode, one-hot. -/
def GateTagsAre (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim) (t : dt.X.Tag)
    (f : dt.CtlIx → A) : Prop :=
  ∀ t' : dt.X.Tag, dt.ctlBit one f (dt.gateTagC hc t') ↔ t' = t

variable {dt zero one}

omit [L.IsRelational] [LinearOrder A] [L.Structure A] [Finite A] [Nonempty A] in
/-- **A gate's decoding is exclusive**, so its branch never co-fires. -/
theorem gateTagsAre_unique (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (t t' : dt.X.Tag) (f : dt.CtlIx → A) (h : dt.GateTagsAre one hc t f)
    (h' : dt.GateTagsAre one hc t' f) : t = t' :=
  (h' t).mp ((h t).mpr rfl)

/-- **The data of the `r`-th read leaf of a domain sentence**: the point's
relation variable and the levels its payload reads – all at the gated block,
since the sentence is over the block itself. -/
noncomputable def domLeafData (t : dt.X.Tag) (r : Fin (dt.domNr t)) :
    (i : dt.X.B.ι) × (Fin (dt.X.B.arity i) → Fin (dt.domPk t).n) :=
  let h : isBlkAtom ((blkAtoms (dt.domPk t).mat).get r) = true :=
    isBlkAtom_of_mem_blkAtoms (List.get_mem _ _)
  ⟨(exists_blkA_of_isBlkAtom h).choose,
    (exists_blkA_of_isBlkAtom h).choose_spec.choose⟩

omit [LinearOrder A] [L.Structure A] [Finite A] [Nonempty A] in
/-- **The leaf is that block atom.** -/
theorem blkAtom?_domLeafData (t : dt.X.Tag) (r : Fin (dt.domNr t)) :
    blkAtom? ((blkAtoms (dt.domPk t).mat).get r) =
      some (.blkA (domLeafData t r).1 (domLeafData t r).2) :=
  (exists_blkA_of_isBlkAtom
    (isBlkAtom_of_mem_blkAtoms (List.get_mem _ _))).choose_spec.choose_spec

variable (dt zero one)

/-- **The payload a domain read leaf spells.** -/
noncomputable def domPay (t : dt.X.Tag) (r : Fin (dt.domNr t))
    (hn : (dt.domPk t).n ≤ dt.eDim) (f : dt.CtlIx → A) :
    Fin (blockArityBound dt.X.B) → A :=
  pad zero fun q : Fin (dt.X.B.arity (domLeafData t r).1) =>
    f (dt.lvE (Fin.castLE hn ((domLeafData t r).2 q)))

/-- **The cell a domain read leaf goes to**: the member tuple of the gated
point, in the block being gated. -/
noncomputable def domMatch (b : Fin dt.ko ⊕ Fin dt.ki) (t : dt.X.Tag)
    (r : Fin (dt.domNr t)) (hn : (dt.domPk t).n ≤ dt.eDim) :
    (dt.CtlIx → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one b
    (dt.encCoord zero one (Sum.inr (domLeafData t r).1)
      (dt.domPay (zero := zero) (t := t) (r := r) (hn := hn)))

/-- **Where a domain read leaf files its bit.** -/
noncomputable def domSetFlag (t : dt.X.Tag) (r : Fin (dt.domNr t))
    (hrd : dt.domNr t ≤ dt.nfDim) (b : Bool) (f : dt.CtlIx → A)
    (_g : dt.SlotIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one (dt.rdfC (Fin.castLE hrd r)) (b = true) f

/-- **The value of a domain sentence's matrix, from the control alone.** -/
noncomputable def domLeafVal (t : dt.X.Tag) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) (f : dt.CtlIx → A) : Prop :=
  qfValue (dt.domPk t).mat fun a =>
    if isBlkAtom a = true then
      (∃ r : Fin (dt.domNr t), (blkAtoms (dt.domPk t).mat).get r = a ∧
        dt.ctlBit one f (dt.rdfC (Fin.castLE hrd r)))
    else (blkAtom? a).elim False
      (BlkAtom.holds (L := L) (B := dt.X.B) (fun _ _ => False)
        fun j => f (dt.lvE (Fin.castLE hn j)))

variable {dt zero one}

omit [Finite A] [Nonempty A] in
/-- **What the control computes is the domain sentence's leaf**, given that
every leaf-read flag holds its block atom's bit. -/
theorem domLeafVal_iff (t : dt.X.Tag) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) (ρ : dt.X.B.Assignment A) (f : dt.CtlIx → A)
    (hav : ∀ r : Fin (dt.domNr t),
      dt.ctlBit one f (dt.rdfC (Fin.castLE hrd r)) ↔
        BlkAtom.holds (L := L) (B := dt.X.B) ρ
          (fun j => f (dt.lvE (Fin.castLE hn j)))
          (.blkA (domLeafData t r).1 (domLeafData t r).2)) :
    dt.domLeafVal one t hn hrd f ↔
      dt.domLeaf t ρ fun j => f (dt.lvE (Fin.castLE hn j)) := by
  refine qfValue_congr _ _ _ fun a ha => ?_
  by_cases hb : isBlkAtom a = true
  · rw [if_pos hb]
    have hmem : a ∈ blkAtoms (dt.domPk t).mat := List.mem_filter.mpr ⟨ha, hb⟩
    obtain ⟨r, hr⟩ : ∃ r : Fin (dt.domNr t),
        (blkAtoms (dt.domPk t).mat).get r = a := List.mem_iff_get.mp hmem
    have hkind : blkAtom? a = some (.blkA (domLeafData t r).1 (domLeafData t r).2) :=
      hr ▸ blkAtom?_domLeafData t r
    rw [hkind]
    constructor
    · rintro ⟨r', hr', hbit⟩
      have hkind' : blkAtom? a =
          some (.blkA (domLeafData t r').1 (domLeafData t r').2) :=
        hr' ▸ blkAtom?_domLeafData t r'
      have hsame := Option.some.inj (hkind'.symm.trans hkind)
      exact hsame ▸ (hav r').mp hbit
    · intro hh
      exact ⟨r, hr, (hav r).mpr hh⟩
  · rw [if_neg hb]
    obtain ⟨κ, hκ⟩ :=
      Option.isSome_iff_exists.mp (isSome_blkAtom?_of_mem_qfAtoms (dt.domPk t).mat a ha)
    rw [hκ]
    match κ with
    | .eqA _ _ => exact Iff.rfl
    | .ordA _ _ => exact Iff.rfl
    | .baseA _ _ => exact Iff.rfl
    | .blkA _ _ => exact absurd (isBlkAtom_of_blkA hκ) hb

variable (dt zero one)

/-- **A gate's domain loop, started.** -/
noncomputable def gateInit (t : dt.X.Tag) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.initSac zero one (dt.domPk t).pol (dt.initLvE f)

/-- **A gate's domain round, folded and advanced.** -/
noncomputable def gateAdv (t : dt.X.Tag) (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.advLvE
    (dt.carrySac zero one (dt.domPk t).pol (tupCarry (dt.readLvE f))
      (dt.setSubLeaf zero one (dt.domLeafVal one t hn hrd f) f))

/-- **The dispatch's default tag**. A gate's branch checkpoint dispatches on
the decoded tag of its block value; where the witness flags are not one-hot —
block values the sweeps and the VAL enumeration produce and no point encodes —
the checkpoint fires into *this* tag's branch instead, and the branch's
conjoining exit reads the non-one-hotness off the surviving witness flags and
clears the flag. Any tag serves.

That last sentence is load-bearing, and is why the tag is chosen from a
**nonemptiness of the tags** rather than from a point: an interpretation names
this tag in a formula, so it must be the same tag at every instance, and by
proof irrelevance a `Classical.ofNonempty` at a `Prop` is (the structure only
witnesses that the tags are inhabited, and which structure witnessed it does
not survive into the value). Choosing a point instead would give a different
tag at a different instance, and no formula could name it. -/
noncomputable def defTag : dt.X.Tag :=
  @Classical.ofNonempty dt.X.Tag ⟨(Classical.ofNonempty (α := dt.X.Map A)).1.1⟩

/-- **What a gate's branch checkpoint dispatches on**: the decoded tag
where the witness flags are one-hot, the default tag where they are not —
so some dispatch always fires, on *every* block value. The exit's
one-hotness conjunct makes the default branch clear the flag, so totality
costs no wrong verdict. Shared by the outer gates (at MIRROR) and the
inner ones (at VAL). -/
def DspTagsAre (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim) (t : dt.X.Tag)
    (f : dt.CtlIx → A) : Prop :=
  dt.GateTagsAre one hc t f ∨
    (t = dt.defTag (A := A) ∧ ∀ t' : dt.X.Tag, ¬dt.GateTagsAre one hc t' f)

variable {dt zero one} in
omit [L.IsRelational] in
/-- **The total dispatch is still exclusive**, so the branch never
co-fires. -/
theorem dspTagsAre_unique (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (t t' : dt.X.Tag) (f : dt.CtlIx → A) (h : dt.DspTagsAre one hc t f)
    (h' : dt.DspTagsAre one hc t' f) : t = t' := by
  rcases h with h | ⟨he, hn⟩ <;> rcases h' with h' | ⟨he', hn'⟩
  · exact gateTagsAre_unique hc t t' f h h'
  · exact absurd h (hn' t)
  · exact absurd h' (hn t')
  · rw [he, he']

open Classical in
/-- **The tag a gate dispatches to**: the unique tag whose witness the
block value holds, where there is one; the default tag otherwise. -/
noncomputable def dspTagOf (S : (Fin dt.dd → A) → Prop) : dt.X.Tag :=
  if h : ∃ t : dt.X.Tag, ∀ t' : dt.X.Tag,
      S (encTagTup dt.ly zero one t') ↔ t' = t then h.choose
  else dt.defTag (A := A)

variable {dt zero one} in
omit [L.IsRelational] in
/-- **At a one-hot block value the dispatch is the decoded tag** — how a
gated address's per-block tag data pins the dispatch. -/
theorem dspTagOf_eq_of_onehot {S : (Fin dt.dd → A) → Prop} {t : dt.X.Tag}
    (hone : ∀ t' : dt.X.Tag,
      S (encTagTup dt.ly zero one t') ↔ t' = t) :
    dt.dspTagOf zero one S = t := by
  classical
  have hex : ∃ t₁ : dt.X.Tag, ∀ t' : dt.X.Tag,
      S (encTagTup dt.ly zero one t') ↔ t' = t₁ := ⟨t, hone⟩
  rw [dspTagOf, dif_pos hex]
  exact (hone hex.choose).mp ((hex.choose_spec hex.choose).mpr rfl)

/-- **A gate's conjoining exit**: the flag keeps its value only if the
block's witness flags are **one-hot at the dispatched tag** — so the
default branch always clears — and the sub-fold of the tag's domain
sentence holds. -/
noncomputable def gateExit (t : dt.X.Tag)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : (dt.domPk t).n ≤ dt.eDim)
    (hrd : dt.domNr t ≤ dt.nfDim) (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one dt.gateFlagC
    (dt.ctlBit one f dt.gateFlagC ∧ dt.GateTagsAre one hc t f ∧
      dt.sacVerdict one (dt.domPk t).pol
        (dt.setSubLeaf zero one (dt.domLeafVal one t hn hrd f) f))
    (dt.setSubLeaf zero one (dt.domLeafVal one t hn hrd f) f)

/-- **The parameter pack of one gate block's domain evaluation**: the tag
witnesses of the block, their one-hot decoding, and per tag the read leaves
of its domain sentence with the sub-fold over its prefix. -/
noncomputable def gateArgs (b : Fin dt.ko ⊕ Fin dt.ki)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ t : dt.X.Tag, (dt.domPk t).n ≤ dt.eDim)
    (hrd : ∀ t : dt.X.Tag, dt.domNr t ≤ dt.nfDim) :
    TagArgs A dt.CtlIx dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr where
  rdTrackT := fun _ => Slot.mir
  MatchT := fun c =>
    dt.tagWitnessMatch zero one b ((Fintype.equivFin dt.X.Tag).symm c)
  setTagFlag := fun c bb f _ =>
    dt.setCtl zero one (dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm c))
      (bb = true) f
  TagsAre := fun t => dt.DspTagsAre one hc t
  hTags := fun t t' f h h' => dspTagsAre_unique hc t t' f h h'
  rdTrackE := fun _ _ => Slot.mir
  MatchE := fun t r => dt.domMatch zero one b t r (hn t)
  setFlagE := fun t r bb f g => dt.domSetFlag zero one t r (hrd t) bb f g
  initEl := fun t f _ => dt.gateInit zero one t f
  advEl := fun t f _ => dt.gateAdv zero one t (hn t) (hrd t) f
  exitSt := fun t f _ => dt.gateExit zero one t hc (hn t) (hrd t) f
  IsMaxEl := fun _ => dt.IsMaxLvE

end Gate

/-! ### The stage atoms

A stage atom is the random access: the argument points' blocks are copied
into the outer blocks of TARGET – one coordinate loop per position, a read
trip and a write trip per padded cell – the working cell is sought to that
address, and the stage track is read under the head. Everything the pack
names is already fixed: where a level's point lives, the narrow tuple
enumeration, and the copied bit's flag. -/

section Stage

variable (dt zero one)

/-- **The parameter pack of a stage atom's machinery**: the source track and
block of each argument position, the outer block of TARGET it is copied to,
the coordinate loop and its copied bit, the stage track read under the head,
and the atom's verdict slot. -/
noncomputable def stageArgs (v : dt.VarIx) (i : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf v)) (a : Fin dt.natMax) :
    StageArgs A dt.CtlIx dt.SlotIx (Fin dt.ko ⊕ Fin dt.ki) dt.dd0
      (dt.d.B.arity i) where
  srcTrack := fun ℓ => dt.lvTrack v (ts ℓ)
  srcBlk := fun ℓ => dt.lvBlk v (ts ℓ)
  dstBlk := fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko (some i)) ℓ)
  coord := dt.lvC
  bitFlag := fun f => dt.ctlBit one f dt.bitFlagC
  setBit := fun b f _ => dt.setCtl zero one dt.bitFlagC (b = true) f
  initLv := fun f _ => dt.initLvN f
  advLv := fun f _ => dt.advLvN f
  IsMaxLv := dt.IsMaxLvN
  oldSlot := Slot.old i
  setAv := fun b f _ => dt.setCtl zero one (dt.avC a) (b = true) f

omit [L.IsRelational] [L.Structure A] in
/-- **A stage atom's verdict store reads the control alone**: what it files
is the bit the random access came back with, and that bit is a hypothesis
of the store, not a read of it. -/
theorem stageArgs_setAv_congr (v : dt.VarIx) (i : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf v)) (a : Fin dt.natMax)
    (b : Bool) (f : dt.CtlIx → A) (g g' : dt.SlotIx → A) :
    (dt.stageArgs zero one v i ts a).setAv b f g =
      (dt.stageArgs zero one v i ts a).setAv b f g' := rfl

end Stage

/-! ### The dispatch: one pack per atom -/

section Dispatch

variable (dt zero one)

/-- **The pack of an atom, by its kind**, with the budgets it needs as
hypotheses about that kind – so the match is on the kind itself and the
stuck `DescriptiveComplexity.Pfp.PfpData.kindOf` never has to be unfolded. -/
noncomputable def kindArgsOf (v : dt.VarIx) (a : Fin dt.natMax) :
    ∀ κ : MatAtom dt.X dt.d.B (dt.nOf v),
      dt.kindArgs κ * @Fintype.card dt.X.Tag (Fintype.ofFinite _) ≤ dt.ntgDim →
      dt.kindDepth κ ≤ dt.eDim → dt.kindReads κ ≤ dt.nfDim →
      dt.KindArgs (A := A) (Q := dt.CtlIx) κ
  | .eq j₁ j₂, _, _, hrd => dt.cmpArgs zero one v a hrd true j₁ j₂
  | .ord j₁ j₂, _, _, hrd => dt.cmpArgs zero one v a hrd false j₁ j₂
  | .stage i ts, _, _, _ => dt.stageArgs zero one v i ts a
  | @MatAtom.exp _ _ _ _ k e ts, hk, hn, hrd =>
    letI := Fintype.ofFinite dt.X.Tag
    dt.expArgs zero one v ts e a hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)

/-- **The pack of the `a`-th atom of a variable's matrix.** -/
noncomputable def atomArgs (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    dt.KindArgs (A := A) (Q := dt.CtlIx) (dt.kindOf v a) :=
  dt.kindArgsOf zero one v (Fin.castLE (dt.natOf_le_natMax v) a) (dt.kindOf v a)
    (dt.kindArgs_mul_card_le_ntgDim v a) (dt.kindDepth_le_eDim v a)
    (dt.kindReads_le_nfDim v a)

end Dispatch

/-! ### The whole pack of a variable -/

section Var

variable (dt zero one)

/-- **The well-shapedness question of a gate**, per cell: a cell of the gated
block whose digit is set must carry a canonically padded element whose name
slots spell an encoded tuple – the witness of some tag, or a member of some
relation variable. With the tag out of the members
(`DescriptiveComplexity.Pfp.PtCode`) this is a question about the cell and
nothing else, which is what a file test can ask. -/
noncomputable def wellShapedG (b : Fin dt.ko ⊕ Fin dt.ki) (g : dt.SlotIx → A) :
    Prop :=
  g (.blk (some b)) = one → g Slot.mir = one →
    (g .pdd = one ∧
      ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
          g (.name j) = encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
        ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A), ∀ j : Fin dt.dd0,
          g (.name j) = encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j)))

/-- **The well-shapedness question of an inner gate**, per cell: the same
question as `DescriptiveComplexity.Pfp.PfpData.wellShapedG` with the digit
read off the VAL register instead of the mirror. -/
noncomputable def wellShapedIG (b : Fin dt.ko ⊕ Fin dt.ki)
    (g : dt.SlotIx → A) : Prop :=
  g (.blk (some b)) = one → g Slot.val = one →
    (g .pdd = one ∧
      ((∃ t : dt.X.Tag, ∀ j : Fin dt.dd0,
          g (.name j) = encTagTup dt.ly zero one t (Fin.castLE dt.dd0Le j)) ∨
        ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A), ∀ j : Fin dt.dd0,
          g (.name j) = encAsgTup dt.ly zero one i w (Fin.castLE dt.dd0Le j)))

/-- **An inner gate's conjoining exit**: as
`DescriptiveComplexity.Pfp.PfpData.gateExit`, into the given flag — the
level's polarity chooses which of the round's two flags — with one
conjunct more: the witness flags must be **one-hot at the dispatched
tag**. On the genuine branch the conjunct is what the dispatch already
knew; on the default branch it is false, so the flag is cleared — which is
the right verdict, a block value with no one-hot witness encoding no
point. -/
noncomputable def igateExit (flag : dt.CtlIx) (t : dt.X.Tag)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : (dt.domPk t).n ≤ dt.eDim) (hrd : dt.domNr t ≤ dt.nfDim)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  dt.setCtl zero one flag
    (dt.ctlBit one f flag ∧ dt.GateTagsAre one hc t f ∧
      dt.sacVerdict one (dt.domPk t).pol
        (dt.setSubLeaf zero one (dt.domLeafVal one t hn hrd f) f))
    (dt.setSubLeaf zero one (dt.domLeafVal one t hn hrd f) f)

/-- **The parameter pack of one inner gate block**: the outer gates' pack
with the read tracks on VAL and the verdict conjoined into the level's
polarity flag. -/
noncomputable def igateArgs (b : Fin dt.ko ⊕ Fin dt.ki) (flag : dt.CtlIx)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ t : dt.X.Tag, (dt.domPk t).n ≤ dt.eDim)
    (hrd : ∀ t : dt.X.Tag, dt.domNr t ≤ dt.nfDim) :
    TagArgs A dt.CtlIx dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr where
  rdTrackT := fun _ => Slot.val
  MatchT := fun c =>
    dt.tagWitnessMatch zero one b ((Fintype.equivFin dt.X.Tag).symm c)
  setTagFlag := fun c bb f _ =>
    dt.setCtl zero one (dt.gateTagC hc ((Fintype.equivFin dt.X.Tag).symm c))
      (bb = true) f
  TagsAre := fun t => dt.DspTagsAre one hc t
  hTags := fun t t' f h h' => dspTagsAre_unique hc t t' f h h'
  rdTrackE := fun _ _ => Slot.val
  MatchE := fun t r => dt.domMatch zero one b t r (hn t)
  setFlagE := fun t r bb f g => dt.domSetFlag zero one t r (hrd t) bb f g
  initEl := fun t f _ => dt.gateInit zero one t f
  advEl := fun t f _ => dt.gateAdv zero one t (hn t) (hrd t) f
  exitSt := fun t f _ => dt.igateExit zero one flag t hc (hn t) (hrd t) f
  IsMaxEl := fun _ => dt.IsMaxLvE

/-- **The semantic pack of one variable's machinery**, assembled: the atoms'
packs by kind, the gates' per block, the fold updates in the control, and the
stage slot the variable writes – the output's being the marker itself, which
a true verdict rewrites with the value already there and a false one erases
just as the machine halts. -/
noncomputable def varArgsOf (v : dt.VarIx) : dt.VarArgs (A := A) (Q := dt.CtlIx) v where
  argsA := fun a => dt.atomArgs zero one v a
  enterAtomSt := fun _ f _ => f
  argsG := fun ℓ =>
    dt.gateArgs zero one (Sum.inl (Fin.castLE (dt.arOf_le_ko v) ℓ)) dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
  wellGOf := fun ℓ =>
    dt.wellShapedG zero one (Sum.inl (Fin.castLE (dt.arOf_le_ko v) ℓ))
  setFail := fun f _ => dt.setCtl zero one dt.gateFlagC False f
  enterBlockSt := fun _ f _ => f
  argsIG := fun ℓ =>
    dt.igateArgs zero one
      (Sum.inr ⟨dt.arOf v + (ℓ : ℕ), by
        have h1 := ℓ.isLt
        have h2 := dt.nOf_le_ki v
        have h3 := dt.arOf_le_nOf v
        simp only [nIn] at h1
        omega⟩)
      (if dt.polOf v (dt.arOf v + (ℓ : ℕ)) then dt.existGateC
        else dt.allGateC)
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup (f := fun t' : dt.X.Tag =>
        (dt.domPk t').n) (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
  wellIGOf := fun ℓ =>
    dt.wellShapedIG zero one
      (Sum.inr ⟨dt.arOf v + (ℓ : ℕ), by
        have h1 := ℓ.isLt
        have h2 := dt.nOf_le_ki v
        have h3 := dt.arOf_le_nOf v
        simp only [nIn] at h1
        omega⟩)
  setFailIGOf := fun ℓ f _ =>
    dt.setCtl zero one
      (if dt.polOf v (dt.arOf v + (ℓ : ℕ)) then dt.existGateC
        else dt.allGateC) False f
  enterIGSt := fun ℓ f _ =>
    if (ℓ : ℕ) = 0 then
      dt.setCtl zero one dt.existGateC True
        (dt.setCtl zero one dt.allGateC True f)
    else f
  existFlag := dt.existGateC
  allFlag := dt.allGateC
  newSlot := match v with
    | some i => Slot.new i
    | none => Slot.wk
  gateFlag := dt.gateFlagC
  accBit := fun f => dt.accVerdict one (dt.polOf v) f
  enterSt := fun f _ => dt.setCtl zero one dt.gateFlagC True f
  initSt := fun f _ =>
    dt.setCtl zero one dt.existGateC True
      (dt.setCtl zero one dt.allGateC True
        (dt.initAcc zero one (dt.polOf v) f))
  postFold := fun f _ => dt.setLeaf zero one
    (dt.ctlBit one f dt.existGateC ∧
      (dt.ctlBit one f dt.allGateC → dt.postLeaf one v f)) f
  storeCarry := fun b f _ =>
    dt.carryAcc zero one (dt.polOf v)
      (match b with
        | some (Sum.inr j) => (j : ℕ)
        | _ => 0) f

end Var

/-! ### What a read leaf finds -/

section LeafRead

variable {R' P' : Type} [LinearOrder R'] [LinearOrder P']
variable [Finite R'] [Finite P'] [Finite dt.KIx]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

omit [LinearOrder R'] [LinearOrder P'] [Nonempty A] in
/-- **A read leaf's digit is the block atom's value.** At a block holding the
encoding of the copy's point, the bit the trip finds at the member tuple is
exactly what
`DescriptiveComplexity.Pfp.BlkAtom.holds` says of the atom, at the valuation
the loop's wide tuple spells. This is the join between
`DescriptiveComplexity.Problems.Wide.PfpExp`'s leaf predicate and the
machine. -/
theorem regBit_expMatch (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {k : ℕ} {v : dt.VarIx} (ts : Fin k → Fin (dt.nOf v))
    (e : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e τ))
    (hn : (dt.relPk e τ).n ≤ dt.eDim) (points : Fin k → dt.X.Map A)
    {m : Univ A R' P' dt.KIx dt.dd → Prop}
    (hp : wmBlk m (PfpTag.arg (toLex (dt.lvBlk v (ts (relLeafData e τ r).1.1))) :
        PfpTag R' P' dt.KIx) =
      encMap dt.ly zero one (points (relLeafData e τ r).1.1))
    (f : dt.CtlIx → A) :
    regBit m (wmSeg (dt.blkElt (dt.lvBlk v (ts (relLeafData e τ r).1.1))
        (encTup dt.ly zero one (Sum.inr (relLeafData e τ r).1.2)
          (dt.expPay (zero := zero) (e := e) (τ := τ) (r := r) (hn := hn) f)))) ↔
      BlkAtom.holds (L := L) (B := dt.X.B.replicate k)
        (dt.X.B.replicateAssign fun ℓ => (points ℓ).1.2)
        (fun j => f (dt.lvE (Fin.castLE hn j)))
        (.blkA (relLeafData e τ r).1 (relLeafData e τ r).2) := by
  exact dt.blk_encAsgTup_iff hzo hlin hp (relLeafData e τ r).1.2
    (fun q => f (dt.lvE (Fin.castLE hn ((relLeafData e τ r).2 q))))

end LeafRead

end Exp

end PfpData

end Pfp

end DescriptiveComplexity
