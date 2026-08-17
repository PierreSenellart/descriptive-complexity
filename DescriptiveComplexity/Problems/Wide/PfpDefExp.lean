/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpDefGate

/-!
# An expansion atom's pack

An expansion atom runs the same machinery a gate does, one exponent along: it
reads the **tags** of its argument points, branches on the tuple they decode,
and folds the defining sentence of that branch. So every piece it needs is one
already discharged for the gates, at the branch's prefix rather than the
domain's — the naming guards through `DescriptiveComplexity.Pfp.PfpData.encCoord`,
the leaf from the control, and the three shapes of a fold.

With them, `DescriptiveComplexity.Pfp.UTagArgsDef` of
`DescriptiveComplexity.Pfp.PfpData.expArgs` is a field-by-field check.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational] {dt : PfpData L}
variable [Fintype dt.SlotIx]

/-! ### What a branch reads -/

omit [L.IsRelational] in
/-- **A witness read's name is definable**: the tag's encoded tuple in the
block of the level the position reads. -/
theorem uGDefinable_tagMatch (v : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf v))
    (ℓ : Fin k) (t : dt.X.Tag) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
      dt.tagMatch e.zero e.one v ts ℓ t f g :=
  uGDefinable_nameGF_of_readable fun j =>
    uReadable_encCoord (Sum.inl t) (fun _ => uReadable_zero) j

omit [L.IsRelational] in
/-- **A branch's decoding is definable**: one-hotness of the witness flags, at
every argument position. -/
theorem uGDefinable_TagsAre {k : ℕ}
    (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim) (τ : Fin k → dt.X.Tag) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.TagsAre e.one hk τ f :=
  (uGDefinable_forall fun ℓ : Fin k =>
    uGDefinable_forall fun t : dt.X.Tag =>
      (uGDefinable_ctlBit (dt.tagIx hk ℓ t)).iff
        (uGDefinable_const (t = τ ℓ))).congr fun _ _ _ => Iff.rfl

/-- **A read leaf's name is definable**: the member tuple of the copy's point,
its payload the loop element at the levels the leaf's atom reads. -/
theorem uGDefinable_expMatch (v : dt.VarIx) {k : ℕ} (ts : Fin k → Fin (dt.nOf v))
    (e' : dt.X.E.Relations k) (τ : Fin k → dt.X.Tag) (r : Fin (dt.relNr e' τ))
    (hn : (dt.relPk e' τ).n ≤ dt.eDim) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f g =>
      dt.expMatch e.zero e.one v ts e' τ r hn f g :=
  uGDefinable_nameGF_of_readable fun j =>
    uReadable_encCoord (Sum.inr (relLeafData e' τ r).1.2)
      (fun p => uReadable_pad_ctl
        (q := fun i => dt.lvE (Fin.castLE hn ((relLeafData e' τ r).2 i))) p) j

open Classical in
/-- **The value of a branch's matrix from the control is definable**, exactly
as a domain sentence's is. -/
theorem uGDefinable_expLeafVal {k : ℕ} (e' : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (hn : (dt.relPk e' τ).n ≤ dt.eDim)
    (hrd : dt.relNr e' τ ≤ dt.nfDim) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx) fun e f _ =>
      dt.expLeafVal e.one e' τ hn hrd f := by
  refine uGDefinable_qfValue (dt.relPk e' τ).mat _ fun a => ?_
  refine UGDefinable.ite (p := isBlkAtom a = true) ?_ ?_
  · exact uGDefinable_exists fun r : Fin (dt.relNr e' τ) =>
      (uGDefinable_const ((blkAtoms (dt.relPk e' τ).mat).get r = a)).and
        (uGDefinable_ctlBit (dt.rdfC (Fin.castLE hrd r)))
  · match hb : blkAtom? a with
    | none =>
      exact (uGDefinable_false (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
        fun _ _ _ => Iff.rfl
    | some κ =>
      exact (uGDefinable_blkAtomHolds (fun j => dt.lvE (Fin.castLE hn j)) κ).congr
        fun _ _ _ => Iff.rfl

/-! ### A branch's three folds -/

omit [L.IsRelational] in
/-- **A branch's loop, started.** -/
theorem uStDefinable_expInit {k : ℕ} (e' : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.expInit e.zero e.one e' τ f :=
  uStDefinable_initSac_initLvE (dt.relPk e' τ).pol

/-- **A branch's round, folded and advanced.** -/
theorem uStDefinable_expAdv {k : ℕ} (e' : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (hn : (dt.relPk e' τ).n ≤ dt.eDim)
    (hrd : dt.relNr e' τ ≤ dt.nfDim) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.expAdv e.zero e.one e' τ hn hrd f :=
  uStDefinable_advSac (dt.relPk e' τ).pol (uGDefinable_expLeafVal e' τ hn hrd)

/-- **A branch's last round**: the final leaf filed and the sub-fold's verdict
into the atom's slot. -/
theorem uStDefinable_expExit {k : ℕ} (e' : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) (hn : (dt.relPk e' τ).n ≤ dt.eDim)
    (hrd : dt.relNr e' τ ≤ dt.nfDim) (a : Fin dt.natMax) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.expExit e.zero e.one e' τ hn hrd a f :=
  uStDefinable_setCtl_setSubLeaf (dt.avC a) (uGDefinable_expLeafVal e' τ hn hrd)
    (uGDefinable_sacVerdict_setSubLeaf (dt.relPk e' τ).pol
      (uGDefinable_expLeafVal e' τ hn hrd))

/-! ### The pack -/

/-- **An expansion atom's pack meets its obligation**, field by field. -/
theorem uTagArgsDef_expArgs {k : ℕ} (v : dt.VarIx) (ts : Fin k → Fin (dt.nOf v))
    (e' : dt.X.E.Relations k) (a : Fin dt.natMax)
    (hk : k * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ τ : Fin k → dt.X.Tag, (dt.relPk e' τ).n ≤ dt.eDim)
    (hrd : ∀ τ : Fin k → dt.X.Tag, dt.relNr e' τ ≤ dt.nfDim) :
    UTagArgsDef (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e : Env L => dt.expArgs e.zero e.one v ts e' a hk hn hrd where
  rdTrackT := ⟨_, fun _ => rfl⟩
  MatchT i := uGDefinable_tagMatch v ts (dt.wIx i).1 (dt.wIx i).2
  setTagFlag _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  TagsAre τ := uGDefinable_TagsAre hk τ
  rdTrackE := ⟨_, fun _ => rfl⟩
  MatchE τ r := uGDefinable_expMatch v ts e' τ r (hn τ)
  setFlagE _ _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  initEl τ := uStDefinable_expInit e' τ
  advEl τ := uStDefinable_expAdv e' τ (hn τ) (hrd τ)
  exitSt τ := uStDefinable_expExit e' τ (hn τ) (hrd τ) a
  IsMaxEl _ := uGDefinable_isMaxLvE

/-! ### A comparison's pack

The equality and order atoms of a matrix compare two *points*, and the machine
does it by walking their two registers in step. What it keeps between rounds is
three scratch flags — agreement so far, a difference seen, and its direction —
so its folds are nested single-slot writes over the narrow loop element. -/

open Classical in
omit [L.IsRelational] in
/-- **A narrow loop-element write over a definable base.** -/
theorem uStDefinable_putLv_comp
    {w : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Fin dt.dd0 → e.α}
    (hw : ∀ j : Fin dt.dd0, USlotDefinable fun e f g => w e f g j)
    {F : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → dt.CtlIx → e.α}
    (hF : UStDefinable F) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.putLv (F e f g) (w e f g) := by
  intro q
  by_cases hq : ∃ j : Fin dt.dd0, q = dt.lvC j
  · obtain ⟨j, rfl⟩ := hq
    refine (hw j).congr fun e f g => ?_
    exact congrFun (dt.readLv_putLv (F e f g) (w e f g)) j
  · refine (hF q).congr fun _ _ _ => ?_
    exact putLv_of_not_lv fun j hc => hq ⟨j, hc⟩

omit [L.IsRelational] in
/-- **A comparison's bookkeeping, folded**: three scratch flags, each written
from a question about the round's two reads. -/
theorem uStDefinable_cmpFold (hnf : 2 ≤ dt.nfDim) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.cmpFold e.zero e.one hnf f :=
  have hrd0 := uGDefinable_ctlBit (L := L) (dt := dt) (dt.cmpRdC hnf 0)
  have hrd1 := uGDefinable_ctlBit (L := L) (dt := dt) (dt.cmpRdC hnf 1)
  (((uStDefinable_id (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).update dt.cmpValC
    (uSlotDefinable_bitVal
      (((uGDefinable_ctlBit dt.cmpDecC).and (uGDefinable_ctlBit dt.cmpValC)).or
        ((uGDefinable_ctlBit dt.cmpDecC).not.and (hrd0.not.and hrd1))))).update
    dt.cmpDecC
    (uSlotDefinable_bitVal
      ((uGDefinable_ctlBit dt.cmpDecC).or (hrd0.iff hrd1).not))).update dt.cmpAccC
    (uSlotDefinable_bitVal
      ((uGDefinable_ctlBit dt.cmpAccC).and (hrd0.iff hrd1)))

omit [L.IsRelational] in
/-- **A comparison's bookkeeping, started.** -/
theorem uStDefinable_cmpInit_initLvN :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.cmpInit e.zero e.one (dt.initLvN f) :=
  (((uStDefinable_initLvN (L := L)).update dt.cmpValC
    (uSlotDefinable_bitVal (uGDefinable_const False))).update dt.cmpDecC
    (uSlotDefinable_bitVal (uGDefinable_const False))).update dt.cmpAccC
    (uSlotDefinable_bitVal (uGDefinable_const True))

omit [L.IsRelational] in
/-- **A comparison's verdict, read off the folded flags.** -/
theorem uGDefinable_cmpVerdict_cmpFold (hnf : 2 ≤ dt.nfDim) (isEq : Bool) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.cmpVerdict e.one isEq (dt.cmpFold e.zero e.one hnf f) := by
  have hrd0 := uGDefinable_ctlBit (L := L) (dt := dt) (dt.cmpRdC hnf 0)
  have hrd1 := uGDefinable_ctlBit (L := L) (dt := dt) (dt.cmpRdC hnf 1)
  have hacc : UGDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) _ =>
        dt.ctlBit e.one (dt.cmpFold e.zero e.one hnf f) dt.cmpAccC :=
    ((uGDefinable_ctlBit dt.cmpAccC).and (hrd0.iff hrd1)).congr fun e f g =>
      ctlBit_cmpAccC_cmpFold e.hzo hnf f
  have hval : UGDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) _ =>
        dt.ctlBit e.one (dt.cmpFold e.zero e.one hnf f) dt.cmpValC :=
    (((uGDefinable_ctlBit dt.cmpDecC).and (uGDefinable_ctlBit dt.cmpValC)).or
      ((uGDefinable_ctlBit dt.cmpDecC).not.and (hrd0.not.and hrd1))).congr
      fun e f g => ctlBit_cmpValC_cmpFold e.hzo hnf f
  exact (UGDefinable.ite (p := isEq = true) hacc (hacc.or hval)).congr
    fun _ _ _ => Iff.rfl

omit [L.IsRelational] in
/-- **A comparison's pack meets its obligation.** -/
theorem uElemArgsDef_cmpArgs (v : dt.VarIx) (a : Fin dt.natMax)
    (hnf : 2 ≤ dt.nfDim) (isEq : Bool) (j₁ j₂ : Fin (dt.nOf v)) :
    UElemArgsDef (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e : Env L => dt.cmpArgs e.zero e.one v a hnf isEq j₁ j₂ where
  rdTrack := ⟨_, fun _ => rfl⟩
  MatchOf k :=
    uGDefinable_nameG (if k = 0 then dt.lvBlk v j₁ else dt.lvBlk v j₂) dt.lvC
  setFlag _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  initEl := uStDefinable_cmpInit_initLvN
  advEl := by
    refine (uStDefinable_putLv_comp
      (w := fun e (f : dt.CtlIx → e.α) _ => tupNext (dt.readLv f))
      (fun j => uSlotDefinable_tupNext_lvC j) (uStDefinable_cmpFold hnf)).congr
      fun e f g q => ?_
    simp only [cmpArgs, advLvN, readLv_cmpFold]
  exitSt :=
    (uStDefinable_cmpFold hnf).update (dt.avC a)
      (uSlotDefinable_bitVal (uGDefinable_cmpVerdict_cmpFold hnf isEq))
  IsMaxEl := uGDefinable_isMaxLvN

/-! ### A stage atom's pack -/

omit [L.IsRelational] in
/-- **A stage atom's pack meets its obligation**: everything it names is
static, and the two bits it writes are flags. -/
theorem uStageArgsDef_stageArgs (v : dt.VarIx) (i : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf v)) (a : Fin dt.natMax) :
    UStageArgsDef (L := L) (Q := dt.CtlIx)
      fun e : Env L => dt.stageArgs e.zero e.one v i ts a where
  srcTrack := ⟨_, fun _ => rfl⟩
  srcBlk := ⟨_, fun _ => rfl⟩
  dstBlk := ⟨_, fun _ => rfl⟩
  coord := ⟨_, fun _ => rfl⟩
  oldSlot := ⟨_, fun _ => rfl⟩
  bitFlag := uGDefinable_ctlBit dt.bitFlagC
  setBit b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  initLv := uStDefinable_initLvN
  advLv := uStDefinable_advLvN
  IsMaxLv := uGDefinable_isMaxLvN
  setAv b := uStDefinable_setCtl _ (uGDefinable_const (b = true))

/-! ### A gate block's pack -/

/-- **A gate block's pack meets its obligation**: the witness reads are named
by the tags' encoded tuples, the leaf reads by the members of the gated point,
and the three folds are the gate's. The one thing that needs an environment is
the *default* branch of the dispatch, which names a tag. -/
theorem uTagArgsDef_gateArgs (e₀ : Env L) (b : Fin dt.ko ⊕ Fin dt.ki)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ t : dt.X.Tag, (dt.domPk t).n ≤ dt.eDim)
    (hrd : ∀ t : dt.X.Tag, dt.domNr t ≤ dt.nfDim) :
    UTagArgsDef (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e : Env L => dt.gateArgs e.zero e.one b hc hn hrd where
  rdTrackT := ⟨_, fun _ => rfl⟩
  MatchT c := uGDefinable_tagWitnessMatch b ((Fintype.equivFin dt.X.Tag).symm c)
  setTagFlag _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  TagsAre t := uGDefinable_dspTagsAre hc e₀ t
  rdTrackE := ⟨_, fun _ => rfl⟩
  MatchE t r := uGDefinable_domMatch b t r (hn t)
  setFlagE _ _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  initEl t := uStDefinable_gateInit t
  advEl t := uStDefinable_gateAdv t (hn t) (hrd t)
  exitSt t := uStDefinable_gateExit t hc (hn t) (hrd t)
  IsMaxEl _ := uGDefinable_isMaxLvE

/-- **An inner gate block's pack**, the same with the reads on VAL and the
verdict into the level's flag. -/
theorem uTagArgsDef_igateArgs (e₀ : Env L) (b : Fin dt.ko ⊕ Fin dt.ki)
    (flag : dt.CtlIx) (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hn : ∀ t : dt.X.Tag, (dt.domPk t).n ≤ dt.eDim)
    (hrd : ∀ t : dt.X.Tag, dt.domNr t ≤ dt.nfDim) :
    UTagArgsDef (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e : Env L => dt.igateArgs e.zero e.one b flag hc hn hrd where
  rdTrackT := ⟨_, fun _ => rfl⟩
  MatchT c := uGDefinable_tagWitnessMatch b ((Fintype.equivFin dt.X.Tag).symm c)
  setTagFlag _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  TagsAre t := uGDefinable_dspTagsAre hc e₀ t
  rdTrackE := ⟨_, fun _ => rfl⟩
  MatchE t r := uGDefinable_domMatch b t r (hn t)
  setFlagE _ _ b := uStDefinable_setCtl _ (uGDefinable_const (b = true))
  initEl t := uStDefinable_gateInit t
  advEl t := uStDefinable_gateAdv t (hn t) (hrd t)
  exitSt t := uStDefinable_igateExit flag t hc (hn t) (hrd t)
  IsMaxEl _ := uGDefinable_isMaxLvE

/-! ### An atom's pack, by kind -/

/-- **Every atom kind's pack meets its obligation**, one constructor at a
time. -/
theorem uKindArgsDef_kindArgsOf (v : dt.VarIx) (a : Fin dt.natMax) :
    ∀ (κ : MatAtom dt.X dt.d (dt.nOf v))
      (hk : dt.kindArgs κ * @Fintype.card dt.X.Tag (Fintype.ofFinite _) ≤ dt.ntgDim)
      (hn : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim),
      UKindArgsDef (L := L) (Q := dt.CtlIx) κ
        fun e : Env L => dt.kindArgsOf e.zero e.one v a κ hk hn hrd
  | .eq j₁ j₂, _, _, hrd => uElemArgsDef_cmpArgs v a hrd true j₁ j₂
  | .ord j₁ j₂, _, _, hrd => uElemArgsDef_cmpArgs v a hrd false j₁ j₂
  | .stage i ts, _, _, _ => uStageArgsDef_stageArgs v i ts a
  | @MatAtom.exp _ _ _ _ k e' ts, hk, hn, hrd =>
    letI := Fintype.ofFinite dt.X.Tag
    uTagArgsDef_expArgs v ts e' a hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e' τ').n) (Finset.mem_univ τ)) hn)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e' τ').mat).length) (Finset.mem_univ τ)) hrd)

/-- **The pack of the `a`-th atom of a variable's matrix.** -/
theorem uKindArgsDef_atomArgs (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    UKindArgsDef (L := L) (Q := dt.CtlIx) (dt.kindOf v a)
      fun e : Env L => dt.atomArgs e.zero e.one v a :=
  uKindArgsDef_kindArgsOf v _ (dt.kindOf v a) _ _ _

/-! ### The whole pack of a variable -/

/-- **The semantic pack of one variable's machinery meets its obligation.**
This is the last thing the program's rules owe the interpretation: with it,
`DescriptiveComplexity.Pfp.PfpData.uRulesDefinable_progAsm` applies to the
reduction's own machine. -/
theorem uVarArgsDef_varArgsOf (e₀ : Env L) (v : dt.VarIx) :
    UVarArgsDef (L := L) (Q := dt.CtlIx) v
      fun e : Env L => dt.varArgsOf e.zero e.one v where
  argsA a := uKindArgsDef_atomArgs v a
  enterAtomSt _ := uStDefinable_id
  argsG _ := uTagArgsDef_gateArgs e₀ _ _ _ _
  wellGOf _ := uGDefinable_wellShapedG _
  setFail := uStDefinable_setCtl _ (uGDefinable_const False)
  enterBlockSt _ := uStDefinable_id
  argsIG _ := uTagArgsDef_igateArgs e₀ _ _ _ _ _
  wellIGOf _ := uGDefinable_wellShapedIG _
  setFailIGOf _ := uStDefinable_setCtl _ (uGDefinable_const False)
  enterIGSt ℓ :=
    UStDefinable.ite (p := (ℓ : ℕ) = 0)
      ((uStDefinable_id.update dt.allGateC
        (uSlotDefinable_bitVal (uGDefinable_const True))).update dt.existGateC
        (uSlotDefinable_bitVal (uGDefinable_const True))) uStDefinable_id
  existFlag := ⟨_, fun _ => rfl⟩
  allFlag := ⟨_, fun _ => rfl⟩
  newSlot := ⟨_, fun _ => rfl⟩
  gateFlag := ⟨_, fun _ => rfl⟩
  accBit := uGDefinable_accVerdict (dt.polOf v)
  enterSt := uStDefinable_setCtl _ (uGDefinable_const True)
  initSt :=
    ((uStDefinable_initAcc (dt.polOf v)).update dt.allGateC
      (uSlotDefinable_bitVal (uGDefinable_const True))).update dt.existGateC
      (uSlotDefinable_bitVal (uGDefinable_const True))
  postFold :=
    uStDefinable_setLeaf
      ((uGDefinable_ctlBit dt.existGateC).and
        ((uGDefinable_ctlBit dt.allGateC).imp (uGDefinable_postLeaf v)))
  storeCarry _ := uStDefinable_carryAcc (dt.polOf v) _

/-- **The EXPSPACE program's whole rule set is definable.** Every rule of the
reduction's own machine – its guard, the pointer it leaves and the tracks it
writes – is written down by one formula for every instance, so the eleven
relations of `FirstOrder.Language.wide` can be emitted by an interpretation.
The one environment it asks for is what names the dispatch's default tag. -/
theorem uRulesDefinable_progOf (e₀ : Env L) :
    URulesDefinable (L := L) (Q := dt.CtlIx) (S := dt.SF) (Sh := dt.SFSh)
      fun e : Env L =>
        dt.outerRule e.zero e.one
          (dt.evalRuleF e.zero e.one fun v => dt.varArgsOf e.zero e.one v)
          (.chk 0) (.sub dt.smEntryOut) :=
  uRulesDefinable_progAsm fun v => uVarArgsDef_varArgsOf e₀ v

end PfpData

end Pfp

end DescriptiveComplexity
