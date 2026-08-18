/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefProg
import DescriptiveComplexity.Problems.Wide.DrawProg

/-!
# The whole assembly is definable, given its semantic packs

The last floor: one variable's machinery
(`DescriptiveComplexity.Draw.DrawData.varRuleF`), the evaluation's machineries
(`smRule`), its spine (`evalRuleF`) and the program's assembly (`progAsm`) are
definable as soon as the **semantic packs** are – which is what
`DescriptiveComplexity.Draw.DrawData.UVarArgsDef` says, field by field: the four
control locations a variable's machinery names must be the same at every
instance, and every guard and control update it carries must be definable.

Nothing above this file reads a rule any more: what is left of the discharge is
`DescriptiveComplexity.Draw.DrawData.varArgsOf` meeting `UVarArgsDef`, which is a
statement about `DescriptiveComplexity.Problems.Wide.DrawArgs` alone.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : DrawData L} {Q P : Type} [Fintype Q]
variable [Fintype dt.SlotIx]

/-- **What one variable's semantic pack owes.** -/
structure UVarArgsDef (v : dt.VarIx)
    (args : ∀ e : Env L, dt.VarArgs (A := e.α) (Q := Q) v) : Prop where
  /-- Each classified atom's pack. -/
  argsA : ∀ a : Fin (dt.natOf v),
    UKindArgsDef (dt.kindOf v a) fun e => (args e).argsA a
  /-- The update entering each atom. -/
  enterAtomSt : ∀ a : Fin (dt.natOf v),
    UStDefinable fun e => (args e).enterAtomSt a
  /-- Each argument block's pack. -/
  argsG : ∀ b : Fin (dt.arOf v),
    letI := Fintype.ofFinite dt.X.Tag
    UTagArgsDef fun e => (args e).argsG b
  /-- Each argument block's well-shapedness question. -/
  wellGOf : ∀ b : Fin (dt.arOf v),
    UGDefinable fun e (_ : Q → e.α) g => (args e).wellGOf b g
  /-- Clearing the gates' verdict flag. -/
  setFail : UStDefinable fun e => (args e).setFail
  /-- The update entering each argument block. -/
  enterBlockSt : ∀ b : Fin (dt.arOf v),
    UStDefinable fun e => (args e).enterBlockSt b
  /-- Each quantified level's pack. -/
  argsIG : ∀ b : Fin (dt.nIn v),
    letI := Fintype.ofFinite dt.X.Tag
    UTagArgsDef fun e => (args e).argsIG b
  /-- Each quantified level's well-shapedness question. -/
  wellIGOf : ∀ b : Fin (dt.nIn v),
    UGDefinable fun e (_ : Q → e.α) g => (args e).wellIGOf b g
  /-- Clearing each level's polarity flag. -/
  setFailIGOf : ∀ b : Fin (dt.nIn v),
    UStDefinable fun e => (args e).setFailIGOf b
  /-- The update entering each level's block. -/
  enterIGSt : ∀ b : Fin (dt.nIn v),
    UStDefinable fun e => (args e).enterIGSt b
  /-- The ∃-levels' flag is the same at every instance. -/
  existFlag : UConst fun e => (args e).existFlag
  /-- And so is the ∀-levels'. -/
  allFlag : UConst fun e => (args e).allFlag
  /-- And so is the stage slot the variable writes. -/
  newSlot : UConst fun e => (args e).newSlot
  /-- And so is the gates' verdict flag. -/
  gateFlag : UConst fun e => (args e).gateFlag
  /-- The verdict the exit checkpoint writes is definable. -/
  accBit : UGDefinable fun e f (_ : dt.SlotIx → e.α) => (args e).accBit f
  /-- And so are the four folds. -/
  enterSt : UStDefinable fun e => (args e).enterSt
  /-- The folds at the empty valuation. -/
  initSt : UStDefinable fun e => (args e).initSt
  /-- The folds after a matrix pass. -/
  postFold : UStDefinable fun e => (args e).postFold
  /-- And the folds at an increment's carry block. -/
  storeCarry : ∀ b : dt.CarryB, UStDefinable fun e => (args e).storeCarry b

/-- **One variable's machinery is definable**: the gates, the round – inner
gates and matrix behind the branch checkpoint – and the variable's own
checkpoints. -/
theorem uRulesDefinable_varRuleF {v : dt.VarIx}
    {args : ∀ e : Env L, dt.VarArgs (A := e.α) (Q := Q) v}
    {emb : dt.VarPhF v → P} {exitPh : P} (h : UVarArgsDef v args) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.varRuleF e.zero e.one v (args e) emb exitPh := by
  obtain ⟨ef, hef0⟩ := h.existFlag
  obtain ⟨af, haf0⟩ := h.allFlag
  obtain ⟨ns, hns0⟩ := h.newSlot
  obtain ⟨gf, hgf0⟩ := h.gateFlag
  have hef : ∀ e : Env L, (args e).existFlag = ef := hef0
  have haf : ∀ e : Env L, (args e).allFlag = af := haf0
  have hns : ∀ e : Env L, (args e).newSlot = ns := hns0
  have hgf : ∀ e : Env L, (args e).gateFlag = gf := hgf0
  intro i ρ
  exact URuleDefinable.congr
    (uRulesDefinable_varRule (emb := emb) (pgEntry := emb (.gatesP (.chk 0)))
      (pxEntry := emb (.matrixP (.igP (.chk 0)))) (exitPh := exitPh)
      (newSlot := ns) (gateFlag := gf)
      (uRulesDefinable_gatesRule (emb := fun p => emb (.gatesP p))
        (failPh := emb .vchk1) (exitPh := emb .vchk1)
        h.wellGOf h.setFail h.argsG h.enterBlockSt)
      (uRulesDefinable_roundRule (emb := fun p => emb (.matrixP p))
        (pxEntry := emb (.matrixP (.matP (.chk 0)))) (exitPh := emb .mchk1)
        (existFlag := ef) (allFlag := af)
        (uRulesDefinable_igatesRule (emb := fun p => emb (.matrixP (.igP p)))
          (exitPh := emb (.matrixP .rchk))
          h.wellIGOf h.setFailIGOf h.argsIG h.enterIGSt)
        (uRulesDefinable_matrixRule (emb := fun p => emb (.matrixP (.matP p)))
          (exitPh := emb .mchk1) h.argsA h.enterAtomSt))
      h.accBit h.enterSt h.initSt h.postFold h.storeCarry i ρ)
    fun e => by simp only [varRuleF, hef, haf, hns, hgf]; rfl

/-- **The evaluation's machineries are definable**: one copy of the variable
machinery per spine position, and the output's. -/
theorem uRulesDefinable_smRule
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SMF) (Sh := dt.SMSh) fun e =>
      dt.smRule e.zero e.one (args e) := by
  rintro (⟨j, s⟩ | s) ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (OuterPh.evalP (.sub (Sum.inl ⟨j, p⟩)) : OuterPh dt.PEF))
      (exitPh := .evalP (.chk j.succ)) (h (dt.varAt j)) s ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (OuterPh.evalP (.sub (Sum.inr p)) : OuterPh dt.PEF))
      (exitPh := .acceptP) (h none) s ρ

/-- **The evaluation is definable**: its spine over the machineries. -/
theorem uRulesDefinable_evalRuleF
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SEF) (Sh := dt.SESh) fun e =>
      dt.evalRuleF e.zero e.one (args e) :=
  uRulesDefinable_evalRule (uRulesDefinable_smRule h)

/-- **The whole program's rule set is definable**: the outer loop around the
evaluation. This is `DescriptiveComplexity.Draw.DrawData.progAsm`'s `rule` field,
so an interpretation may be written down from here. -/
theorem uRulesDefinable_progAsm
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SF) (Sh := dt.SFSh) fun e =>
      dt.outerRule e.zero e.one (dt.evalRuleF e.zero e.one (args e))
        (.chk 0) (.sub dt.smEntryOut) :=
  uRulesDefinable_outerRule (uRulesDefinable_evalRuleF h)

end DrawData

end Draw

end DescriptiveComplexity
