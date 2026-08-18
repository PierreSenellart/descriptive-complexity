/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpVarRule

/-!
# The program, assembled

The last shape layer: the tower of
`DescriptiveComplexity.Problems.Wide.PfpTower` is plugged together into
**one** `DescriptiveComplexity.Pfp.Assembly` – the gates and the matrix into
one variable's machinery, one copy of that per fixed-point variable (and one
for the output), those into the evaluation's spine, and the spine into the
outer loop – so that `DescriptiveComplexity.Pfp.Assembly.prog` and
`DescriptiveComplexity.Pfp.Assembly.sep` deliver the program together with
its determinism.

The **semantic** parameters ride in one pack per variable
(`DescriptiveComplexity.Pfp.PfpData.VarArgs`): the per-atom and per-block
parameter packs, the loop and fold updates, the stage slot the variable
writes and the accumulator its verdict is read from. Separation never reads
any of them, so the assembly is complete before their content is fixed –
that happens with the runs.

Where the machinery goes, in one glance (the flow of
`DescriptiveComplexity.Pfp.PfpData.varRuleF`): the entry checkpoint enters
the gates; the gates' failing block clears the verdict flag and lands on the
verdict checkpoint, which either writes `False` into the stage slot and
leaves, or clears the VAL register and enters the matrix; the matrix's exit
is the post-matrix checkpoint, which folds and tests VAL for exhaustion –
increment and matrix again, or the exit checkpoint, which writes the
variable's next-stage bit at the marker.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q P : Type}

/-! ### The semantic parameters, per variable -/

/-- The parameter pack of a gate block's tag-branched domain evaluation. -/
noncomputable def GateArgs : Type :=
  letI := Fintype.ofFinite dt.X.Tag
  TagArgs A Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr

/-- **The semantic parameters of one variable's machinery**: the per-atom
packs of its matrix and the per-block packs of its gates, the control
updates the checkpoints carry, the stage slot it writes and the flags its
verdicts are read from. Separation reads none of them. -/
structure VarArgs (v : dt.VarIx) where
  /-- The parameter pack of each classified atom of the matrix. -/
  argsA : ∀ a : Fin (dt.natOf v), dt.KindArgs (A := A) (Q := Q) (dt.kindOf v a)
  /-- The control update entering each atom. -/
  enterAtomSt : Fin (dt.natOf v) → (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The parameter pack of each argument block's domain evaluation. -/
  argsG : Fin (dt.arOf v) → dt.GateArgs (A := A) (Q := Q)
  /-- The well-shapedness question of each argument block. -/
  wellGOf : Fin (dt.arOf v) → (dt.SlotIx → A) → Prop
  /-- Clearing the gates' verdict flag. -/
  setFail : (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The control update entering each gate block. -/
  enterBlockSt : Fin (dt.arOf v) → (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The parameter pack of each quantified level's inner gate. -/
  argsIG : Fin (dt.nIn v) → dt.GateArgs (A := A) (Q := Q)
  /-- The well-shapedness question of each inner gate. -/
  wellIGOf : Fin (dt.nIn v) → (dt.SlotIx → A) → Prop
  /-- Clearing the level's polarity flag on a failed inner gate. -/
  setFailIGOf : Fin (dt.nIn v) → (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The control update entering each inner gate block — the first one
  resets the round's two flags. -/
  enterIGSt : Fin (dt.nIn v) → (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The ∃-levels' gate flag. -/
  existFlag : Q
  /-- The ∀-levels' gate flag. -/
  allFlag : Q
  /-- The stage slot the variable writes. -/
  newSlot : dt.SlotIx
  /-- The gates' verdict flag. -/
  gateFlag : Q
  /-- The verdict the exit checkpoint writes. -/
  accBit : (Q → A) → Prop
  /-- The control update entering the machinery: where the gates' verdict
  flag is set, since every block conjoins into it and a variable with no
  argument blocks never touches it. -/
  enterSt : (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The folds at the empty valuation. -/
  initSt : (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The folds after a matrix pass. -/
  postFold : (Q → A) → (dt.SlotIx → A) → Q → A
  /-- The folds at an increment's carry block. -/
  storeCarry : dt.CarryB → (Q → A) → (dt.SlotIx → A) → Q → A

/-! ### One variable's machinery, plugged in -/

variable (zero one : A)

/-- **The rules of one variable's machinery**, the gates and the matrix
plugged into the spine of
`DescriptiveComplexity.Problems.Wide.PfpVar`. -/
noncomputable def varRuleF (v : dt.VarIx) (args : dt.VarArgs (A := A) (Q := Q) v)
    (emb : dt.VarPhF v → P) (exitPh : P) :
    ∀ i : dt.VarSiteF v, dt.VarShF v i → Rule A Q dt.SlotIx P :=
  dt.varRule zero one emb
    (dt.gatesRule (one := one) (v := v) (emb := fun p => emb (.gatesP p))
      (argsG := args.argsG) (wellGOf := args.wellGOf) (setFail := args.setFail)
      (enterSt := args.enterBlockSt) (failPh := emb .vchk1)
      (exitPh := emb .vchk1))
    (dt.roundRule (one := one) (emb := fun p => emb (.matrixP p))
      (ruleG := dt.igatesRule (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.igP p)))
        (argsG := args.argsIG) (wellGOf := args.wellIGOf)
        (setFailOf := args.setFailIGOf) (enterSt := args.enterIGSt)
        (exitPh := emb (.matrixP .rchk)))
      (ruleX := dt.matrixRule (zero := zero) (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.matP p))) (argsA := args.argsA)
        (enterSt := args.enterAtomSt) (exitPh := emb .mchk1))
      (pxEntry := emb (.matrixP (.matP (.chk 0)))) (exitPh := emb .mchk1)
      (existFlag := args.existFlag) (allFlag := args.allFlag))
    (emb (.gatesP (.chk 0))) (emb (.matrixP (.igP (.chk 0)))) exitPh
    args.newSlot args.gateFlag args.accBit args.enterSt args.initSt
    args.postFold args.storeCarry

variable {dt}

/-- **Every rule of one variable's machinery fires from a phase its site
owns.** -/
theorem varHosrcF (v : dt.VarIx) (args : dt.VarArgs (A := A) (Q := Q) v)
    {emb : dt.VarPhF v → P} (exitPh : P) :
    ∀ (i : dt.VarSiteF v) (ρ : dt.VarShF v i),
      ∃ p : dt.VarPhF v,
        (dt.varRuleF zero one v args emb exitPh i ρ).srcPh = emb p ∧
          dt.varOwnF v p = i :=
  dt.varHosrc zero one _ _ _ _ _ _ _ _ _ _
    (ownG := seqOwn fun _ => dt.gateBlockOwn)
    (ownX := dt.roundOwnF v)
    (dt.gatesHosrc (one := one) (v := v) (emb := fun p => emb (.gatesP p))
      (argsG := args.argsG) (wellGOf := args.wellGOf) (setFail := args.setFail)
      (enterSt := args.enterBlockSt) (failPh := emb .vchk1)
      (exitPh := emb .vchk1))
    (dt.roundHosrc one (emb (.matrixP (.matP (.chk 0)))) (emb .mchk1)
      args.existFlag args.allFlag
      (dt.igatesHosrc (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.igP p)))
        (argsG := args.argsIG) (wellGOf := args.wellIGOf)
        (setFailOf := args.setFailIGOf) (enterSt := args.enterIGSt)
        (exitPh := emb (.matrixP .rchk)))
      (dt.matrixHosrc (zero := zero) (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.matP p))) (argsA := args.argsA)
        (enterSt := args.enterAtomSt) (exitPh := emb .mchk1)))

/-- **A property of one variable machinery's phases and its exit holds of every
phase it can move to**: the gates, the round and the matrix all stay inside, and
only the two verdict dispatches leave. This is the fact a
determinism-after-the-guess argument asks of the evaluation
(`DescriptiveComplexity.Pfp.PfpData.nexProg_uniqueFrom`). -/
theorem varRuleF_dstIn (v : dt.VarIx) (args : dt.VarArgs (A := A) (Q := Q) v)
    {emb : dt.VarPhF v → P} (exitPh : P) {S : P → Prop}
    (hemb : ∀ p : dt.VarPhF v, S (emb p)) (hexit : S exitPh)
    (i : dt.VarSiteF v) (ρ : dt.VarShF v i) :
    S (dt.varRuleF zero one v args emb exitPh i ρ).dstPh :=
  dt.varRule_dstIn zero one (emb := emb)
    (pgEntry := emb (.gatesP (.chk 0)))
    (pxEntry := emb (.matrixP (.igP (.chk 0)))) (exitPh := exitPh)
    (newSlot := args.newSlot) (gateFlag := args.gateFlag) (accBit := args.accBit)
    (enterSt := args.enterSt) (initSt := args.initSt) (postFold := args.postFold)
    (storeCarry := args.storeCarry)
    (S := S) hemb hexit
    (fun s ρ => dt.gatesRule_dstIn (one := one) (v := v)
      (emb := fun p => emb (.gatesP p)) (argsG := args.argsG)
      (wellGOf := args.wellGOf) (setFail := args.setFail)
      (enterSt := args.enterBlockSt) (failPh := emb .vchk1) (exitPh := emb .vchk1)
      (fun p => hemb (.gatesP p)) (hemb .vchk1) (hemb .vchk1) s ρ)
    (fun s ρ => dt.roundRule_dstIn (one := one)
      (emb := fun p => emb (.matrixP p))
      (ruleG := dt.igatesRule (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.igP p))) (argsG := args.argsIG)
        (wellGOf := args.wellIGOf) (setFailOf := args.setFailIGOf)
        (enterSt := args.enterIGSt) (exitPh := emb (.matrixP .rchk)))
      (ruleX := dt.matrixRule (zero := zero) (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.matP p))) (argsA := args.argsA)
        (enterSt := args.enterAtomSt) (exitPh := emb .mchk1))
      (pxEntry := emb (.matrixP (.matP (.chk 0)))) (exitPh := emb .mchk1)
      (existFlag := args.existFlag) (allFlag := args.allFlag)
      (fun p => hemb (.matrixP p)) (hemb .mchk1)
      (fun s ρ => dt.igatesRule_dstIn (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.igP p))) (argsG := args.argsIG)
        (wellGOf := args.wellIGOf) (setFailOf := args.setFailIGOf)
        (enterSt := args.enterIGSt) (exitPh := emb (.matrixP .rchk))
        (fun p => hemb (.matrixP (.igP p))) (hemb (.matrixP .rchk)) s ρ)
      (fun s ρ => dt.matrixRule_dstIn (zero := zero) (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.matP p))) (argsA := args.argsA)
        (enterSt := args.enterAtomSt) (exitPh := emb .mchk1)
        (fun p => hemb (.matrixP (.matP p))) (hemb .mchk1) s ρ)
      (hemb (.matrixP (.matP (.chk 0)))) s ρ)
    (hemb (.gatesP (.chk 0))) (hemb (.matrixP (.igP (.chk 0)))) i ρ

/-- **One variable's machinery separates in-shape.** -/
theorem varSepF (hzo : zero ≠ one) (v : dt.VarIx)
    (args : dt.VarArgs (A := A) (Q := Q) v)
    {emb : dt.VarPhF v → P} (hemb : Function.Injective emb) (exitPh : P) :
    ∀ (i : dt.VarSiteF v) (ρ ρ' : dt.VarShF v i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.varRuleF zero one v args emb exitPh i ρ).guard f g →
      (dt.varRuleF zero one v args emb exitPh i ρ').guard f g →
      (dt.varRuleF zero one v args emb exitPh i ρ).srcPh =
        (dt.varRuleF zero one v args emb exitPh i ρ').srcPh →
      ρ = ρ' :=
  dt.varSep zero one hzo hemb
    (dt.gatesSep (one := one) (v := v) (emb := fun p => emb (.gatesP p))
      (argsG := args.argsG) (wellGOf := args.wellGOf) (setFail := args.setFail)
      (enterSt := args.enterBlockSt) (failPh := emb .vchk1)
      (exitPh := emb .vchk1) (fun x y h => by cases hemb h; rfl))
    (dt.roundSep one (emb (.matrixP (.matP (.chk 0)))) (emb .mchk1)
      args.existFlag args.allFlag
      (dt.igatesSep (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.igP p)))
        (argsG := args.argsIG) (wellGOf := args.wellIGOf)
        (setFailOf := args.setFailIGOf) (enterSt := args.enterIGSt)
        (exitPh := emb (.matrixP .rchk))
        (fun x y h => by
          have h1 := hemb h
          injection h1 with h2
          injection h2))
      (dt.matrixSep (zero := zero) (one := one) (v := v)
        (emb := fun p => emb (.matrixP (.matP p))) (argsA := args.argsA)
        (enterSt := args.enterAtomSt) (exitPh := emb .mchk1) hzo
        (fun x y h => by
          have h1 := hemb h
          injection h1 with h2
          injection h2)))

/-! ### The evaluation's machineries -/

variable (dt)

/-- **The rules of the evaluation's machineries**: one copy of the variable
machinery per spine position – its exit the next checkpoint – and the
output's, whose exit is the accepting phase (the verdict itself is read from
the control by the program's accepting predicate). -/
noncomputable def smRule (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ s : dt.SMF, dt.SMSh s → Rule A Q dt.SlotIx (OuterPh dt.PEF)
  | Sum.inl ⟨j, s⟩, ρ =>
    dt.varRuleF zero one (dt.varAt j) (args _)
      (fun p => .evalP (.sub (Sum.inl ⟨j, p⟩))) (.evalP (.chk j.succ)) s ρ
  | Sum.inr s, ρ =>
    dt.varRuleF zero one none (args none)
      (fun p => .evalP (.sub (Sum.inr p))) .acceptP s ρ

/-- The entry phase of the machinery at a spine position. -/
noncomputable def smEntry (j : Fin dt.nv) : dt.PMF := Sum.inl ⟨j, .vchk0⟩

/-- The entry phase of the output's machinery. -/
noncomputable def smEntryOut : dt.PMF := Sum.inr .vchk0

variable {dt}

/-- **Every rule of the evaluation's machineries fires from a phase its site
owns.** -/
theorem smHosrc (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (s : dt.SMF) (ρ : dt.SMSh s),
      ∃ p : dt.PMF, (dt.smRule zero one args s ρ).srcPh = .evalP (.sub p) ∧
        dt.smOwn p = s := by
  intro s ρ
  match s, ρ with
  | Sum.inl ⟨j, s⟩, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      dt.varHosrcF zero one (dt.varAt j) (args _)
        (emb := fun p => (OuterPh.evalP (.sub (Sum.inl ⟨j, p⟩)) : OuterPh dt.PEF))
        (.evalP (.chk j.succ)) s ρ
    exact ⟨Sum.inl ⟨j, p⟩, hp, congrArg (fun x => (Sum.inl ⟨j, x⟩ : dt.SMF)) ho⟩
  | Sum.inr s, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      dt.varHosrcF zero one none (args none)
        (emb := fun p => (OuterPh.evalP (.sub (Sum.inr p)) : OuterPh dt.PEF))
        .acceptP s ρ
    exact ⟨Sum.inr p, hp, congrArg (fun x => (Sum.inr x : dt.SMF)) ho⟩

/-- **The evaluation's machineries separate in-shape.** -/
theorem smSep (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (s : dt.SMF) (ρ ρ' : dt.SMSh s) (f : Q → A) (g : dt.SlotIx → A),
      (dt.smRule zero one args s ρ).guard f g →
      (dt.smRule zero one args s ρ').guard f g →
      (dt.smRule zero one args s ρ).srcPh = (dt.smRule zero one args s ρ').srcPh →
      ρ = ρ' := by
  intro s ρ ρ' f g hg hg' hph
  match s, ρ, ρ' with
  | Sum.inl ⟨j, s⟩, ρ, ρ' =>
    exact dt.varSepF zero one hzo (dt.varAt j) (args _)
      (emb := fun p => (OuterPh.evalP (.sub (Sum.inl ⟨j, p⟩)) : OuterPh dt.PEF))
      (fun x y h => by
        have h1 := OuterPh.evalP.inj h
        have h2 := EvalPh.sub.inj h1
        have h3 : (⟨j, x⟩ : (Σ j' : Fin dt.nv, dt.VarPhF (dt.varAt j'))) = ⟨j, y⟩ :=
          Sum.inl.inj h2
        exact sigma_mk_injective (β := fun j' : Fin dt.nv => dt.VarPhF (dt.varAt j')) h3)
      (.evalP (.chk j.succ)) s ρ ρ' f g hg hg' hph
  | Sum.inr s, ρ, ρ' =>
    exact dt.varSepF zero one hzo none (args none)
      (emb := fun p => (OuterPh.evalP (.sub (Sum.inr p)) : OuterPh dt.PEF))
      (fun x y h => by
        have h1 := OuterPh.evalP.inj h
        have h2 := EvalPh.sub.inj h1
        have h3 : (x : dt.VarPhF none) = y := Sum.inr.inj h2
        exact h3)
      .acceptP s ρ ρ' f g hg hg' hph

/-! ### The whole program -/

variable (dt)

/-- **The rules of the evaluation**: the spine over the machineries. -/
noncomputable def evalRuleF (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ e : dt.SEF, dt.SESh e → Rule A Q dt.SlotIx (OuterPh dt.PEF) :=
  dt.evalRule zero one (dt.smRule zero one args) (dt.smEntry)

variable {dt}

/-- **Every evaluation rule fires from a phase its site owns.** -/
theorem evalHosrcF (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (e : dt.SEF) (ρ : dt.SESh e),
      ∃ p : dt.PEF, (dt.evalRuleF zero one args e ρ).srcPh = .evalP p ∧
        dt.seOwn p = e :=
  dt.evalHosrc zero one (smHosrc zero one args)

/-- **The evaluation separates in-shape.** -/
theorem evalSepF (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    ∀ (e : dt.SEF) (ρ ρ' : dt.SESh e) (f : Q → A) (g : dt.SlotIx → A),
      (dt.evalRuleF zero one args e ρ).guard f g →
      (dt.evalRuleF zero one args e ρ').guard f g →
      (dt.evalRuleF zero one args e ρ).srcPh =
        (dt.evalRuleF zero one args e ρ').srcPh →
      ρ = ρ' :=
  dt.evalSep zero one (smSep zero one hzo args)

variable (dt) [Fintype Q] [Fintype dt.SlotIx]

/-- **The program's assembly**: every site of the outer loop, of the
evaluation's spine, of each variable's machinery and of each atom's
subroutine, with its rules, its owner and its in-shape separation. This is
the EXPSPACE program's rule set, complete; `DescriptiveComplexity.Pfp.Assembly.prog`
turns it into a `DescriptiveComplexity.Pfp.Prog` and
`DescriptiveComplexity.Pfp.Assembly.sep` into its determinism. -/
noncomputable def progAsm (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    Assembly A Q dt.SlotIx dt.PF dt.SF :=
  dt.outerAsm zero one (ruleE := dt.evalRuleF zero one args)
    (evalEntry := .chk 0) (evalEntryOut := .sub (dt.smEntryOut))
    (ownE := dt.seOwn) (hosrcE := evalHosrcF zero one args) hzo
    (evalSepF zero one hzo args)

/-- **The rule names of the program**: a site and one of its rules. -/
noncomputable abbrev RIx (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) : Type :=
  (i : dt.SF) × (dt.progAsm zero one hzo args).Sh i

/-! ### The machine

The remaining fields of a `DescriptiveComplexity.Pfp.Prog` are the
reduction's constants: the start phase and an all-clear pointer, the
accepting predicate – the output machinery's exit phase, with its verdict
read from the control, so that a false output halts and rejects – the blank
symbol, and the mark of `DescriptiveComplexity.Pfp.slotMark`. -/

section Machine

variable [LinearOrder A]
variable (hzo : zero ≠ one)
variable (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v)
variable [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]

/-- **The EXPSPACE program**: the assembled rule set with the reduction's
constants. -/
noncomputable def prog (hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd) :
    Prog A (dt.RIx zero one hzo args) dt.PF Q dt.SlotIx dt.KIx dt.dd :=
  (dt.progAsm zero one hzo args).prog (K := dt.KIx) (dd := dt.dd) zero one hzo
    hpl .start (fun _ => zero)
    (fun p f => p = .acceptP ∧ (args none).accBit f)
    (fun _ => zero) (slotMark zero one dt.dd0Le)

/-- **The program is deterministic**: separation by the assembly, site by
site. -/
theorem prog_sep (hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd) :
    (dt.prog zero one hzo args hpl).table.Sep :=
  Assembly.sep _

variable {dt zero one hzo args}

/-- The mirror track is clear at time zero – on the register file and off it
alike – so it is the track the initial tape is presented along
(`DescriptiveComplexity.Pfp.Prog.trackTape_initBack`). -/
theorem prog_mark_mir (hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd)
    (x : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) :
    (dt.prog zero one hzo args hpl).mark x Slot.mir =
      (dt.prog zero one hzo args hpl).zero := rfl

theorem prog_blank_mir (hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd) :
    (dt.prog zero one hzo args hpl).blank Slot.mir =
      (dt.prog zero one hzo args hpl).zero := rfl

end Machine

end PfpData

end Pfp

end DescriptiveComplexity
