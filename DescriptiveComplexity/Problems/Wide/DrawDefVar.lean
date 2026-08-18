/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefKind
import DescriptiveComplexity.Problems.Wide.DrawVarRule

/-!
# The matrix and the gates carry definability

One variable's machinery is a matrix – the sequencer over the classified atoms
of its step formula – and two runs of gates – sequencers over the argument
blocks and over the quantified levels, each block a well-shapedness file test
followed by a tag-branched domain evaluation. All four are sequencers over
things already discharged, so all four are one line plus the checkpoints'
control updates.

The only new shape is a gate block's **verdict exit**, whose destination
pointer branches on a bit that the *kit* fixes, not the data: passing leaves
the pointer alone, failing applies the caller's clearing update, and
`DescriptiveComplexity.Draw.UStDefinable.ite` decides which when the formula is
built.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} {Q P : Type} [Fintype Q]
variable [Fintype dt.SlotIx]

/-! ### The matrix -/

/-- **A matrix's rules are definable**: the sequencer over the classified
atoms, each stage its kind's machinery. -/
theorem uRulesDefinable_matrixRule {v : dt.VarIx} {emb : dt.MatrixPh v → P}
    {argsA : ∀ (e : Env L) (a : Fin (dt.natOf v)),
      dt.KindArgs (A := e.α) (Q := Q) (dt.kindOf v a)}
    {enterSt : ∀ e : Env L,
      Fin (dt.natOf v) → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {exitPh : P}
    (hA : ∀ a : Fin (dt.natOf v),
      UKindArgsDef (dt.kindOf v a) fun e => argsA e a)
    (hen : ∀ a : Fin (dt.natOf v), UStDefinable fun e => enterSt e a) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.matrixRule e.zero e.one v emb (argsA e) (enterSt e) exitPh :=
  uRulesDefinable_seqRule
    (fun a s ρ => uRulesDefinable_kindRule (dt.kindOf v a)
      (emb := fun p => emb (SeqPh.sub a p)) (exitPh := emb (.chk a.succ))
      (hA a) s ρ)
    hen

/-! ### One gate block -/

/-- **A gate block's rules are definable**: the well-shapedness file test, its
two verdict exits – the failing one clearing the caller's flag – and the
tag-branched domain evaluation. -/
theorem uRulesDefinable_gateBlockRule {emb : dt.GateBlockPh → P}
    {args : ∀ e : Env L,
      letI := Fintype.ofFinite dt.X.Tag
      TagArgs e.α Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr}
    {wellG : ∀ e : Env L, (dt.SlotIx → e.α) → Prop}
    {setFail : ∀ e : Env L, (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {failPh exitPh : P}
    (hwell : UGDefinable fun e (_ : Q → e.α) g => wellG e g)
    (hfail : UStDefinable setFail)
    (hargs : letI := Fintype.ofFinite dt.X.Tag
      UTagArgsDef args) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.gateBlockRule (one := e.one) (emb := emb) (args := args e)
        (wellG := wellG e) (setFail := setFail e) (failPh := failPh)
        (exitPh := exitPh) := by
  let := Fintype.ofFinite dt.X.Tag
  rintro (- | s) ρ
  · match ρ with
    | Sum.inl σ => exact TestKit.uRuleDefinable hwell σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG
        (uStDefinable_id.ite hfail) fun _ _ _ => rfl
  · exact uRulesDefinable_tagArgs (wk := Slot.wk) (rg := Slot.reg)
      (emb := fun p => emb (Sum.inr p)) (exitPh := exitPh) hargs s ρ

/-! ### The two runs of gates -/

/-- **The gates' rules are definable**: the sequencer over the argument
blocks. -/
theorem uRulesDefinable_gatesRule {v : dt.VarIx} {emb : dt.GatesPh v → P}
    {argsG : ∀ (e : Env L), Fin (dt.arOf v) →
      letI := Fintype.ofFinite dt.X.Tag
      TagArgs e.α Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr}
    {wellGOf : ∀ e : Env L, Fin (dt.arOf v) → (dt.SlotIx → e.α) → Prop}
    {setFail : ∀ e : Env L, (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {enterSt : ∀ e : Env L,
      Fin (dt.arOf v) → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {failPh exitPh : P}
    (hwell : ∀ b : Fin (dt.arOf v),
      UGDefinable fun e (_ : Q → e.α) g => wellGOf e b g)
    (hfail : UStDefinable setFail)
    (hargs : ∀ b : Fin (dt.arOf v),
      letI := Fintype.ofFinite dt.X.Tag
      UTagArgsDef fun e => argsG e b)
    (hen : ∀ b : Fin (dt.arOf v), UStDefinable fun e => enterSt e b) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.gatesRule (one := e.one) (v := v) (emb := emb) (argsG := argsG e)
        (wellGOf := wellGOf e) (setFail := setFail e) (enterSt := enterSt e)
        (failPh := failPh) (exitPh := exitPh) :=
  uRulesDefinable_seqRule
    (fun b s ρ => uRulesDefinable_gateBlockRule
      (emb := fun p => emb (SeqPh.sub b p)) (failPh := failPh)
      (exitPh := emb (.chk b.succ)) (hwell b) hfail (hargs b) s ρ)
    hen

/-- **The inner gates' rules are definable**: the same sequencer, every fail
exit continuing to the next block with the level's flag cleared. -/
theorem uRulesDefinable_igatesRule {v : dt.VarIx} {emb : dt.IGatesPh v → P}
    {argsG : ∀ (e : Env L), Fin (dt.nIn v) →
      letI := Fintype.ofFinite dt.X.Tag
      TagArgs e.α Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr}
    {wellGOf : ∀ e : Env L, Fin (dt.nIn v) → (dt.SlotIx → e.α) → Prop}
    {setFailOf : ∀ e : Env L,
      Fin (dt.nIn v) → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {enterSt : ∀ e : Env L,
      Fin (dt.nIn v) → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {exitPh : P}
    (hwell : ∀ b : Fin (dt.nIn v),
      UGDefinable fun e (_ : Q → e.α) g => wellGOf e b g)
    (hfail : ∀ b : Fin (dt.nIn v), UStDefinable fun e => setFailOf e b)
    (hargs : ∀ b : Fin (dt.nIn v),
      letI := Fintype.ofFinite dt.X.Tag
      UTagArgsDef fun e => argsG e b)
    (hen : ∀ b : Fin (dt.nIn v), UStDefinable fun e => enterSt e b) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.igatesRule (one := e.one) (v := v) (emb := emb) (argsG := argsG e)
        (wellGOf := wellGOf e) (setFailOf := setFailOf e) (enterSt := enterSt e)
        (exitPh := exitPh) :=
  uRulesDefinable_seqRule
    (fun b s ρ => uRulesDefinable_gateBlockRule
      (emb := fun p => emb (SeqPh.sub b p)) (failPh := emb (.chk b.succ))
      (exitPh := emb (.chk b.succ)) (hwell b) (hfail b) (hargs b) s ρ)
    hen

end Data

end Draw

end DescriptiveComplexity
