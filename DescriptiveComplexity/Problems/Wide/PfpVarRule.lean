/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpKindRule

/-!
# The matrix's and the gates' rules

One layer up from the kind dispatch: the **matrix** of a variable is the
sequencer over its classified atoms – each stage the kind's machinery, its
exit the next checkpoint – and the **gates** are the sequencer over the
argument blocks, each block a well-shapedness file test whose passing exit
enters the tag-branched domain evaluation and whose failing exit leaves the
whole gate sequence with the verdict flag cleared.

As below, the semantic parameters ride in packs and `dstSt` parameters;
the shapes and separations close here.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q P : Type}
variable (zero one : A)

/-! ### The matrix -/

section Matrix

variable (v : dt.VarIx) (emb : dt.MatrixPh v → P)
variable (argsA : ∀ a : Fin (dt.natOf v), dt.KindArgs (A := A) (Q := Q) (dt.kindOf v a))
variable (enterSt : Fin (dt.natOf v) → (Q → A) → (dt.SlotIx → A) → Q → A)
variable (exitPh : P)

/-- **The matrix's rules**: the sequencer over the classified atoms, each
stage its kind's machinery, its exit the next checkpoint. -/
noncomputable def matrixRule :
    ∀ i : dt.MatrixSite v, dt.MatrixSh v i → Rule A Q dt.SlotIx P :=
  seqRule one Slot.wk Slot.reg emb
    (fun a s ρ => dt.kindRule zero one (dt.kindOf v a) (argsA a)
      (fun p => emb (.sub a p)) (emb (.chk a.succ)) s ρ)
    (fun a => dt.kindEntry (dt.kindOf v a))
    enterSt exitPh

variable {emb}

/-- **Every rule of the matrix fires from a phase its site owns.** -/
theorem matrixHosrc :
    ∀ (i : dt.MatrixSite v) (ρ : dt.MatrixSh v i),
      ∃ p : dt.MatrixPh v,
        (dt.matrixRule zero one v emb argsA enterSt exitPh i ρ).srcPh = emb p ∧
          seqOwn (fun a => dt.kindOwn (dt.kindOf v a)) p = i :=
  seqHosrc one Slot.wk Slot.reg emb
    (fun a s ρ => dt.kindRule zero one (dt.kindOf v a) (argsA a)
      (fun p => emb (.sub a p)) (emb (.chk a.succ)) s ρ)
    (fun a => dt.kindEntry (dt.kindOf v a))
    enterSt exitPh
    (fun a => dt.kindOwn (dt.kindOf v a))
    (fun a s ρ =>
      kindHosrc zero one (dt.kindOf v a) (argsA a) (emb (.chk a.succ)) s ρ)

/-- **The matrix separates in-shape.** -/
theorem matrixSep (hzo : zero ≠ one) (hemb : Function.Injective emb) :
    ∀ (i : dt.MatrixSite v) (ρ ρ' : dt.MatrixSh v i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.matrixRule zero one v emb argsA enterSt exitPh i ρ).guard f g →
      (dt.matrixRule zero one v emb argsA enterSt exitPh i ρ').guard f g →
      (dt.matrixRule zero one v emb argsA enterSt exitPh i ρ).srcPh =
        (dt.matrixRule zero one v emb argsA enterSt exitPh i ρ').srcPh →
      ρ = ρ' :=
  seqSep one Slot.wk Slot.reg emb
    (fun a s ρ => dt.kindRule zero one (dt.kindOf v a) (argsA a)
      (fun p => emb (.sub a p)) (emb (.chk a.succ)) s ρ)
    (fun a => dt.kindEntry (dt.kindOf v a))
    enterSt exitPh
    (fun a s ρ ρ' f g hg hg' hph =>
      kindSep zero one hzo (dt.kindOf v a) (argsA a)
        (fun x y h => by cases hemb h; rfl)
        (emb (.chk a.succ)) s ρ ρ' f g hg hg' hph)

end Matrix

/-! ### One gate block -/

section GateBlock

variable (emb : dt.GateBlockPh → P)
variable (args : letI := Fintype.ofFinite dt.X.Tag
  TagArgs A Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr)
variable (wellG : (dt.SlotIx → A) → Prop)
variable (setFail : (Q → A) → (dt.SlotIx → A) → Q → A)
variable (failPh exitPh : P)

/-- The entry of the domain evaluation. -/
noncomputable def gateDomEntry : P :=
  letI := Fintype.ofFinite dt.X.Tag
  tagFirstRd (fun p => emb (Sum.inr p))

/-- **One gate block's rules**: the well-shapedness file test – its passing
exit entering the domain evaluation, its failing exit leaving the whole
gate sequence with the verdict flag cleared – and the tag-branched domain
evaluation. -/
noncomputable def gateBlockRule :
    ∀ i : dt.GateBlockSite, dt.GateBlockSh i → Rule A Q dt.SlotIx P
  | Sum.inl _, Sum.inl ρ =>
    (TestKit.mk (A := A) (Q := Q) Slot.mir Slot.reg Slot.regLast Slot.wk
      wellG (fun t => emb (Sum.inl t))).rule one ρ
  | Sum.inl _, Sum.inr b =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (Sum.inl (if b then .ty else .tn))
      dstPh := if b then dt.gateDomEntry emb else failPh
      dstSt := fun f g => if b then f else setFail f g
      wr := fun _ g => g
      moveRight := True }
  | Sum.inr s, ρ =>
    letI := Fintype.ofFinite dt.X.Tag
    tagRule one Slot.wk Slot.reg (fun p => emb (Sum.inr p)) args.rdTrackT
      args.MatchT args.setTagFlag args.TagsAre args.rdTrackE args.MatchE
      args.setFlagE args.initEl args.advEl args.exitSt args.IsMaxEl exitPh s ρ

variable {emb}

/-- **Every rule of a gate block fires from a phase its site owns.** -/
theorem gateBlockHosrc :
    ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
      ∃ p : dt.GateBlockPh,
        (dt.gateBlockRule (one := one) (emb := emb) (args := args)
          (wellG := wellG) (setFail := setFail) (failPh := failPh)
          (exitPh := exitPh) i ρ).srcPh = emb p ∧ dt.gateBlockOwn p = i := by
  intro i ρ
  match i, ρ with
  | Sum.inl _, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | Sum.inl _, Sum.inr b => cases b <;> exact ⟨_, rfl, rfl⟩
  | Sum.inr s, ρ =>
    letI := Fintype.ofFinite dt.X.Tag
    obtain ⟨p, hp, ho⟩ :=
      tagHosrc one Slot.wk Slot.reg args.rdTrackT args.MatchT args.setTagFlag
        args.TagsAre args.rdTrackE args.MatchE args.setFlagE args.initEl
        args.advEl args.exitSt args.IsMaxEl exitPh
        (emb := fun p => emb (Sum.inr p)) s ρ
    exact ⟨Sum.inr p, hp, congrArg Sum.inr ho⟩

/-- **One gate block separates in-shape.** -/
theorem gateBlockSep (hemb : Function.Injective emb) :
    ∀ (i : dt.GateBlockSite) (ρ ρ' : dt.GateBlockSh i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.gateBlockRule (one := one) (emb := emb) (args := args)
        (wellG := wellG) (setFail := setFail) (failPh := failPh)
        (exitPh := exitPh) i ρ).guard f g →
      (dt.gateBlockRule (one := one) (emb := emb) (args := args)
        (wellG := wellG) (setFail := setFail) (failPh := failPh)
        (exitPh := exitPh) i ρ').guard f g →
      (dt.gateBlockRule (one := one) (emb := emb) (args := args)
        (wellG := wellG) (setFail := setFail) (failPh := failPh)
        (exitPh := exitPh) i ρ).srcPh =
        (dt.gateBlockRule (one := one) (emb := emb) (args := args)
          (wellG := wellG) (setFail := setFail) (failPh := failPh)
          (exitPh := exitPh) i ρ').srcPh →
      ρ = ρ' := by
  have htst : Function.Injective (fun t => emb (Sum.inl t) : TestPh → P) :=
    fun x y h => by cases hemb h; rfl
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | Sum.inl _, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (TestKit.sep _ one htst σ σ' f g hg hg' hph)
  | Sum.inl _, Sum.inl σ, Sum.inr b =>
    refine absurd hph (fun hp => TestKit.exit_disjoint _ one htst σ f g hg
      hg'.1 hg'.2 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | Sum.inl _, Sum.inr b, Sum.inl σ =>
    refine absurd hph.symm (fun hp => TestKit.exit_disjoint _ one htst σ f g hg'
      hg.1 hg.2 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | Sum.inl _, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hemb hph
      injection h2 with h3
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | Sum.inr s, ρ, ρ' =>
    letI := Fintype.ofFinite dt.X.Tag
    exact tagSep one Slot.wk Slot.reg args.rdTrackT args.MatchT
      args.setTagFlag args.TagsAre args.rdTrackE args.MatchE args.setFlagE
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh
      (fun x y h => by cases hemb h; rfl) args.hTags s ρ ρ' f g hg hg' hph

end GateBlock

/-! ### The gates -/

section Gates

variable (v : dt.VarIx) (emb : dt.GatesPh v → P)
variable (argsG : Fin (dt.arOf v) →
  letI := Fintype.ofFinite dt.X.Tag
  TagArgs A Q dt.SlotIx (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr)
variable (wellGOf : Fin (dt.arOf v) → (dt.SlotIx → A) → Prop)
variable (setFail : (Q → A) → (dt.SlotIx → A) → Q → A)
variable (enterSt : Fin (dt.arOf v) → (Q → A) → (dt.SlotIx → A) → Q → A)
variable (failPh exitPh : P)

/-- **The gates' rules**: the sequencer over the argument blocks. -/
noncomputable def gatesRule :
    ∀ i : dt.GatesSite v, dt.GatesSh v i → Rule A Q dt.SlotIx P :=
  seqRule one Slot.wk Slot.reg emb
    (fun b s ρ => dt.gateBlockRule (one := one)
      (emb := fun p => emb (.sub b p)) (args := argsG b)
      (wellG := wellGOf b) (setFail := setFail) (failPh := failPh)
      (exitPh := emb (.chk b.succ)) s ρ)
    (fun _ => Sum.inl .up)
    enterSt exitPh

variable {emb}

/-- **Every rule of the gates fires from a phase its site owns.** -/
theorem gatesHosrc :
    ∀ (i : dt.GatesSite v) (ρ : dt.GatesSh v i),
      ∃ p : dt.GatesPh v,
        (dt.gatesRule (one := one) (v := v) (emb := emb) (argsG := argsG)
          (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
          (failPh := failPh) (exitPh := exitPh) i ρ).srcPh = emb p ∧
          seqOwn (fun _ => dt.gateBlockOwn) p = i :=
  seqHosrc one Slot.wk Slot.reg emb
    (fun b s ρ => dt.gateBlockRule (one := one)
      (emb := fun p => emb (.sub b p)) (args := argsG b)
      (wellG := wellGOf b) (setFail := setFail) (failPh := failPh)
      (exitPh := emb (.chk b.succ)) s ρ)
    (fun _ => Sum.inl .up)
    enterSt exitPh
    (fun _ => dt.gateBlockOwn)
    (fun b s ρ =>
      dt.gateBlockHosrc (one := one) (args := argsG b) (wellG := wellGOf b)
        (setFail := setFail) (failPh := failPh) (exitPh := emb (.chk b.succ))
        s ρ)

/-- **The gates separate in-shape.** -/
theorem gatesSep (hemb : Function.Injective emb) :
    ∀ (i : dt.GatesSite v) (ρ ρ' : dt.GatesSh v i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.gatesRule (one := one) (v := v) (emb := emb) (argsG := argsG)
        (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
        (failPh := failPh) (exitPh := exitPh) i ρ).guard f g →
      (dt.gatesRule (one := one) (v := v) (emb := emb) (argsG := argsG)
        (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
        (failPh := failPh) (exitPh := exitPh) i ρ').guard f g →
      (dt.gatesRule (one := one) (v := v) (emb := emb) (argsG := argsG)
        (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
        (failPh := failPh) (exitPh := exitPh) i ρ).srcPh =
        (dt.gatesRule (one := one) (v := v) (emb := emb) (argsG := argsG)
          (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
          (failPh := failPh) (exitPh := exitPh) i ρ').srcPh →
      ρ = ρ' :=
  seqSep one Slot.wk Slot.reg emb
    (fun b s ρ => dt.gateBlockRule (one := one)
      (emb := fun p => emb (.sub b p)) (args := argsG b)
      (wellG := wellGOf b) (setFail := setFail) (failPh := failPh)
      (exitPh := emb (.chk b.succ)) s ρ)
    (fun _ => Sum.inl .up)
    enterSt exitPh
    (fun b s ρ ρ' f g hg hg' hph =>
      dt.gateBlockSep (one := one) (args := argsG b) (wellG := wellGOf b)
        (setFail := setFail) (failPh := failPh) (exitPh := emb (.chk b.succ))
        (fun x y h => by cases hemb h; rfl)
        s ρ ρ' f g hg hg' hph)

end Gates

end PfpData

end Pfp

end DescriptiveComplexity
