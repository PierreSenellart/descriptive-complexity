/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefStage
import DescriptiveComplexity.Problems.Wide.DrawKindRule

/-!
# What a parameter pack owes, and one atom kind's machinery

The machineries above the combinators take their parameters in a *pack*
(`DescriptiveComplexity.Draw.StageArgs`, `TagArgs`, `ElemArgs`), so what they
owe the interpretation is stated pack by pack. A pack's fields split in two:
the **static** ones – which slot a trip walks, which block it names, where the
coordinate loop lives – must not depend on the instance at all
(`DescriptiveComplexity.Draw.UConst`), since they are what the emitted formula
is built from; the **dynamic** ones are guards and control updates, and owe the
usual three obligations.

With the three pack statements, an atom kind's machinery
(`DescriptiveComplexity.Draw.Data.kindRule`) is definable one constructor at
a time: the stage atom's by
`DescriptiveComplexity.Draw.Data.uRulesDefinable_stageRule`, an expansion
atom's by the tag-branched statement, an equality's and an order atom's by the
element loop's.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {Q W P : Type} [Fintype Q] [Fintype W]

/-- **A field that does not depend on the instance**: what a static parameter
of a pack owes, the emitted formula being built from it. -/
def UConst {α : Type} (F : Env L → α) : Prop := ∃ a : α, ∀ e : Env L, F e = a

/-! ### An element loop's pack -/

/-- **What an element loop's pack owes.** -/
structure UElemArgsDef {nr : ℕ} (args : ∀ e : Env L, ElemArgs e.α Q W nr) : Prop where
  /-- The tracks it walks are the same at every instance. -/
  rdTrack : UConst fun e => (args e).rdTrack
  /-- Each leaf's name guard is definable. -/
  MatchOf : ∀ j : Fin nr, UGDefinable fun e => (args e).MatchOf j
  /-- And so is each leaf's filing. -/
  setFlag : ∀ (j : Fin nr) (b : Bool), UStDefinable fun e => (args e).setFlag j b
  /-- The three folds are definable. -/
  initEl : UStDefinable fun e => (args e).initEl
  /-- Advancing and folding. -/
  advEl : UStDefinable fun e => (args e).advEl
  /-- The final fold. -/
  exitSt : UStDefinable fun e => (args e).exitSt
  /-- And the exhaustion test. -/
  IsMaxEl : UGDefinable fun e f (_ : W → e.α) => (args e).IsMaxEl f

theorem uRulesDefinable_elemArgs {nr : ℕ} {wk rg : W} {emb : ElemPh nr → P}
    {exitPh : P} {args : ∀ e : Env L, ElemArgs e.α Q W nr}
    (h : UElemArgsDef args) :
    URulesDefinable fun e =>
      elemRule e.one wk rg emb (args e).rdTrack (args e).MatchOf
        (args e).setFlag (args e).initEl (args e).advEl (args e).exitSt
        (args e).IsMaxEl exitPh := by
  obtain ⟨t, ht0⟩ := h.rdTrack
  have ht : ∀ e : Env L, (args e).rdTrack = t := ht0
  intro i ρ
  exact URuleDefinable.congr
    (uRulesDefinable_elemRule (wk := wk) (rg := rg) (emb := emb) (rdTrack := t)
      (exitPh := exitPh) (MatchOf := fun j e => (args e).MatchOf j)
      (setFlag := fun e => (args e).setFlag) (initEl := fun e => (args e).initEl)
      (advEl := fun e => (args e).advEl) (exitSt := fun e => (args e).exitSt)
      (IsMaxEl := fun e => (args e).IsMaxEl)
      h.MatchOf h.setFlag h.initEl h.advEl h.exitSt h.IsMaxEl i ρ)
    fun e => by simp only [ht]

/-! ### A tag-branched machinery's pack -/

/-- **What a tag-branched machinery's pack owes.** -/
structure UTagArgsDef {m : ℕ} {T : Type} {nrOf : T → ℕ}
    (args : ∀ e : Env L, TagArgs e.α Q W m T nrOf) : Prop where
  /-- The witness tracks are the same at every instance. -/
  rdTrackT : UConst fun e => (args e).rdTrackT
  /-- Each witness read's name guard is definable. -/
  MatchT : ∀ i : Fin m, UGDefinable fun e => (args e).MatchT i
  /-- And so is its filing. -/
  setTagFlag : ∀ (i : Fin m) (b : Bool),
    UStDefinable fun e => (args e).setTagFlag i b
  /-- The branch's decoding is definable. -/
  TagsAre : ∀ τ : T, UGDefinable fun e f (_ : W → e.α) => (args e).TagsAre τ f
  /-- The leaf tracks are the same at every instance. -/
  rdTrackE : UConst fun e => (args e).rdTrackE
  /-- Each leaf's name guard is definable. -/
  MatchE : ∀ (τ : T) (j : Fin (nrOf τ)), UGDefinable fun e => (args e).MatchE τ j
  /-- And so is its filing. -/
  setFlagE : ∀ (τ : T) (j : Fin (nrOf τ)) (b : Bool),
    UStDefinable fun e => (args e).setFlagE τ j b
  /-- The three folds are definable, per branch. -/
  initEl : ∀ τ : T, UStDefinable fun e => (args e).initEl τ
  /-- Advancing and folding. -/
  advEl : ∀ τ : T, UStDefinable fun e => (args e).advEl τ
  /-- The final fold. -/
  exitSt : ∀ τ : T, UStDefinable fun e => (args e).exitSt τ
  /-- And the exhaustion test. -/
  IsMaxEl : ∀ τ : T,
    UGDefinable fun e f (_ : W → e.α) => (args e).IsMaxEl τ f

theorem uRulesDefinable_tagArgs {m : ℕ} {T : Type} {nrOf : T → ℕ} {wk rg : W}
    {emb : TagPh m T nrOf → P} {exitPh : P}
    {args : ∀ e : Env L, TagArgs e.α Q W m T nrOf} (h : UTagArgsDef args) :
    URulesDefinable fun e =>
      tagRule e.one wk rg emb (args e).rdTrackT (args e).MatchT
        (args e).setTagFlag (args e).TagsAre (args e).rdTrackE (args e).MatchE
        (args e).setFlagE (args e).initEl (args e).advEl (args e).exitSt
        (args e).IsMaxEl exitPh := by
  obtain ⟨tT, htT0⟩ := h.rdTrackT
  obtain ⟨tE, htE0⟩ := h.rdTrackE
  have htT : ∀ e : Env L, (args e).rdTrackT = tT := htT0
  have htE : ∀ e : Env L, (args e).rdTrackE = tE := htE0
  intro i ρ
  exact URuleDefinable.congr
    (uRulesDefinable_tagRule (wk := wk) (rg := rg) (emb := emb) (rdTrackT := tT)
      (rdTrackE := tE) (exitPh := exitPh)
      (MatchT := fun i e => (args e).MatchT i)
      (setTagFlag := fun e => (args e).setTagFlag)
      (TagsAre := fun e => (args e).TagsAre)
      (MatchE := fun τ j e => (args e).MatchE τ j)
      (setFlagE := fun e => (args e).setFlagE)
      (initEl := fun e => (args e).initEl) (advEl := fun e => (args e).advEl)
      (exitSt := fun e => (args e).exitSt) (IsMaxEl := fun e => (args e).IsMaxEl)
      h.MatchT h.setTagFlag h.TagsAre h.MatchE h.setFlagE h.initEl h.advEl
      h.exitSt h.IsMaxEl i ρ)
    fun e => by simp only [htT, htE]

/-! ### A stage atom's pack, and an atom kind's machinery -/

namespace Data

variable {dt : Data L} [Fintype dt.SlotIx]

/-- **What a stage atom's pack owes.** -/
structure UStageArgsDef {k : ℕ}
    (args : ∀ e : Env L,
      StageArgs e.α Q dt.SlotIx (Fin dt.ko ⊕ Fin dt.ki) dt.dd0 k) : Prop where
  /-- The source tracks are the same at every instance. -/
  srcTrack : UConst fun e => (args e).srcTrack
  /-- And so are the two block families. -/
  srcBlk : UConst fun e => (args e).srcBlk
  /-- The target's among them. -/
  dstBlk : UConst fun e => (args e).dstBlk
  /-- And the coordinate loop's control location. -/
  coord : UConst fun e => (args e).coord
  /-- and the stage track read under the head. -/
  oldSlot : UConst fun e => (args e).oldSlot
  /-- The copied bit is definable. -/
  bitFlag : UGDefinable fun e f (_ : dt.SlotIx → e.α) => (args e).bitFlag f
  /-- And so is its filing. -/
  setBit : ∀ b : Bool, UStDefinable fun e => (args e).setBit b
  /-- The coordinate loop's two updates are definable. -/
  initLv : UStDefinable fun e => (args e).initLv
  /-- The advance among them. -/
  advLv : UStDefinable fun e => (args e).advLv
  /-- With its exhaustion test. -/
  IsMaxLv : UGDefinable fun e f (_ : dt.SlotIx → e.α) => (args e).IsMaxLv f
  /-- and the verdict's filing. -/
  setAv : ∀ b : Bool, UStDefinable fun e => (args e).setAv b

theorem uRulesDefinable_stageArgs {k : ℕ} {emb : StagePh k → P} {exitPh : P}
    {args : ∀ e : Env L,
      StageArgs e.α Q dt.SlotIx (Fin dt.ko ⊕ Fin dt.ki) dt.dd0 k}
    (h : UStageArgsDef args) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.stageRule e.zero e.one emb (args e).srcTrack (args e).srcBlk
        (args e).dstBlk (args e).coord (args e).bitFlag (args e).setBit
        (args e).initLv (args e).advLv (args e).IsMaxLv (args e).oldSlot
        (args e).setAv exitPh := by
  obtain ⟨sT, hsT0⟩ := h.srcTrack
  obtain ⟨sB, hsB0⟩ := h.srcBlk
  obtain ⟨dB, hdB0⟩ := h.dstBlk
  obtain ⟨co, hco0⟩ := h.coord
  obtain ⟨os, hos0⟩ := h.oldSlot
  have hsT : ∀ e : Env L, (args e).srcTrack = sT := hsT0
  have hsB : ∀ e : Env L, (args e).srcBlk = sB := hsB0
  have hdB : ∀ e : Env L, (args e).dstBlk = dB := hdB0
  have hco : ∀ e : Env L, (args e).coord = co := hco0
  have hos : ∀ e : Env L, (args e).oldSlot = os := hos0
  intro i ρ
  exact URuleDefinable.congr
    (uRulesDefinable_stageRule (emb := emb) (srcTrack := sT) (srcBlk := sB)
      (dstBlk := dB) (coord := co) (oldSlot := os) (exitPh := exitPh)
      (bitFlag := fun e => (args e).bitFlag) (setBit := fun e => (args e).setBit)
      (initLv := fun e => (args e).initLv) (advLv := fun e => (args e).advLv)
      (IsMaxLv := fun e => (args e).IsMaxLv) (setAv := fun e => (args e).setAv)
      h.bitFlag h.setBit h.initLv h.advLv h.IsMaxLv h.setAv i ρ)
    fun e => by simp only [hsT, hsB, hdB, hco, hos]

/-- **What an atom kind's pack owes**, one constructor at a time. -/
noncomputable def UKindArgsDef {n : ℕ} :
    ∀ κ : MatAtom dt.X dt.d.B n,
      (∀ e : Env L, dt.KindArgs (A := e.α) (Q := Q) κ) → Prop
  | .stage _ _, args => UStageArgsDef args
  | @MatAtom.exp _ _ _ _ _ _ _, args =>
    letI := Fintype.ofFinite dt.X.Tag
    UTagArgsDef args
  | .eq _ _, args => UElemArgsDef args
  | .ord _ _, args => UElemArgsDef args

/-- **An atom kind's machinery is definable**, given its pack: the stage
atom's by its own statement, an expansion atom's by the tag-branched one, an
equality's and an order atom's by the element loop's. -/
theorem uRulesDefinable_kindRule {n : ℕ} (κ : MatAtom dt.X dt.d.B n)
    {args : ∀ e : Env L, dt.KindArgs (A := e.α) (Q := Q) κ}
    {emb : dt.KindPh κ → P} {exitPh : P} (h : UKindArgsDef κ args) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.kindRule e.zero e.one κ (args e) emb exitPh := by
  match κ with
  | .stage _i _ts => exact uRulesDefinable_stageArgs h
  | @MatAtom.exp _ _ _ _ _k _e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    exact uRulesDefinable_tagArgs h
  | .eq _j₁ _j₂ => exact uRulesDefinable_elemArgs h
  | .ord _j₁ _j₂ => exact uRulesDefinable_elemArgs h

end Data

end Draw

end DescriptiveComplexity
