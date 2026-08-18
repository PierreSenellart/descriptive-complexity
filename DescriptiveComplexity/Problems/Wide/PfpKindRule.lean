/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTower

/-!
# The rules of an atom's machinery, dispatched by its kind

One atom of a step matrix gets the machinery its kind names: a stage atom
the random access of
`DescriptiveComplexity.Problems.Wide.PfpStageAtom`, an expansion atom the
tag-branched loops of `DescriptiveComplexity.Problems.Wide.PfpTagged`, a
comparison the coordinate loop of
`DescriptiveComplexity.Problems.Wide.PfpElem`. This file is the dispatch:
per kind a **parameter pack** (`DescriptiveComplexity.Pfp.StageArgs` and
friends) mirroring the machinery's semantic parameters – the matches, the
control updates, the loop operations, and for the tag branch its
exclusivity proof – then
`DescriptiveComplexity.Pfp.PfpData.kindRule`/`kindSep`/`kindEntry`:
the rules, their separation, and the machinery's entry phase.

The packs keep the semantic content where it belongs – it is fixed with
the runs – while the shapes and their separation are closed here: `kindSep`
needs nothing beyond the packs and the embedding's injectivity.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The parameter packs -/

/-- **The parameters of a stage atom's machinery** (see
`DescriptiveComplexity.Pfp.PfpData.stageRule`). -/
structure StageArgs (A Q W KB : Type) (dd0 k : ℕ) : Type where
  /-- The source track of each argument position. -/
  srcTrack : Fin k → W
  /-- The source block of each argument position. -/
  srcBlk : Fin k → KB
  /-- The target block of each argument position. -/
  dstBlk : Fin k → KB
  /-- The control location of the coordinate loop. -/
  coord : Fin dd0 → Q
  /-- The copied bit, read back from the control. -/
  bitFlag : (Q → A) → Prop
  /-- Storing the read bit. -/
  setBit : Bool → (Q → A) → (W → A) → Q → A
  /-- Initializing the coordinate loop. -/
  initLv : (Q → A) → (W → A) → Q → A
  /-- Advancing the coordinate loop. -/
  advLv : (Q → A) → (W → A) → Q → A
  /-- The coordinate loop is exhausted. -/
  IsMaxLv : (Q → A) → Prop
  /-- The stage track read under the head. -/
  oldSlot : W
  /-- Storing the atom's verdict. -/
  setAv : Bool → (Q → A) → (W → A) → Q → A

/-- **The parameters of a tag-branched machinery** (see
`DescriptiveComplexity.Pfp.tagRule`), with the branch's exclusivity
proof. -/
structure TagArgs (A Q W : Type) (m : ℕ) (T : Type) (nrOf : T → ℕ) : Type where
  /-- The track of each witness read. -/
  rdTrackT : Fin m → W
  /-- The name guard of each witness read. -/
  MatchT : Fin m → (Q → A) → (W → A) → Prop
  /-- Storing a witness bit. -/
  setTagFlag : Fin m → Bool → (Q → A) → (W → A) → Q → A
  /-- The branch's decoding. -/
  TagsAre : T → (Q → A) → Prop
  /-- The decoding is exclusive. -/
  hTags : ∀ (τ τ' : T) (f : Q → A), TagsAre τ f → TagsAre τ' f → τ = τ'
  /-- The track of each leaf read, per branch. -/
  rdTrackE : (τ : T) → Fin (nrOf τ) → W
  /-- The name guard of each leaf read, per branch. -/
  MatchE : (τ : T) → Fin (nrOf τ) → (Q → A) → (W → A) → Prop
  /-- Storing a leaf bit. -/
  setFlagE : (τ : T) → Fin (nrOf τ) → Bool → (Q → A) → (W → A) → Q → A
  /-- Initializing the loop and accumulators. -/
  initEl : T → (Q → A) → (W → A) → Q → A
  /-- Advancing and folding. -/
  advEl : T → (Q → A) → (W → A) → Q → A
  /-- The final fold. -/
  exitSt : T → (Q → A) → (W → A) → Q → A
  /-- The loop is exhausted. -/
  IsMaxEl : T → (Q → A) → Prop

/-- **The parameters of a plain element loop** (see
`DescriptiveComplexity.Pfp.elemRule`). -/
structure ElemArgs (A Q W : Type) (nr : ℕ) : Type where
  /-- The track of each leaf read. -/
  rdTrack : Fin nr → W
  /-- The name guard of each leaf read. -/
  MatchOf : Fin nr → (Q → A) → (W → A) → Prop
  /-- Storing a leaf bit. -/
  setFlag : Fin nr → Bool → (Q → A) → (W → A) → Q → A
  /-- Initializing the loop and accumulators. -/
  initEl : (Q → A) → (W → A) → Q → A
  /-- Advancing and folding. -/
  advEl : (Q → A) → (W → A) → Q → A
  /-- The final fold. -/
  exitSt : (Q → A) → (W → A) → Q → A
  /-- The loop is exhausted. -/
  IsMaxEl : (Q → A) → Prop

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q P : Type}

/-- **The parameter pack of an atom kind's machinery.** -/
noncomputable def KindArgs {n : ℕ} : MatAtom dt.X dt.d.B n → Type
  | .stage i _ =>
    StageArgs A Q dt.SlotIx (Fin dt.ko ⊕ Fin dt.ki) dt.dd0 (dt.d.B.arity i)
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    TagArgs A Q dt.SlotIx (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag)
      (dt.relNr e)
  | .eq _ _ => ElemArgs A Q dt.SlotIx 2
  | .ord _ _ => ElemArgs A Q dt.SlotIx 2

/-- **The entry phase of an atom kind's machinery**: the machinery's own
first phase – for an expansion atom the *first witness read*, so the tag
chain is entered, not skipped (the branch checkpoint only when there is no
read at all). -/
noncomputable def kindEntry {n : ℕ} :
    ∀ κ : MatAtom dt.X dt.d.B n, dt.KindPh κ
  | .stage _ _ => .savP .up
  | @MatAtom.exp _ _ _ _ k _ _ =>
    letI := Fintype.ofFinite dt.X.Tag
    if h : 0 < k * Fintype.card dt.X.Tag then .tagRdP ⟨0, h⟩ .start else .brP
  | .eq _ _ => .e0
  | .ord _ _ => .e0

variable (zero one : A)

/-- **The rules of an atom kind's machinery**, at its parameter pack. -/
noncomputable def kindRule {n : ℕ} :
    ∀ (κ : MatAtom dt.X dt.d.B n) (_args : dt.KindArgs (A := A) (Q := Q) κ)
      (_emb : dt.KindPh κ → P) (_exitPh : P)
      (s : dt.KindSite κ), dt.KindSh κ s → Rule A Q dt.SlotIx P
  | .stage _i _, args, emb, exitPh =>
    dt.stageRule zero one emb args.srcTrack args.srcBlk args.dstBlk
      args.coord args.bitFlag args.setBit args.initLv args.advLv
      args.IsMaxLv args.oldSlot args.setAv exitPh
  | @MatAtom.exp _ _ _ _ _k _e _, args, emb, exitPh =>
    letI := Fintype.ofFinite dt.X.Tag
    tagRule one Slot.wk Slot.reg emb args.rdTrackT args.MatchT
      args.setTagFlag args.TagsAre args.rdTrackE args.MatchE args.setFlagE
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh
  | .eq _ _, args, emb, exitPh =>
    elemRule one Slot.wk Slot.reg emb args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh
  | .ord _ _, args, emb, exitPh =>
    elemRule one Slot.wk Slot.reg emb args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh

variable {dt}

/-- **A property of an atom kind's phases and its exit holds of every phase it
can move to**: whichever kind it is, its machinery stays inside its own phases
and only its verdict leaves. This is what a determinism-after-the-guess argument
asks of an atom (`DescriptiveComplexity.Pfp.PfpData.nexProg_uniqueFrom`). -/
theorem kindDstIn {S : P → Prop} {n : ℕ}
    (κ : MatAtom dt.X dt.d.B n) (args : dt.KindArgs (A := A) (Q := Q) κ)
    {emb : dt.KindPh κ → P} (exitPh : P)
    (hemb : ∀ p : dt.KindPh κ, S (emb p)) (hexit : S exitPh) :
    ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      S (dt.kindRule zero one κ args emb exitPh s ρ).dstPh := by
  match κ with
  | .stage _i _ts =>
    exact fun s ρ => dt.stageRule_dstIn zero one args.srcTrack args.srcBlk
      args.dstBlk args.coord args.bitFlag args.setBit args.initLv args.advLv
      args.IsMaxLv args.oldSlot args.setAv exitPh hemb hexit s ρ
  | @MatAtom.exp _ _ _ _ _k _e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    exact fun s ρ => tagRule_dstIn one Slot.wk Slot.reg args.rdTrackT args.MatchT
      args.setTagFlag args.TagsAre args.rdTrackE args.MatchE args.setFlagE
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb hexit s ρ
  | .eq _j₁ _j₂ =>
    exact fun s ρ => elemRule_dstIn one Slot.wk Slot.reg args.rdTrack args.MatchOf
      args.setFlag args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb
      hexit s ρ
  | .ord _j₁ _j₂ =>
    exact fun s ρ => elemRule_dstIn one Slot.wk Slot.reg args.rdTrack args.MatchOf
      args.setFlag args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb
      hexit s ρ

/-- **Every rule of an atom kind's machinery fires from a phase its site
owns.** -/
theorem kindHosrc {n : ℕ}
    (κ : MatAtom dt.X dt.d.B n) (args : dt.KindArgs (A := A) (Q := Q) κ)
    {emb : dt.KindPh κ → P} (exitPh : P) :
    ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      ∃ p : dt.KindPh κ,
        (dt.kindRule zero one κ args emb exitPh s ρ).srcPh = emb p ∧
          dt.kindOwn κ p = s := by
  match κ with
  | .stage _i _ts =>
    exact dt.stageHosrc zero one args.srcTrack args.srcBlk args.dstBlk
      args.coord args.bitFlag args.setBit args.initLv args.advLv
      args.IsMaxLv args.oldSlot args.setAv exitPh
  | @MatAtom.exp _ _ _ _ _k _e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    exact tagHosrc one Slot.wk Slot.reg args.rdTrackT args.MatchT
      args.setTagFlag args.TagsAre args.rdTrackE args.MatchE args.setFlagE
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh
  | .eq _j₁ _j₂ =>
    exact elemHosrc one Slot.wk Slot.reg args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh
  | .ord _j₁ _j₂ =>
    exact elemHosrc one Slot.wk Slot.reg args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh

/-- **An atom kind's machinery separates in-shape.** -/
theorem kindSep (hzo : zero ≠ one) {n : ℕ}
    (κ : MatAtom dt.X dt.d.B n) (args : dt.KindArgs (A := A) (Q := Q) κ)
    {emb : dt.KindPh κ → P} (hemb : Function.Injective emb) (exitPh : P) :
    ∀ (s : dt.KindSite κ) (ρ ρ' : dt.KindSh κ s) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.kindRule zero one κ args emb exitPh s ρ).guard f g →
      (dt.kindRule zero one κ args emb exitPh s ρ').guard f g →
      (dt.kindRule zero one κ args emb exitPh s ρ).srcPh =
        (dt.kindRule zero one κ args emb exitPh s ρ').srcPh →
      ρ = ρ' := by
  match κ with
  | .stage _i _ts =>
    exact dt.stageSep zero one args.srcTrack args.srcBlk args.dstBlk
      args.coord args.bitFlag args.setBit args.initLv args.advLv
      args.IsMaxLv args.oldSlot args.setAv exitPh hzo hemb
  | @MatAtom.exp _ _ _ _ _k _e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    exact tagSep one Slot.wk Slot.reg args.rdTrackT args.MatchT
      args.setTagFlag args.TagsAre args.rdTrackE args.MatchE args.setFlagE
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb args.hTags
  | .eq _j₁ _j₂ =>
    exact elemSep one Slot.wk Slot.reg args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb
  | .ord _j₁ _j₂ =>
    exact elemSep one Slot.wk Slot.reg args.rdTrack args.MatchOf args.setFlag
      args.initEl args.advEl args.exitSt args.IsMaxEl exitPh hemb

end PfpData

end Pfp

end DescriptiveComplexity
