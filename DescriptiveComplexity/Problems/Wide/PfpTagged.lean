/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpElem

/-!
# Tag-branched element loops: the expansion atoms and the domain gates

An expansion atom's defining sentence – and a block's domain sentence –
depends on the **tags** of its argument points (EXPONENTIAL.md §6.4.4). The
machine reads them first: one named-bit read per argument position and
candidate tag, at the canonical tag-witness cell, the verdicts stored
one-hot in the control. A branch checkpoint then dispatches on the decoded
tag tuple – one dispatch rule per tuple, their guards made exclusive by the
decoding – into that tuple's own element loop
(`DescriptiveComplexity.Problems.Wide.PfpElem`), which evaluates the
sentence's prefix with one leaf read per block atom of its matrix.

The expansion atoms instantiate this at their arity, the domain gates at
one argument. As everywhere, the shapes and separation are fixed here; the
decodings and folds are parameters.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The rules of a branch checkpoint**: the walk back, and one dispatch
per tag tuple. -/
inductive BrRule (T : Type) : Type
  /-- Walk left back to the marker. -/
  | stay : BrRule T
  /-- Dispatch into the tuple's loop. -/
  | dsp : T → BrRule T

/-- **The phases of a tag-branched machinery**: the witness reads, the
branch checkpoint, and one element loop per tag tuple. -/
inductive TagPh (m : ℕ) (T : Type) (nrOf : T → ℕ) : Type
  /-- The `i`-th witness read. -/
  | tagRdP : Fin m → ReadPh → TagPh m T nrOf
  /-- The branch checkpoint. -/
  | brP : TagPh m T nrOf
  /-- A phase of the tuple's element loop. -/
  | loopP : (τ : T) → ElemPh (nrOf τ) → TagPh m T nrOf

/-- **The sites of a tag-branched machinery.** -/
inductive TagSite (m : ℕ) (T : Type) (nrOf : T → ℕ) : Type
  /-- A witness read. -/
  | tagRd : Fin m → TagSite m T nrOf
  /-- The branch checkpoint. -/
  | br : TagSite m T nrOf
  /-- A site of the tuple's element loop. -/
  | loop : (τ : T) → ElemSite (nrOf τ) → TagSite m T nrOf

/-- **The rule shape of each site.** -/
def TagSh (m : ℕ) (T : Type) (nrOf : T → ℕ) : TagSite m T nrOf → Type
  | .tagRd _ => ReadRule ⊕ Bool
  | .br => BrRule T
  | .loop τ s => ElemSh (nrOf τ) s

/-- **The owner of each phase of a tag-branched machinery.** -/
def tagOwn {m : ℕ} {T : Type} {nrOf : T → ℕ} :
    TagPh m T nrOf → TagSite m T nrOf
  | .tagRdP i _ => .tagRd i
  | .brP => .br
  | .loopP τ p => .loop τ (elemOwn p)

section Rules

variable {A Q W P T : Type} {m : ℕ} {nrOf : T → ℕ}
variable (one : A) (wk rg : W)
variable (emb : TagPh m T nrOf → P)
variable (rdTrackT : Fin m → W)
variable (MatchT : Fin m → (Q → A) → (W → A) → Prop)
variable (setTagFlag : Fin m → Bool → (Q → A) → (W → A) → (Q → A))
variable (TagsAre : T → (Q → A) → Prop)
variable (rdTrackE : (τ : T) → Fin (nrOf τ) → W)
variable (MatchE : (τ : T) → Fin (nrOf τ) → (Q → A) → (W → A) → Prop)
variable (setFlagE : (τ : T) → Fin (nrOf τ) → Bool → (Q → A) → (W → A) → (Q → A))
variable (initEl advEl exitSt : T → (Q → A) → (W → A) → (Q → A))
variable (IsMaxEl : T → (Q → A) → Prop)
variable (exitPh : P)

/-- The first witness read's entry, or the branch checkpoint when there is
none. -/
def tagFirstRd : P :=
  if h : 0 < m then emb (.tagRdP ⟨0, h⟩ .start) else emb .brP

/-- The phase after the `i`-th witness read. -/
def tagNextRd (i : Fin m) : P :=
  if h : (i : ℕ) + 1 < m then emb (.tagRdP ⟨(i : ℕ) + 1, h⟩ .start)
  else emb .brP

/-- **The rules of a tag-branched machinery.** -/
def tagRule : ∀ i : TagSite m T nrOf, TagSh m T nrOf i → Rule A Q W P
  | .tagRd i, Sum.inl ρ =>
    (ReadKit.mk (rdTrackT i) wk (MatchT i)
      (fun rp => emb (.tagRdP i rp))).rule one ρ
  | .tagRd i, Sum.inr b =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      srcPh := emb (.tagRdP i (if b then .ry else .rn))
      dstPh := tagNextRd emb i
      dstSt := setTagFlag i b
      wr := fun _ g => g
      moveRight := True }
  | .br, .stay =>
    { guard := fun _ g => g wk ≠ one
      srcPh := emb .brP
      dstPh := emb .brP
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .br, .dsp τ =>
    { guard := fun f g => (g wk = one ∧ g rg ≠ one) ∧ TagsAre τ f
      srcPh := emb .brP
      dstPh := emb (.loopP τ .e0)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .loop τ s, ρ =>
    elemRule one wk rg (fun p => emb (.loopP τ p)) (rdTrackE τ) (MatchE τ)
      (setFlagE τ) (initEl τ) (advEl τ) (exitSt τ) (IsMaxEl τ) exitPh s ρ

variable {emb}

/-- **Every rule of a tag-branched machinery fires from a phase its site
owns**; the loops' obligation is the element loop's. -/
theorem tagHosrc :
    ∀ (i : TagSite m T nrOf) (ρ : TagSh m T nrOf i),
      ∃ p : TagPh m T nrOf,
        (tagRule one wk rg emb rdTrackT MatchT setTagFlag TagsAre rdTrackE
          MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).srcPh =
          emb p ∧ tagOwn p = i := by
  intro i ρ
  match i, ρ with
  | .tagRd i, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .tagRd i, Sum.inr b => cases b <;> exact ⟨_, rfl, rfl⟩
  | .br, .stay => exact ⟨.brP, rfl, rfl⟩
  | .br, .dsp τ => exact ⟨.brP, rfl, rfl⟩
  | .loop τ s, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      elemHosrc one wk rg (rdTrackE τ) (MatchE τ) (setFlagE τ) (initEl τ)
        (advEl τ) (exitSt τ) (IsMaxEl τ) exitPh (emb := fun p => emb (.loopP τ p))
        s ρ
    exact ⟨.loopP τ p, hp, congrArg (TagSite.loop τ) ho⟩

variable (hemb : Function.Injective emb)
variable (hTags : ∀ (τ τ' : T) (f : Q → A), TagsAre τ f → TagsAre τ' f → τ = τ')

include hemb hTags in
/-- **A tag-branched machinery separates in-shape**: the reads by their kit,
the branch's dispatches by the exclusive decoding, the loops by their own
separation. -/
theorem tagSep :
    ∀ (i : TagSite m T nrOf) (ρ ρ' : TagSh m T nrOf i) (f : Q → A) (g : W → A),
      (tagRule one wk rg emb rdTrackT MatchT setTagFlag TagsAre rdTrackE
        MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).guard f g →
      (tagRule one wk rg emb rdTrackT MatchT setTagFlag TagsAre rdTrackE
        MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ').guard f g →
      (tagRule one wk rg emb rdTrackT MatchT setTagFlag TagsAre rdTrackE
        MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ).srcPh =
        (tagRule one wk rg emb rdTrackT MatchT setTagFlag TagsAre rdTrackE
          MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ').srcPh →
      ρ = ρ' := by
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .tagRd i, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ReadKit.sep _ one
      (fun x y h => by cases hemb h; rfl) σ σ' f g hg hg' hph)
  | .tagRd i, Sum.inl σ, Sum.inr b =>
    refine absurd hph (fun hp => ReadKit.exit_disjoint _ one
      (fun x y h => by cases hemb h; rfl) σ f g hg hg'.1 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .tagRd i, Sum.inr b, Sum.inl σ =>
    refine absurd hph.symm (fun hp => ReadKit.exit_disjoint _ one
      (fun x y h => by cases hemb h; rfl) σ f g hg' hg.1 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .tagRd i, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hemb hph
      injection h2 with h3 h4
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .br, .stay, .stay => rfl
  | .br, .dsp τ, .dsp τ' =>
    exact congrArg BrRule.dsp (hTags τ τ' f hg.2 hg'.2)
  | .br, .stay, .dsp τ => exact absurd hg'.1.1 hg
  | .br, .dsp τ, .stay => exact absurd hg.1.1 hg'
  | .loop τ s, ρ, ρ' =>
    exact elemSep one wk rg (rdTrackE τ) (MatchE τ) (setFlagE τ) (initEl τ)
      (advEl τ) (exitSt τ) (IsMaxEl τ) exitPh
      (fun x y h => by cases hemb h; rfl) s ρ ρ' f g hg hg' hph

end Rules

end Pfp

end DescriptiveComplexity
