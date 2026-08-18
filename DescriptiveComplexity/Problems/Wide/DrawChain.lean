/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawEval

/-!
# The chain combinator: checkpoints around abstract stages

The outer program, the evaluation's spine and one variable's machinery all
repeat one pattern: **checkpoints** – a phase whose stay rule walks left to
the working-cell marker and whose dispatch rules fire there – between
**stages** that are kit instances or further abstract blocks. The remaining
machinery (the gates, the per-atom subroutines, the tuple and element
loops) is more of the same, so this file is the pattern as a combinator,
built once:

* `DescriptiveComplexity.Draw.PreRule` – a rule without its source phase,
  what a dispatch descriptor is;
* `DescriptiveComplexity.Draw.ChainPh`/`ChainSite`/`ChainSh` – `n`
  checkpoints (each carrying the three-rule gadget of
  `DescriptiveComplexity.Draw.EvalChkRule`) plus an abstract stage family;
* `DescriptiveComplexity.Draw.chainRule` – the rules, the dispatches given
  as **descriptors** per checkpoint (`Fin n → Bool → PreRule`): a
  descriptor's target may be any phase, so loops – a tuple loop's back edge
  – cost nothing;
* `DescriptiveComplexity.Draw.chainSep`/`chainHosrc` – separation and
  ownership, from two per-checkpoint hypotheses: every dispatch fires only
  at the marker, and the two dispatches of a checkpoint never fire
  together.

A machinery block is then a stage family (its kits, with their `sep` and
`exit_disjoint`) plus a descriptor list, and nothing else.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Rules without their source phase -/

/-- **A rule without its source phase**: what a chain's dispatch descriptor
is – the checkpoint it belongs to supplies the source. -/
structure PreRule (A Q W P : Type) where
  /-- When the rule applies. -/
  guard : (Q → A) → (W → A) → Prop
  /-- The phase the rule moves to. -/
  dstPh : P
  /-- The pointer the rule leaves in the control. -/
  dstSt : (Q → A) → (W → A) → (Q → A)
  /-- The tracks the rule writes. -/
  wr : (Q → A) → (W → A) → (W → A)
  /-- Whether the rule moves the head right. -/
  moveRight : Prop

/-- A descriptor, at a source phase. -/
def PreRule.toRule {A Q W P : Type} (r : PreRule A Q W P) (p : P) :
    Rule A Q W P :=
  { guard := r.guard
    srcPh := p
    dstPh := r.dstPh
    dstSt := r.dstSt
    wr := r.wr
    moveRight := r.moveRight }

/-! ### The chain's shapes -/

/-- **The phases of a chain**: `n` checkpoints, and the stages'. -/
inductive ChainPh (n : ℕ) (PS : Type) : Type
  /-- A checkpoint. -/
  | chk : Fin n → ChainPh n PS
  /-- A stage phase. -/
  | sub : PS → ChainPh n PS

instance {n : ℕ} {PS : Type} [Finite PS] : Finite (ChainPh n PS) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin n ⊕ PS)
      | .sub p => Sum.inr p)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The sites of a chain.** -/
inductive ChainSite (n : ℕ) (SS : Type) : Type
  /-- A checkpoint site. -/
  | chk : Fin n → ChainSite n SS
  /-- A stage site. -/
  | sub : SS → ChainSite n SS

/-- **The rule shape of each chain site**: checkpoints carry the three-rule
gadget, stages their own shapes. -/
def ChainSh (n : ℕ) (SS : Type) (ShS : SS → Type) : ChainSite n SS → Type
  | .chk _ => EvalChkRule
  | .sub s => ShS s

/-! ### The rules -/

section Rules

variable {A Q W P PS SS : Type} {n : ℕ} {ShS : SS → Type}

/-- **The rules of a chain**: per checkpoint the walk back to the marker and
its two dispatch descriptors; the stages' rules are the parameter. -/
def chainRule (one : A) (wk : W)
    (emb : ChainPh n PS → P)
    (ruleS : ∀ s : SS, ShS s → Rule A Q W P)
    (dsp : Fin n → Bool → PreRule A Q W P) :
    ∀ i : ChainSite n SS, ChainSh n SS ShS i → Rule A Q W P
  | .chk k, .stay =>
    { guard := fun _ g => g wk ≠ one
      srcPh := emb (.chk k)
      dstPh := emb (.chk k)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .chk k, .dspA => (dsp k false).toRule (emb (.chk k))
  | .chk k, .dspB => (dsp k true).toRule (emb (.chk k))
  | .sub s, ρ => ruleS s ρ

variable {one : A} {wk : W} {emb : ChainPh n PS → P}
variable {ruleS : ∀ s : SS, ShS s → Rule A Q W P}
variable {dsp : Fin n → Bool → PreRule A Q W P}

/-- **A property of a chain's phases and its dispatches' destinations holds of
every phase it can move to**: the checkpoints stay where they are, the
dispatches go where their descriptors say, and the stages are the parameter.
This is what a determinism-after-the-guess argument asks of a sequenced
machinery (`DescriptiveComplexity.Draw.Data.nexProg_uniqueFrom`). -/
theorem chainRule_dstIn {S : P → Prop} (hemb : ∀ p : ChainPh n PS, S (emb p))
    (hdsp : ∀ (k : Fin n) (b : Bool), S (dsp k b).dstPh)
    (hS : ∀ (s : SS) (ρ : ShS s), S (ruleS s ρ).dstPh)
    (i : ChainSite n SS) (ρ : ChainSh n SS ShS i) :
    S (chainRule one wk emb ruleS dsp i ρ).dstPh := by
  match i, ρ with
  | .chk k, .stay => exact hemb _
  | .chk k, .dspA => exact hdsp k false
  | .chk k, .dspB => exact hdsp k true
  | .sub s, ρ => exact hS s ρ

/-- **A chain separates in-shape**: the stay's guard is disjoint from the
dispatches' – they only fire at the marker – and the two dispatches of a
checkpoint never fire together; the stages' separation is the parameter. -/
theorem chainSep
    (hwk : ∀ (k : Fin n) (b : Bool) (f : Q → A) (g : W → A),
      (dsp k b).guard f g → g wk = one)
    (hAB : ∀ (k : Fin n) (f : Q → A) (g : W → A),
      ¬((dsp k false).guard f g ∧ (dsp k true).guard f g))
    (hsepS : ∀ (s : SS) (ρ ρ' : ShS s) (f : Q → A) (g : W → A),
      (ruleS s ρ).guard f g → (ruleS s ρ').guard f g →
      (ruleS s ρ).srcPh = (ruleS s ρ').srcPh → ρ = ρ') :
    ∀ (i : ChainSite n SS) (ρ ρ' : ChainSh n SS ShS i) (f : Q → A) (g : W → A),
      (chainRule one wk emb ruleS dsp i ρ).guard f g →
      (chainRule one wk emb ruleS dsp i ρ').guard f g →
      (chainRule one wk emb ruleS dsp i ρ).srcPh =
        (chainRule one wk emb ruleS dsp i ρ').srcPh →
      ρ = ρ' := by
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .chk k, .stay, .stay => rfl
  | .chk k, .dspA, .dspA => rfl
  | .chk k, .dspB, .dspB => rfl
  | .chk k, .stay, .dspA => exact absurd (hwk k false f g hg') hg
  | .chk k, .dspA, .stay => exact absurd (hwk k false f g hg) hg'
  | .chk k, .stay, .dspB => exact absurd (hwk k true f g hg') hg
  | .chk k, .dspB, .stay => exact absurd (hwk k true f g hg) hg'
  | .chk k, .dspA, .dspB => exact absurd ⟨hg, hg'⟩ (hAB k f g)
  | .chk k, .dspB, .dspA => exact absurd ⟨hg', hg⟩ (hAB k f g)
  | .sub s, ρ, ρ' => exact hsepS s ρ ρ' f g hg hg' hph

/-- **Every chain rule fires from a phase its site owns**; the stages'
obligation is the parameter. -/
theorem chainHosrc {S' : Type} (site : ChainSite n SS → S')
    (own : ChainPh n PS → S')
    (hownChk : ∀ k : Fin n, own (.chk k) = site (.chk k))
    (hosrcS : ∀ (s : SS) (ρ : ShS s),
      ∃ p : ChainPh n PS, (ruleS s ρ).srcPh = emb p ∧ own p = site (.sub s)) :
    ∀ (i : ChainSite n SS) (ρ : ChainSh n SS ShS i),
      ∃ p : ChainPh n PS,
        (chainRule one wk emb ruleS dsp i ρ).srcPh = emb p ∧ own p = site i := by
  intro i ρ
  match i, ρ with
  | .chk k, .stay => exact ⟨.chk k, rfl, hownChk k⟩
  | .chk k, .dspA => exact ⟨.chk k, rfl, hownChk k⟩
  | .chk k, .dspB => exact ⟨.chk k, rfl, hownChk k⟩
  | .sub s, ρ => exact hosrcS s ρ

end Rules

end Draw

end DescriptiveComplexity
