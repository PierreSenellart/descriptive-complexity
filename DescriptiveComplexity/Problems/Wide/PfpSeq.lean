/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpChain

/-!
# The sequencer: heterogeneous stages in a row

The matrix of a step formula is evaluated atom by atom, and the gates block
by block: a **sequence** of machineries of different shapes – a stage
atom's random access here, a tag-branched element loop there – with a
checkpoint between consecutive ones and an exit after the last. The chain
combinator of `DescriptiveComplexity.Problems.Wide.PfpChain` fixes a single
stage family; this file is its dependent sibling: `n` stages with their own
phase and shape types (`PA`/`SA`-indexed families), `n + 1` checkpoints,
the `k`-th dispatching into stage `k`'s entry and the last leaving.

The per-stage machineries and their separation are parameters, so the
matrix instantiates this with the kind-dependent atom machineries and the
gates with the per-block gate machinery, and neither needs a new
checkpoint proof.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The phases of a sequence**: `n + 1` checkpoints and the stages'. -/
inductive SeqPh (n : ℕ) (PA : Fin n → Type) : Type
  /-- The checkpoint before stage `k` (at `k = n`: after the last). -/
  | chk : Fin (n + 1) → SeqPh n PA
  /-- A phase of stage `a`. -/
  | sub : (a : Fin n) → PA a → SeqPh n PA

/-- **The sites of a sequence.** -/
inductive SeqSite (n : ℕ) (SA : Fin n → Type) : Type
  /-- A checkpoint site. -/
  | chk : Fin (n + 1) → SeqSite n SA
  /-- A site of stage `a`. -/
  | sub : (a : Fin n) → SA a → SeqSite n SA

/-- **The rule shape of each sequence site.** -/
def SeqSh (n : ℕ) {SA : Fin n → Type} (ShA : ∀ a : Fin n, SA a → Type) :
    SeqSite n SA → Type
  | .chk _ => EvalChkRule
  | .sub a s => ShA a s

/-- **The owner of each phase of a sequence**, over the stages' owners. -/
def seqOwn {n : ℕ} {PA : Fin n → Type} {SA : Fin n → Type}
    (ownA : ∀ a : Fin n, PA a → SA a) : SeqPh n PA → SeqSite n SA
  | .chk k => .chk k
  | .sub a p => .sub a (ownA a p)

section Rules

variable {A Q W P : Type} {n : ℕ} {PA : Fin n → Type} {SA : Fin n → Type}
variable {ShA : ∀ a : Fin n, SA a → Type}
variable (one : A) (wk rg : W)
variable (emb : SeqPh n PA → P)
variable (ruleA : ∀ (a : Fin n) (s : SA a), ShA a s → Rule A Q W P)
variable (entry : ∀ a : Fin n, PA a)
variable (enterSt : Fin n → (Q → A) → (W → A) → (Q → A))
variable (exitPh : P)

/-- **The rules of a sequence**: per checkpoint the walk back and the
dispatch – into the next stage's entry, or out after the last. -/
def seqRule : ∀ i : SeqSite n SA, SeqSh n ShA i → Rule A Q W P
  | .chk k, .stay =>
    { guard := fun _ g => g wk ≠ one
      srcPh := emb (.chk k)
      dstPh := emb (.chk k)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .chk k, .dspA =>
    if hk : (k : ℕ) < n then
      { guard := fun _ g => g wk = one ∧ g rg ≠ one
        srcPh := emb (.chk k)
        dstPh := emb (.sub ⟨(k : ℕ), hk⟩ (entry ⟨(k : ℕ), hk⟩))
        dstSt := enterSt ⟨(k : ℕ), hk⟩
        wr := fun _ g => g
        moveRight := True }
    else
      { guard := fun _ g => g wk = one ∧ g rg ≠ one
        srcPh := emb (.chk k)
        dstPh := exitPh
        dstSt := fun f _ => f
        wr := fun _ g => g
        moveRight := True }
  | .chk k, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb (.chk k)
      dstPh := emb (.chk k)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .sub a s, ρ => ruleA a s ρ

/-- **Every rule of a sequence fires from a phase its site owns**; the
stages' obligation is the parameter. -/
theorem seqHosrc (ownA : ∀ a : Fin n, PA a → SA a)
    (hosrcA : ∀ (a : Fin n) (s : SA a) (ρ : ShA a s),
      ∃ p : PA a, (ruleA a s ρ).srcPh = emb (.sub a p) ∧ ownA a p = s) :
    ∀ (i : SeqSite n SA) (ρ : SeqSh n ShA i),
      ∃ p : SeqPh n PA,
        (seqRule one wk rg emb ruleA entry enterSt exitPh i ρ).srcPh = emb p ∧
          seqOwn ownA p = i := by
  intro i ρ
  match i, ρ with
  | .chk k, .stay => exact ⟨.chk k, rfl, rfl⟩
  | .chk k, .dspA =>
    by_cases hk : (k : ℕ) < n
    · exact ⟨.chk k, by simp [seqRule, hk], rfl⟩
    · exact ⟨.chk k, by simp [seqRule, hk], rfl⟩
  | .chk k, .dspB => exact ⟨.chk k, rfl, rfl⟩
  | .sub a s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcA a s ρ
    exact ⟨.sub a p, hp, congrArg (SeqSite.sub a) ho⟩

/-- **A sequence separates in-shape**: the checkpoints by the gadget's
guards, the stages by their parameter. -/
theorem seqSep
    (hsepA : ∀ (a : Fin n) (s : SA a) (ρ ρ' : ShA a s) (f : Q → A) (g : W → A),
      (ruleA a s ρ).guard f g → (ruleA a s ρ').guard f g →
      (ruleA a s ρ).srcPh = (ruleA a s ρ').srcPh → ρ = ρ') :
    ∀ (i : SeqSite n SA) (ρ ρ' : SeqSh n ShA i) (f : Q → A) (g : W → A),
      (seqRule one wk rg emb ruleA entry enterSt exitPh i ρ).guard f g →
      (seqRule one wk rg emb ruleA entry enterSt exitPh i ρ').guard f g →
      (seqRule one wk rg emb ruleA entry enterSt exitPh i ρ).srcPh =
        (seqRule one wk rg emb ruleA entry enterSt exitPh i ρ').srcPh →
      ρ = ρ' := by
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .chk k, .stay, .stay => rfl
  | .chk k, .dspA, .dspA => rfl
  | .chk k, .dspB, .dspB => rfl
  | .chk k, .stay, .dspA =>
    by_cases hk : (k : ℕ) < n
    · simp only [seqRule, dif_pos hk] at hg'
      simp only [seqRule] at hg
      exact absurd hg'.1 hg
    · simp only [seqRule, dif_neg hk] at hg'
      simp only [seqRule] at hg
      exact absurd hg'.1 hg
  | .chk k, .dspA, .stay =>
    by_cases hk : (k : ℕ) < n
    · simp only [seqRule, dif_pos hk] at hg
      simp only [seqRule] at hg'
      exact absurd hg.1 hg'
    · simp only [seqRule, dif_neg hk] at hg
      simp only [seqRule] at hg'
      exact absurd hg.1 hg'
  | .chk k, .stay, .dspB => exact hg'.elim
  | .chk k, .dspB, .stay => exact hg.elim
  | .chk k, .dspA, .dspB => exact hg'.elim
  | .chk k, .dspB, .dspA => exact hg.elim
  | .sub a s, ρ, ρ' => exact hsepA a s ρ ρ' f g hg hg' hph

end Rules

end Pfp

end DescriptiveComplexity
