/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpOuter

/-!
# The evaluation's spine: the per-variable loop

The per-address evaluation the outer program abstracts
(`DescriptiveComplexity.Problems.Wide.PfpOuter`) factors once more, the same
way: a **spine** – one checkpoint per variable position, dispatching into
that variable's machinery and, after the last, back into the outer loop –
around **per-variable sub-machineries** (the gates, the VAL loop, the atom
subroutines, the stage write) that stay abstract here.

A checkpoint phase `chk k` owns two things: the walk back to the marker
(entering rules step right off it, as everywhere in the assembly) and the
dispatch at the marker. For `k < nv` the dispatch enters variable `k`'s
machinery; at `k = nv` it is the pair of outer boundary rules the outer file
promised – erase the marker and step right, into the sweep's advance below
the `ltp` cell, into the post-sweep reset at it. A sub-machinery's final
exit targets the next checkpoint, which is how the spine needs to know
nothing about its internals.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The spine's shapes -/

/-- **The phases of the evaluation**: one checkpoint per variable position
(the last is the return to the outer loop), and the sub-machineries'. -/
inductive EvalPh (nv : ℕ) (PM : Type) : Type
  /-- The checkpoint before variable `k` (at `k = nv`: after the last). -/
  | chk : Fin (nv + 1) → EvalPh nv PM
  /-- A phase of a sub-machinery. -/
  | sub : PM → EvalPh nv PM

instance {nv : ℕ} {PM : Type} [Finite PM] : Finite (EvalPh nv PM) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin (nv + 1) ⊕ PM)
      | .sub p => Sum.inr p)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The sites of the evaluation**: one per checkpoint, and the
sub-machineries'. -/
inductive EvalSite (nv : ℕ) (SM : Type) : Type
  /-- A checkpoint site. -/
  | chk : Fin (nv + 1) → EvalSite nv SM
  /-- A sub-machinery site. -/
  | sub : SM → EvalSite nv SM

/-- **The rules of a checkpoint**: the walk back to the marker, and the two
dispatches (the second is only live at the last checkpoint). -/
inductive EvalChkRule : Type
  /-- Walk left back to the marker. -/
  | stay : EvalChkRule
  /-- Dispatch: into the variable's machinery, or – at the last checkpoint,
  below the `ltp` cell – into the sweep's advance. -/
  | dspA : EvalChkRule
  /-- Dispatch at the last checkpoint, at the `ltp` cell: into the
  post-sweep reset. Dead below the last checkpoint. -/
  | dspB : EvalChkRule
  deriving DecidableEq

instance : Finite EvalChkRule :=
  Finite.of_injective
    (fun p => match p with | .stay => (0 : Fin 3) | .dspA => 1 | .dspB => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule shape of each evaluation site.** -/
def EvalSh (nv : ℕ) (SM : Type) (ShM : SM → Type) : EvalSite nv SM → Type
  | .chk _ => EvalChkRule
  | .sub s => ShM s

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q PM SM : Type} {nv : ℕ}
variable (zero one : A) {ShM : SM → Type}

/-- **The rules of the evaluation's spine**: per checkpoint the walk back
and the dispatches; the sub-machineries' rules are the parameter. -/
noncomputable def evalRule
    (ruleM : ∀ s : SM, ShM s → Rule A Q dt.SlotIx (OuterPh (EvalPh nv PM)))
    (subEntry : Fin nv → PM) :
    ∀ i : EvalSite nv SM, EvalSh nv SM ShM i →
      Rule A Q dt.SlotIx (OuterPh (EvalPh nv PM))
  | .chk k, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := .evalP (.chk k)
      dstPh := .evalP (.chk k)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .chk k, .dspA =>
    if hk : (k : ℕ) < nv then
      { guard := fun _ g => dt.exitG one g
        srcPh := .evalP (.chk k)
        dstPh := .evalP (.sub (subEntry ⟨(k : ℕ), hk⟩))
        dstSt := fun f _ => f
        wr := fun _ g => g
        moveRight := True }
    else
      { guard := fun _ g => dt.exitG one g ∧ g Slot.ltp ≠ one
        srcPh := .evalP (.chk k)
        dstPh := .advP .a1
        dstSt := fun f _ => f
        wr := fun _ g => Function.update g Slot.wk zero
        moveRight := True }
  | .chk k, .dspB =>
    if (k : ℕ) < nv then
      { guard := fun _ _ => False
        srcPh := .evalP (.chk k)
        dstPh := .evalP (.chk k)
        dstSt := fun f _ => f
        wr := fun _ g => g
        moveRight := False }
    else
      { guard := fun _ g => dt.exitG one g ∧ g Slot.ltp = one
        srcPh := .evalP (.chk k)
        dstPh := .reset2P .scan
        dstSt := fun f _ => f
        wr := fun _ g => Function.update g Slot.wk zero
        moveRight := True }
  | .sub s, ρ => ruleM s ρ

/-- **The ownership of the evaluation's phases.** -/
def evalOwn (ownM : PM → SM) : EvalPh nv PM → EvalSite nv SM
  | .chk k => .chk k
  | .sub p => .sub (ownM p)

variable {ruleM : ∀ s : SM, ShM s → Rule A Q dt.SlotIx (OuterPh (EvalPh nv PM))}
variable {subEntry : Fin nv → PM} {ownM : PM → SM}

/-- **Every spine rule fires from a phase its site owns**; the
sub-machineries' obligation is the parameter. -/
theorem evalHosrc
    (hosrcM : ∀ (s : SM) (ρ : ShM s),
      ∃ p : PM, (ruleM s ρ).srcPh = .evalP (.sub p) ∧ ownM p = s) :
    ∀ (e : EvalSite nv SM) (ρ : EvalSh nv SM ShM e),
      ∃ p : EvalPh nv PM,
        (dt.evalRule zero one ruleM subEntry e ρ).srcPh = .evalP p ∧
        evalOwn ownM p = e := by
  intro e ρ
  match e, ρ with
  | .chk k, .stay => exact ⟨.chk k, rfl, rfl⟩
  | .chk k, .dspA =>
    by_cases hk : (k : ℕ) < nv
    · exact ⟨.chk k, by simp [evalRule, hk], rfl⟩
    · exact ⟨.chk k, by simp [evalRule, hk], rfl⟩
  | .chk k, .dspB =>
    by_cases hk : (k : ℕ) < nv
    · exact ⟨.chk k, by simp [evalRule, hk], rfl⟩
    · exact ⟨.chk k, by simp [evalRule, hk], rfl⟩
  | .sub s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcM s ρ
    exact ⟨.sub p, hp, congrArg EvalSite.sub ho⟩

/-- **The spine separates in-shape**: per checkpoint, the walk's guard is
disjoint from the dispatches' and the two dispatches split on the `ltp`
mark; the sub-machineries' separation is the parameter. -/
theorem evalSep
    (hsepM : ∀ (s : SM) (ρ ρ' : ShM s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleM s ρ).guard f g → (ruleM s ρ').guard f g →
      (ruleM s ρ).srcPh = (ruleM s ρ').srcPh → ρ = ρ') :
    ∀ (e : EvalSite nv SM) (ρ ρ' : EvalSh nv SM ShM e) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.evalRule zero one ruleM subEntry e ρ).guard f g →
      (dt.evalRule zero one ruleM subEntry e ρ').guard f g →
      (dt.evalRule zero one ruleM subEntry e ρ).srcPh =
        (dt.evalRule zero one ruleM subEntry e ρ').srcPh →
      ρ = ρ' := by
  intro e ρ ρ' f g hg hg' hph
  match e, ρ, ρ' with
  | .chk k, .stay, .stay => rfl
  | .chk k, .dspA, .dspA => rfl
  | .chk k, .dspB, .dspB => rfl
  | .chk k, .stay, .dspA =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, dif_pos hk] at hg'
      simp only [evalRule] at hg
      exact absurd hg'.1 hg
    · simp only [evalRule, dif_neg hk] at hg'
      simp only [evalRule] at hg
      exact absurd hg'.1.1 hg
  | .chk k, .dspA, .stay =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, dif_pos hk] at hg
      simp only [evalRule] at hg'
      exact absurd hg.1 hg'
    · simp only [evalRule, dif_neg hk] at hg
      simp only [evalRule] at hg'
      exact absurd hg.1.1 hg'
  | .chk k, .stay, .dspB =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, if_pos hk] at hg'
    · simp only [evalRule, if_neg hk] at hg'
      simp only [evalRule] at hg
      exact absurd hg'.1.1 hg
  | .chk k, .dspB, .stay =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, if_pos hk] at hg
    · simp only [evalRule, if_neg hk] at hg
      simp only [evalRule] at hg'
      exact absurd hg.1.1 hg'
  | .chk k, .dspA, .dspB =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, if_pos hk] at hg'
    · simp only [evalRule, dif_neg hk] at hg
      simp only [evalRule, if_neg hk] at hg'
      exact absurd hg'.2 hg.2
  | .chk k, .dspB, .dspA =>
    by_cases hk : (k : ℕ) < nv
    · simp only [evalRule, if_pos hk] at hg
    · simp only [evalRule, if_neg hk] at hg
      simp only [evalRule, dif_neg hk] at hg'
      exact absurd hg.2 hg'.2
  | .sub s, ρ, ρ' => exact hsepM s ρ ρ' f g hg hg' hph

end PfpData

end Pfp

end DescriptiveComplexity
