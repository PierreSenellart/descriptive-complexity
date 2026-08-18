/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawFactor
import DescriptiveComplexity.Problems.Wide.DrawIncrKit
import DescriptiveComplexity.Problems.Wide.DrawSeekKit
import DescriptiveComplexity.Problems.Wide.DrawAdvKit
import DescriptiveComplexity.Problems.Wide.DrawSweepKit
import DescriptiveComplexity.Problems.Wide.DrawReset

/-!
# Every leaf kit's rules are definable

The first floor of the discharge `DescriptiveComplexity.Problems.Wide.DrawFactor`
sets up: each *kit* – the small, separately checkable composites the EXPSPACE
program's rule set is a sum of – meets
`DescriptiveComplexity.Draw.URuleDefinable` for every one of its rule families,
given that its own abstract parameters do.

Two things make each proof a line: every kit's guard is a Boolean combination
of the three atoms (a slot holds `one`, a slot holds `zero`, two slots hold the
same element) with the kit's parameters, and every kit leaves its pointer
alone, writing at most one track slot – `DescriptiveComplexity.Draw.UTrDefinable.update`
with a designated element, a copy of another slot, or a bit whose question is
the kit's parameter.

The kits are stated at a *family* of kits, one per environment: the slots, the
phase embedding and the shape are the same at every instance – they are what an
interpretation's tag decides – and only the parameters vary with it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {Q W P : Type} [Fintype Q] [Fintype W]

/-! ### The named read and write trips -/

/-- **A read trip's rules are definable**, given its name guard: every shape's
guard is one atom, or its negation, or the name guard, and nothing is
written. -/
theorem ReadKit.uRuleDefinable {t wk : W} {emb : ReadPh → P}
    {M : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop} (hM : UGDefinable M)
    (ρ : ReadRule) :
    URuleDefinable fun e => (ReadKit.mk t wk (M e) emb).rule e.one ρ := by
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  have ht := uGDefinable_trkOne (L := L) (Q := Q) t
  cases ρ <;>
    refine uRuleDefinable_of_keep
      ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩, ?_⟩ ?_ (fun _ _ _ => rfl) fun _ _ _ => rfl
  · exact uRight_of_true fun _ => trivial
  · exact hwk
  · exact uRight_of_true fun _ => trivial
  · exact hM.not
  · exact uRight_of_false fun _ => not_false
  · exact hM.and ht
  · exact uRight_of_false fun _ => not_false
  · exact hM.and ht.not
  · exact uRight_of_false fun _ => not_false
  · exact hwk.not
  · exact uRight_of_false fun _ => not_false
  · exact hwk.not
  · exact uRight_of_false fun _ => not_false
  · exact hwk.not

/-- **A write trip's rules are definable**, given its name guard and the
question behind the bit it writes. -/
theorem WriteKit.uRuleDefinable [DecidableEq W] {t wk : W} {emb : WritePh → P}
    {M : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {bVal : ∀ e : Env L, (Q → e.α) → Prop} (hM : UGDefinable M)
    (hb : UGDefinable fun e f (_ : W → e.α) => bVal e f) (ρ : WriteRule) :
    URuleDefinable fun e =>
      (WriteKit.mk t wk (M e) (bVal e) emb).rule e.zero e.one ρ := by
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  match ρ with
  | .turn =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hwk (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hM.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hM (fun _ _ _ => rfl)
      (uTrDefinable_id.update t (uSlotDefinable_bitVal hb))
  | .back =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hwk.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .stayS =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hwk.not (fun _ _ _ => rfl) fun _ _ _ => rfl

/-! ### The register-file passes -/

/-- **A file test's rules are definable**, given its per-register question. -/
theorem TestKit.uRuleDefinable {t rg rl wk : W} {emb : TestPh → P}
    {TestG : ∀ e : Env L, (W → e.α) → Prop}
    (hT : UGDefinable fun e (_ : Q → e.α) g => TestG e g) (ρ : TestRule) :
    URuleDefinable (Q := Q) fun e =>
      (TestKit.mk t rg rl wk (TestG e) emb).rule e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  cases ρ <;>
    refine uRuleDefinable_of_keep
      ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩, ?_⟩ ?_ (fun _ _ _ => rfl) fun _ _ _ => rfl
  · exact uRight_of_true fun _ => trivial
  · exact hrl.not
  · exact uRight_of_false fun _ => not_false
  · exact hrl
  · exact uRight_of_true fun _ => trivial
  · exact uGDefinable_true
  · exact uRight_of_false fun _ => not_false
  · exact hT.and hrg
  · exact uRight_of_false fun _ => not_false
  · exact hT.not.and hrg
  · exact uRight_of_false fun _ => not_false
  · exact hrg.not.and hwk.not
  · exact uRight_of_false fun _ => not_false
  · exact hrg.or hwk.not

/-- **A track-clearing pass's rules are definable.** -/
theorem ClearKit.uRuleDefinable [DecidableEq W] {t rg rl wk : W}
    {emb : TrackPh → P} (ρ : TrackRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (ClearKit.mk t rg rl wk emb).rule e.zero e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  match ρ with
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b2go =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrg (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_zero)
  | .walk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-- **A track-copying pass's rules are definable.** -/
theorem CopyKit.uRuleDefinable [DecidableEq W] {t src rg rl wk : W}
    {emb : TrackPh → P} (ρ : TrackRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (CopyKit.mk t src rg rl wk emb).rule e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  match ρ with
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b2go =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrg (fun _ _ _ => rfl)
      (uTrDefinable_id.update t (uSlotDefinable_trk src))
  | .walk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-- **A track-mapping pass's rules are definable**, given the question behind
the bit it writes. -/
theorem MapKit.uRuleDefinable [DecidableEq W] {t rg rl wk : W} {emb : TrackPh → P}
    {Fb : ∀ e : Env L, (W → e.α) → Prop}
    (hF : UGDefinable fun e (_ : Q → e.α) g => Fb e g) (ρ : TrackRule) :
    URuleDefinable (Q := Q) fun e =>
      (MapKit.mk t rg rl wk (Fb e) emb).rule e.zero e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  match ρ with
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b2go =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrg (fun _ _ _ => rfl)
      (uTrDefinable_id.update t (uSlotDefinable_bitVal hF))
  | .walk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-! ### The three roaming passes -/

/-- **An increment's rules are definable**: the one-hot clause of the setting
rule is a conjunction over the block marks of an implication whose conclusion
is decided when the formula is built. -/
theorem IncrKit.uRuleDefinable [DecidableEq W] {B : Type} [Finite B] {t rg rl wk : W}
    {bs : B → W} {emb : IncrPh B → P} (ρ : IncrRule B) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (IncrKit.mk t rg rl wk bs emb).rule e.zero e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  have ht1 := uGDefinable_trkOne (L := L) (Q := Q) t
  have ht0 := uGDefinable_trkZero (L := L) (Q := Q) t
  match ρ with
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b2go =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .clear =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (ht1.and hrg) (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_zero)
  | .set b =>
    refine uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ ?_ (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_one)
    exact ht0.and (hrg.and ((uGDefinable_trkOne (L := L) (Q := Q) (bs b)).and
      (uGDefinable_forall fun b' : B =>
        (uGDefinable_trkOne (L := L) (Q := Q) (bs b')).imp (uGDefinable_const (b' = b)))))
  | .walk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .stay b =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.or hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-- **A seek's rules are definable**: its comparison is an equivalence of two
atoms. -/
theorem SeekKit.uRuleDefinable [DecidableEq W] {t tg rg rl wk : W}
    {emb : SeekPh → P} (ρ : SeekRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (SeekKit.mk t tg rg rl wk emb).rule e.zero e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  have ht1 := uGDefinable_trkOne (L := L) (Q := Q) t
  have ht0 := uGDefinable_trkZero (L := L) (Q := Q) t
  have hcmp := ht1.iff (uGDefinable_trkOne (L := L) (Q := Q) tg)
  match ρ with
  | .turn =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ (hwk.and hrg.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .scanT =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .bT1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .bT2 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .pass =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hcmp.and hrg) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .fail =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hcmp.not.and hrg) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .walkTy =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .stayTn =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.or hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .a0 =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ (hwk.and hrg.not) (fun _ _ _ => rfl)
      (uTrDefinable_id.update wk uSlotDefinable_zero)
  | .put1 =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      (uTrDefinable_id.update wk uSlotDefinable_one)
  | .scanA =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .bA1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .bA2 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .clear =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (ht1.and hrg) (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_zero)
  | .set =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (ht0.and hrg) (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_one)
  | .walkA =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .stayChk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.or hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-- **An advance's rules are definable.** -/
theorem AdvKit.uRuleDefinable [DecidableEq W] {t rg rl wk : W} {emb : AdvPh → P}
    (ρ : AdvRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (AdvKit.mk t rg rl wk emb).rule e.zero e.one ρ := by
  have hrl := uGDefinable_trkOne (L := L) (Q := Q) rl
  have hrg := uGDefinable_trkOne (L := L) (Q := Q) rg
  have hwk := uGDefinable_trkOne (L := L) (Q := Q) wk
  have ht1 := uGDefinable_trkOne (L := L) (Q := Q) t
  have ht0 := uGDefinable_trkZero (L := L) (Q := Q) t
  match ρ with
  | .put1 =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      (uTrDefinable_id.update wk uSlotDefinable_one)
  | .up =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hrl.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b1 =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hrl (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .b2go =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .clear =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (ht1.and hrg) (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_zero)
  | .set =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (ht0.and hrg) (fun _ _ _ => rfl)
      (uTrDefinable_id.update t uSlotDefinable_one)
  | .walk =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.not.and hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl
  | .stay =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ (hrg.or hwk.not) (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-! ### The reset, the walk home and the two sweeps -/

/-- **A reset's rules are definable.** -/
theorem ResetKit.uRuleDefinable [DecidableEq W] {t bt wk : W} {emb : ResetPh → P}
    (ρ : ResetRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (ResetKit.mk t bt wk emb).rule e.one ρ := by
  have hbt := uGDefinable_trkOne (L := L) (Q := Q) bt
  match ρ with
  | .down =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ hbt.not (fun _ _ _ => rfl) fun _ _ _ => rfl
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ hbt (fun _ _ _ => rfl)
      (uTrDefinable_id.update wk uSlotDefinable_one)
  | .back =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
      fun _ _ _ => rfl

/-- **The walk home is definable.** -/
theorem HomeKit.uRuleDefinable {t wk : W} {ph : P} (ρ : HomeKit.HomeRule) :
    URuleDefinable (L := L) (Q := Q) fun e =>
      (HomeKit.mk t wk ph).rule e.one ρ := by
  match ρ with
  | .down =>
    exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_false fun _ => not_false⟩
      (uGDefinable_trkOne (L := L) (Q := Q) wk).not (fun _ _ _ => rfl) fun _ _ _ => rfl

/-- **A flag sweep's rules are definable**, given its per-cell question. -/
theorem FlagSweepKit.uRuleDefinable {t ltp : W} {emb : SweepPh → P}
    {TestG : ∀ e : Env L, (W → e.α) → Prop}
    (hT : UGDefinable fun e (_ : Q → e.α) g => TestG e g) (ρ : SweepRule) :
    URuleDefinable (Q := Q) fun e =>
      (FlagSweepKit.mk t ltp (TestG e) emb).rule e.one ρ := by
  have hltp := uGDefinable_trkOne (L := L) (Q := Q) ltp
  cases ρ <;>
    refine uRuleDefinable_of_keep
      ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩, uRight_of_true fun _ => trivial⟩ ?_
      (fun _ _ _ => rfl) fun _ _ _ => rfl
  · exact hT.and hltp.not
  · exact hT.not.and hltp.not
  · exact hltp.not

/-- **A write sweep's rule is definable**, given the rewrite it carries. -/
theorem WriteSweepKit.uRuleDefinable {t ltp : W} {ph : P}
    {wrG : ∀ e : Env L, (W → e.α) → W → e.α}
    (hw : UTrDefinable fun e (_ : Q → e.α) g => wrG e g) (ρ : WSweepRule) :
    URuleDefinable (Q := Q) fun e =>
      (WriteSweepKit.mk t ltp (fun g => wrG e g) ph).rule e.one ρ := by
  match ρ with
  | .put =>
    exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩
      (uGDefinable_trkOne (L := L) (Q := Q) ltp).not (fun _ _ _ => rfl) hw

end Draw

end DescriptiveComplexity
