/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInterp
import DescriptiveComplexity.Problems.Wide.TrackWrites

/-!
# Rules that never fire, and the tags they buy

A clocked program's budget is `2 ^ |Tag|`, and its tags are its rule names: one
per site and shape. A reduction that needs a longer clock therefore needs more
rule names – and it needs them *without* changing anything else, because every
constant the clock is measured against (the file's registers, the evaluation's
widths, the record's own dimensions) is read off the same record.

This file is that knob. A **junk site** carries one rule whose guard is `False`:
it can never fire, so no run, no separation argument and no determinism argument
sees it, while the rule names go up by one. Padding a site type by `Fin n` adds
`n` of them.

The whole thing is generic in the site type, so it applies to any program the
definability layer writes down (`padRules`, `uRulesDefinable_padRules`), and the
count is one line (`card_rTagOf_pad`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section Pad

variable {L : Language.{0, 0}} {dt : Data L} [Fintype dt.SlotIx]
variable {S : Type} {Sh : S → Type} {P : Type}

/-- **A rule that never fires**: its guard is false, and everything else is the
identity. It sits at a phase of the caller's choosing and is never reached
there, the guard being what a step asks for first. -/
def falseRule {A Q W : Type} (p : P) : Rule A Q W P where
  guard := fun _ _ => False
  srcPh := p
  dstPh := p
  dstSt := fun f _ => f
  wr := fun _ g => g
  moveRight := False

variable (Sh) in
/-- **The shapes of a padded site type**: the old sites keep theirs, and each
new one has a single rule. -/
def padSh (n : ℕ) : S ⊕ Fin n → Type
  | Sum.inl i => Sh i
  | Sum.inr _ => Unit

instance [∀ i, Finite (Sh i)] (n : ℕ) (i : S ⊕ Fin n) :
    Finite (padSh Sh n i) := by
  cases i <;> unfold padSh <;> infer_instance

/-- **The rules of a padded site type**: the old ones, and a rule that never
fires at each new site. -/
def padRules (rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α dt.CtlIx dt.SlotIx P)
    (p₀ : P) (n : ℕ) :
    ∀ (e : Env L) (i : S ⊕ Fin n), padSh Sh n i →
      Rule e.α dt.CtlIx dt.SlotIx P
  | e, Sum.inl i, ρ => rules e i ρ
  | _, Sum.inr _, _ => falseRule p₀

omit [Fintype dt.SlotIx] in
@[simp]
theorem padRules_inl
    (rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α dt.CtlIx dt.SlotIx P)
    (p₀ : P) (n : ℕ) (e : Env L) (i : S) (ρ : Sh i) :
    padRules (dt := dt) rules p₀ n e (Sum.inl i) ρ = rules e i ρ := rfl

omit [Fintype dt.SlotIx] in
@[simp]
theorem padRules_inr
    (rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α dt.CtlIx dt.SlotIx P)
    (p₀ : P) {n : ℕ} (e : Env L) (k : Fin n) (ρ : padSh Sh n (Sum.inr k)) :
    padRules (dt := dt) rules p₀ n e (Sum.inr k) ρ = falseRule p₀ := rfl

/-- **The padded rules are definable**: the old ones by hypothesis, and a rule
that never fires by `uGDefinable_false`. -/
theorem uRulesDefinable_padRules
    {rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α dt.CtlIx dt.SlotIx P}
    (h : URulesDefinable rules) (p₀ : P) (n : ℕ) :
    URulesDefinable (padRules (dt := dt) rules p₀ n) := by
  rintro (i | k) ρ
  · exact h i ρ
  · exact uRuleDefinable_of_keep
      ⟨⟨p₀, fun _ => rfl⟩, ⟨p₀, fun _ => rfl⟩, uRight_of_false fun _ => not_false⟩
      uGDefinable_false (fun _ _ _ => rfl) fun _ _ _ => rfl

omit [Fintype dt.SlotIx] in
/-- **A junk rule writes nothing**, so it keeps the file, keeps the addressed
tracks, keeps every slot and writes bits – the four facts a backward reading
asks of a rule it meets by name. -/
theorem falseRule_facts {A Q : Type} (zero one : A) (p : P) :
    Rule.KeepsFile dt (falseRule (A := A) (Q := Q) (W := dt.SlotIx) p) ∧
      Rule.KeepsCellTracks dt (falseRule (A := A) (Q := Q) (W := dt.SlotIx) p) ∧
      Rule.WritesBits dt zero one (falseRule (A := A) (Q := Q) (W := dt.SlotIx) p) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => Or.inl rfl⟩

omit [Fintype dt.SlotIx] in
/-- **And it leaves every slot as it found it.** -/
theorem falseRule_keepsSlot {A Q : Type} (t : dt.SlotIx) (p : P) :
    Rule.KeepsSlot dt t (falseRule (A := A) (Q := Q) (W := dt.SlotIx) p) :=
  fun _ _ => rfl

variable (Sh) in
/-- **The rules of a padded site type, at one instance**: the same padding as
`padRules`, for a program written down at a fixed universe rather than as a
family. -/
def padRulesAt {A : Type} (rl : ∀ i : S, Sh i → Rule A dt.CtlIx dt.SlotIx P)
    (p₀ : P) (n : ℕ) :
    ∀ i : S ⊕ Fin n, padSh Sh n i → Rule A dt.CtlIx dt.SlotIx P
  | Sum.inl i, ρ => rl i ρ
  | Sum.inr _, _ => falseRule p₀

omit [Fintype dt.SlotIx] in
@[simp]
theorem padRulesAt_inl {A : Type}
    (rl : ∀ i : S, Sh i → Rule A dt.CtlIx dt.SlotIx P) (p₀ : P) (n : ℕ)
    (i : S) (ρ : Sh i) :
    padRulesAt (dt := dt) Sh rl p₀ n (Sum.inl i) ρ = rl i ρ := rfl

omit [Fintype dt.SlotIx] in
/-- **A junk rule never fires**, which is all any run, separation or determinism
argument needs to know about it. -/
theorem not_guard_padRulesAt {A : Type}
    (rl : ∀ i : S, Sh i → Rule A dt.CtlIx dt.SlotIx P) {p₀ : P} {n : ℕ}
    (k : Fin n) (ρ : padSh Sh n (Sum.inr k)) (f : dt.CtlIx → A)
    (g : dt.SlotIx → A) :
    ¬(padRulesAt (dt := dt) Sh rl p₀ n (Sum.inr k) ρ).guard f g := fun h => h

omit [Fintype dt.SlotIx] in
/-- **Padding keeps in-shape separation**: two rules that fire on the same data
in the same phase are the same, the junk ones firing on none. -/
theorem sep_padRulesAt {A : Type}
    {rl : ∀ i : S, Sh i → Rule A dt.CtlIx dt.SlotIx P} {p₀ : P} {n : ℕ}
    {Ph : P → Prop}
    (hsep : ∀ (i i' : S) (ρ : Sh i) (ρ' : Sh i') (f : dt.CtlIx → A)
        (g : dt.SlotIx → A), Ph (rl i ρ).srcPh → (rl i ρ).guard f g →
      (rl i' ρ').guard f g → (rl i ρ).srcPh = (rl i' ρ').srcPh →
      (⟨i, ρ⟩ : Data.RTagOf S Sh) = ⟨i', ρ'⟩) :
    ∀ (i i' : S ⊕ Fin n) (ρ : padSh Sh n i) (ρ' : padSh Sh n i')
      (f : dt.CtlIx → A) (g : dt.SlotIx → A),
      Ph (padRulesAt (dt := dt) Sh rl p₀ n i ρ).srcPh →
      (padRulesAt (dt := dt) Sh rl p₀ n i ρ).guard f g →
      (padRulesAt (dt := dt) Sh rl p₀ n i' ρ').guard f g →
      (padRulesAt (dt := dt) Sh rl p₀ n i ρ).srcPh =
        (padRulesAt (dt := dt) Sh rl p₀ n i' ρ').srcPh →
      (⟨i, ρ⟩ : Data.RTagOf (S ⊕ Fin n) (padSh Sh n)) = ⟨i', ρ'⟩ := by
  rintro (i | k) (i' | k') ρ ρ' f g hph hg hg' hs
  · have h := hsep i i' ρ ρ' f g hph hg hg' hs
    have h1 : i = i' := congrArg Sigma.fst h
    subst h1
    have h2 : ρ = ρ' := eq_of_heq (Sigma.mk.inj h).2
    rw [h2]
  · exact (not_guard_padRulesAt (dt := dt) (Sh := Sh) rl (p₀ := p₀) k' ρ' f g hg').elim
  · exact (not_guard_padRulesAt (dt := dt) (Sh := Sh) rl (p₀ := p₀) k ρ f g hg).elim
  · exact (not_guard_padRulesAt (dt := dt) (Sh := Sh) rl (p₀ := p₀) k ρ f g hg).elim

omit [Fintype dt.SlotIx] in
/-- **The family and the pointwise padding agree**, which is what lets a program
written down at one universe be read as the definability layer's. -/
theorem padRules_eq_padRulesAt
    (rules : ∀ (e : Env L) (i : S), Sh i → Rule e.α dt.CtlIx dt.SlotIx P)
    (p₀ : P) (n : ℕ) (e : Env L) :
    padRules (dt := dt) rules p₀ n e =
      padRulesAt (dt := dt) Sh (rules e) p₀ n := by
  funext i ρ
  cases i <;> rfl

/-- **What the padding buys**: one rule name per junk site. -/
theorem card_rTagOf_pad [Finite S] [∀ i, Finite (Sh i)] (n : ℕ) :
    Nat.card (Data.RTagOf (S ⊕ Fin n) (padSh Sh n)) =
      Nat.card (Data.RTagOf S Sh) + n := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have : ∀ i, Fintype (Sh i) := fun i => Fintype.ofFinite _
  have : ∀ i : S ⊕ Fin n, Fintype (padSh Sh n i) := fun i => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [show Fintype.card (Data.RTagOf (S ⊕ Fin n) (padSh Sh n)) =
      ∑ i : S ⊕ Fin n, Fintype.card (padSh Sh n i) from Fintype.card_sigma,
    show Fintype.card (Data.RTagOf S Sh) = ∑ i : S, Fintype.card (Sh i) from
      Fintype.card_sigma]
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : S, Fintype.card (padSh Sh n (Sum.inl i)) =
      ∑ i : S, Fintype.card (Sh i) :=
    Finset.sum_congr rfl fun i _ => Fintype.card_congr (Equiv.refl (Sh i))
  have h2 : ∑ _k : Fin n, Fintype.card (padSh Sh n (Sum.inr _k)) = n := by
    have : ∀ k : Fin n, Fintype.card (padSh Sh n (Sum.inr k)) = 1 := fun _ =>
      Fintype.card_eq_one_iff.mpr ⟨(), fun _ => rfl⟩
    simp [this]
  rw [h1, h2]

end Pad

end Draw

end DescriptiveComplexity
