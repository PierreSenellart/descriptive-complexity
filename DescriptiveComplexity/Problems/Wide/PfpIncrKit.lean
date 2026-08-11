/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTripKits

/-!
# The increment kit: a round trip around the block-indexed mirror increment

The kit wrapping `DescriptiveComplexity.Pfp.Prog.reaches_incrAt` in its round
trip: scan up to the file top, bounce, run the binary increment down the file
– clearing set digits until the first clear one, setting it – and return to
the marker **in the phase of the block that carried**. The inner VAL loop of
the EXPSPACE program folds its accumulators against exactly that block
(EXPONENTIAL.md §6.4.4), which is why the landing phase is indexed.

The carry block is read off the *mark* of the register cell that carried: the
kit takes one slot per block (`bs`), set exactly at the registers of that
block, and its `set` rule comes in one copy per block. The one-hot clause in
that rule's guard is what makes two copies separable – at an arbitrary
symbol two block slots could both be set, and the third hardening of the
layer (`DescriptiveComplexity.Pfp.Prog.reaches_incrAt`'s one-hot hypothesis)
made the demand and the guard match.

Rules are owned by their source phase: entry (at the scan phase) and exit
(at the marker, in a landing phase, guarded `wk = one ∧ rg ≠ one`) belong to
the caller.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The increment trip's shapes -/

/-- **The phases of an increment trip**: the up-scan, the bounce, the carry
phase, and one landing phase per block. -/
inductive IncrPh (B : Type) : Type
  /-- Scanning up to the file top. -/
  | up : IncrPh B
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : IncrPh B
  /-- Clearing set digits, looking for the first clear one. -/
  | pc : IncrPh B
  /-- The digit of this block was set: walking home. -/
  | pd : B → IncrPh B

instance {B : Type} [DecidableEq B] : DecidableEq (IncrPh B) := fun p q =>
  match p, q with
  | .up, .up => isTrue rfl
  | .b2, .b2 => isTrue rfl
  | .pc, .pc => isTrue rfl
  | .pd b, .pd b' =>
    if h : b = b' then isTrue (by rw [h]) else isFalse fun hc => h (IncrPh.pd.inj hc)
  | .up, .b2 | .up, .pc | .up, .pd _ | .b2, .up | .b2, .pc | .b2, .pd _
  | .pc, .up | .pc, .b2 | .pc, .pd _ | .pd _, .up | .pd _, .b2 | .pd _, .pc =>
    isFalse fun hc => nomatch hc

instance {B : Type} [Finite B] : Finite (IncrPh B) :=
  Finite.of_injective
    (fun p => match p with
      | .up => (Sum.inl 0 : Fin 3 ⊕ B) | .b2 => Sum.inl 1 | .pc => Sum.inl 2
      | .pd b => Sum.inr b)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of an increment trip**, the acting ones per block. -/
inductive IncrRule (B : Type) : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : IncrRule B
  /-- At the file top: step left into the bounce phase. -/
  | b1 : IncrRule B
  /-- Bounce: step back right into the carry phase. -/
  | b2go : IncrRule B
  /-- At a register with a set digit: clear it, carry on. -/
  | clear : IncrRule B
  /-- At a register of this block with a clear digit: set it, land. -/
  | set : B → IncrRule B
  /-- Walk left over unmarked cells in the carry phase. -/
  | walk : IncrRule B
  /-- Hold at registers, walk and return, in this block's landing phase. -/
  | stay : B → IncrRule B

instance {B : Type} [Finite B] : Finite (IncrRule B) :=
  Finite.of_injective
    (fun p => match p with
      | .up => (Sum.inl 0 : Fin 5 ⊕ (Bool × B)) | .b1 => Sum.inl 1
      | .b2go => Sum.inl 2 | .clear => Sum.inl 3 | .walk => Sum.inl 4
      | .set b => Sum.inr (false, b) | .stay b => Sum.inr (true, b))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **An increment kit**: the walked track, the service slots, the per-block
mark slots, and the phases. -/
structure IncrKit (A Q W P B : Type) where
  /-- The walked track being incremented. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The block mark: set exactly at the registers of that block. -/
  bs : B → W
  /-- The kit's phases in the program. -/
  emb : IncrPh B → P

namespace IncrKit

variable {A Q W P B : Type} [DecidableEq W] (κ : IncrKit A Q W P B) (zero one : A)

/-- **The kit's rules.** -/
def rule : IncrRule B → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clear =>
    { guard := fun _ g => g κ.t = one ∧ g κ.rg = one
      srcPh := κ.emb .pc
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t zero
      moveRight := False }
  | .set b =>
    { guard := fun _ g => g κ.t = zero ∧ g κ.rg = one ∧ g (κ.bs b) = one ∧
        ∀ b' : B, g (κ.bs b') = one → b' = b
      srcPh := κ.emb .pc
      dstPh := κ.emb (.pd b)
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t one
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .pc
      dstPh := κ.emb .pc
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stay b =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb (.pd b)
      dstPh := κ.emb (.pd b)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation.** The two indexed families separate through their
index: the `set` rules by the one-hot clause of their guards, the `stay` rules
by their source phases. -/
theorem sep (hzo : zero ≠ one) (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : IncrRule B) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd (hg.1.symm.trans hg'.1) hzo
    | exact absurd (hg'.1.symm.trans hg.1) hzo
    | exact absurd hg.2 hg'.1
    | exact absurd hg'.2 hg.1
    | exact absurd hg.2.1 hg'.1
    | exact absurd hg'.2.1 hg.1
    | exact congrArg IncrRule.set (hg'.2.2.2 _ hg.2.2.1)
    | (have hbb := hemb hph; cases hbb <;> rfl)

/-- **Exit disjointness** at the kit's landing phases. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : IncrRule B) (f : Q → A) (g : W → A) (b : B),
      (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb (.pd b) → False := by
  intro ρ f g b hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact hg.elim (fun h1 => hrg h1) (fun h2 => h2 hwk)
    | (have hbb := hemb hph; cases hbb)

/-! ### The discharge -/

section Discharge

variable {A R P Q W K B : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : IncrKit A Q W P B}
variable {rEmb : IncrRule B → R}
variable (hrules : ∀ ρ : IncrRule B, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable (hbs : ∀ b : B, κ.bs b ≠ κ.t)
variable {gtop gbot : Univ A R P K dd} (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m m' : Univ A R P K dd → Prop}
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (wmSeg gbot))
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = wmSeg gtop))
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))
variable {blkOf : Univ A R P K dd → B}
variable (hblk : ∀ (u : Univ A R P K dd) (b : B),
  rest (wmSeg u) (κ.bs b) = bitVal PR.zero PR.one (blkOf u = b))
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : IncrRule B} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.zero PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
include hlin hnewk hbot hwkLt hwkS in
private theorem wkOff (k r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) :
    PR.passTracks κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (wmSeg gbot) (wmSeg x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((wmSetLt_wmSeg_iff hlin gbot x).mpr
        ⟨hbot x, fun hc => hne (hlin.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hnerg hrg in
private theorem rgOff (k r : Univ A R P K dd → Prop)
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) :
    PR.passTracks κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one

include hrules hR hlin hnerg hnerl hnewk hbs htop hbot hwkLt hrg hrl hwkS hblk in
/-- **The kit increments its track**, and lands at the marker in the phase of
the block that carried: from the scan phase anywhere, up to the file top, the
binary increment down the file, and back. -/
theorem reaches (hi : WMIncr WMLe m m') :
    ∃ u₀ : Univ A R P K dd, (¬m u₀ ∧ ∀ v, WMLt WMLe u₀ v → m v) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
          wideTape (PR.trackTape κ.t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (κ.emb (.pd (blkOf u₀))) fc), Sum.inl wkAddr,
          wideTape (PR.trackTape κ.t rest m') (PR.syElt PR.blank)⟩ := by
  obtain ⟨u₀, pend, hu₀, hpend, hpass⟩ := Prog.reaches_incrAt hR hlin hi
    (t := κ.t) (rg := κ.rg) hnerg (rest := rest) hrg
    (B := B) (bs := κ.bs) hbs (blkOf := blkOf) hblk
    (pc := κ.emb .pc) (pd := fun b => κ.emb (.pd b)) (fc := fc)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .clear) ⟨h1, h2⟩).2 not_false)
    (fun b _g h1 h2 h3 h4 =>
      (has_of_rule hrules (ρ := .set b) ⟨h1, h2, h3, h4⟩).2 not_false)
    (fun b _g h1 => (has_of_rule hrules (ρ := .stay b) (Or.inl h1)).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff hnerg hrg k r hno, wkOff hlin hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (fun b k r hbnd hno =>
      (has_of_rule hrules (ρ := .stay b)
        (Or.inr (wkOff hlin hnewk hbot hwkLt hwkS k r hbnd))).2 not_false)
    (top := gtop) (bot := gbot) htop hbot
  refine ⟨u₀, hu₀, ?_⟩
  exact Prog.reaches_roundTrip hR hlin hnerl hnewk htop hbot (rest := rest)
    (m := m) (m₂ := m') (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .pc) (pOut := κ.emb (.pd (blkOf u₀)))
    (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracks κ.t rest m (wmSeg gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hpend hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .stay (blkOf u₀)) (Or.inr hwk)).2 not_false)
    hwkLt

end Discharge

end IncrKit

end Pfp

end DescriptiveComplexity
