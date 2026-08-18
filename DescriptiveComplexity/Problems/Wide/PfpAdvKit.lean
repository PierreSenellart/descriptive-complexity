/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpAdv
import DescriptiveComplexity.Problems.Wide.PfpKit

/-!
# The advance kit: one round of a sweep

The kit wrapping `DescriptiveComplexity.Pfp.Prog.reaches_fileAdvance` – the round
every sweep of the EXPSPACE program repeats: erase the working-cell marker
and step right, write it at the next address and step on, scan up to the
file top, bounce, run the mirror increment down the file, scan back to the
marker.

The *first* of those steps is fired from the caller's phase – the phase that
decided to advance – so it is a hypothesis of the discharge, not a kit rule
(rules are owned by their source phase). Everything after it is the kit's:
the marker write is the single rule of a dedicated phase (guard `⊤`, the
phase is only ever entered on the fresh marker cell), and the increment and
return rules are the ones the third hardening shaped, with the landing
phase's single `rg = one ∨ wk ≠ one` rule serving hold, walk and return.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The advance's shapes -/

/-- **The phases of an advance**: past the erased marker, scanning up,
bounced, carrying, and landed. -/
inductive AdvPh : Type
  /-- On the fresh marker cell, about to write it. -/
  | a1 : AdvPh
  /-- Scanning up to the file top. -/
  | a2 : AdvPh
  /-- Bounced off the top, about to re-enter rightwards. -/
  | a2b : AdvPh
  /-- Running the increment: clearing set digits. -/
  | a3 : AdvPh
  /-- The increment landed: walking home. -/
  | a4 : AdvPh
  deriving DecidableEq

instance : Finite AdvPh :=
  Finite.of_injective
    (fun p => match p with
      | .a1 => (0 : Fin 5) | .a2 => 1 | .a2b => 2 | .a3 => 3 | .a4 => 4)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of an advance.** -/
inductive AdvRule : Type
  /-- Write the marker at the fresh cell, stepping on. -/
  | put1 : AdvRule
  /-- Scan right while the file-top mark is clear. -/
  | up : AdvRule
  /-- At the file top: step left into the bounce phase. -/
  | b1 : AdvRule
  /-- Bounce: step back right into the increment. -/
  | b2go : AdvRule
  /-- At a register with a set digit: clear it, carry on. -/
  | clear : AdvRule
  /-- At a register with a clear digit: set it, land. -/
  | set : AdvRule
  /-- Walk left over unmarked cells while carrying. -/
  | walk : AdvRule
  /-- Hold at registers, walk and return, once landed. -/
  | stay : AdvRule
  deriving DecidableEq

instance : Finite AdvRule :=
  Finite.of_injective
    (fun p => match p with
      | .put1 => (0 : Fin 8) | .up => 1 | .b1 => 2 | .b2go => 3 | .clear => 4
      | .set => 5 | .walk => 6 | .stay => 7)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **An advance kit**: the walked mirror track, the service slots, and the
phases. -/
structure AdvKit (A Q W P : Type) where
  /-- The walked mirror track. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : AdvPh → P

namespace AdvKit

variable {A Q W P : Type} [DecidableEq W] (κ : AdvKit A Q W P) (zero one : A)

/-- **The kit's rules.** -/
def rule : AdvRule → Rule A Q W P
  | .put1 =>
    { guard := fun _ _ => True
      srcPh := κ.emb .a1
      dstPh := κ.emb .a2
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.wk one
      moveRight := True }
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .a2
      dstPh := κ.emb .a2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .a2
      dstPh := κ.emb .a2b
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .a2b
      dstPh := κ.emb .a3
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clear =>
    { guard := fun _ g => g κ.t = one ∧ g κ.rg = one
      srcPh := κ.emb .a3
      dstPh := κ.emb .a3
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t zero
      moveRight := False }
  | .set =>
    { guard := fun _ g => g κ.t = zero ∧ g κ.rg = one
      srcPh := κ.emb .a3
      dstPh := κ.emb .a4
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t one
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .a3
      dstPh := κ.emb .a3
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stay =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb .a4
      dstPh := κ.emb .a4
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation.** -/
theorem sep (hzo : zero ≠ one) (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : AdvRule) (f : Q → A) (g : W → A),
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
    | (have hbb := hemb hph; cases hbb)

/-- **Exit disjointness** at the kit's landing phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : AdvRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .a4 → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact hg.elim (fun h1 => hrg h1) (fun h2 => h2 hwk)
    | (have hbb := hemb hph; cases hbb)

/-! ### The discharge -/

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : AdvKit A Q W P}
variable {rEmb : AdvRule → R}
variable (hrules : ∀ ρ : AdvRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)
variable {I : Type} [Finite I] {ile : I → I → Prop}
variable (F : IxFile (Univ A R P K dd) I ile)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hix : IsLinOrd ile)
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)
variable {v v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v v')
variable (hv' : WMSetLt WMLe v' (F.cell gbot))
variable {m m' : I → Prop} (him : WMIncr ile m m')
variable {restA restN restB : (Univ A R P K dd → Prop) → W → A}
variable (hAN : ∀ r, r ≠ v → restN r = restA r)
variable (hNB : ∀ r, r ≠ v' → restB r = restN r)
variable (hNwk : restN v' κ.wk = PR.zero)
variable (hNoth : ∀ s : W, s ≠ κ.wk → restB v' s = restN v' s)
variable (hwkB : ∀ r, restB r κ.wk = bitVal PR.zero PR.one (r = v'))
variable (hrgB : ∀ r, restB r κ.rg = bitVal PR.zero PR.one
  (∃ u : I, r = F.cell u))
variable (hrlB : ∀ r, restB r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))
variable {p₀ : P} {fc : Q → A}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : AdvRule} {f : Q → A} {g : W → A}
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

variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hi hv' him hAN hNB hNwk hNoth
  hwkB hrgB hrlB hgap in
/-- **The kit advances the working cell**: from the caller's phase at the old
marker – whose erasing step is the caller's rule, the one hypothesis beyond
the slot equations – to the kit's landing phase at the new marker, mirror
incremented. -/
theorem reachesIn
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt F.cell κ.t restA m v) (κ.emb .a1) fc
      (PR.passTracksAt F.cell κ.t restN m v)) :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot) + 4)
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .a4) fc), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell κ.t restB m') (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- the marker write's symbol equation
  have hput : Function.update (PR.passTracksAt F.cell κ.t restN m v') κ.wk PR.one =
      PR.passTracksAt F.cell κ.t restB m v' := by
    refine funext fun s => ?_
    by_cases hs : s = κ.wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hnewk, hwkB]
      exact (bitVal_pos rfl).symm
    · rw [Function.update_of_ne hs]
      by_cases hst : s = κ.t
      · subst hst
        change (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell m v') else restN v' κ.t) =
          (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell m v') else restB v' κ.t)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne (show s ≠ κ.t from hst),
          Prog.passTracks_of_ne (show s ≠ κ.t from hst)]
        exact (hNoth s hs).symm
  have h₁ : PR.HasRight (κ.emb .a1) fc (PR.passTracksAt F.cell κ.t restN m v') (κ.emb .a2) fc
      (Function.update (PR.passTracksAt F.cell κ.t restN m v') κ.wk PR.one) :=
    (has_of_rule hrules (ρ := .put1) trivial).1 trivial
  rw [hput] at h₁
  -- the marker slot, read at or above the register file
  have hwkOff : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      PR.passTracksAt F.cell κ.t restB k r κ.wk ≠ PR.one := by
    intro k r hbnd
    obtain ⟨x, hx⟩ := hbnd
    have hne : r ≠ v' := by
      rintro rfl
      have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
        rcases eq_or_ne gbot x with rfl | hnex
        · exact hlinSet.1 _
        · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
            ⟨hbot x, fun hc => hnex (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
      exact ((wmSetLt_iff _ _).mp hv').2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv').1 (hlinSet.2.1 _ _ _ hgx hx))
    rw [Prog.passTracks_of_ne hnewk, hwkB, bitVal_neg hne]
    exact PR.zero_ne_one
  -- the register mark, read at unmarked cells
  have hrgOff : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∀ x : I, r ≠ F.cell x) →
      PR.passTracksAt F.cell κ.t restB k r κ.rg ≠ PR.one := by
    intro k r hno
    rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrgB,
      bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
    exact PR.zero_ne_one
  exact Prog.reachesIn_fileAdvance F hR hlin hix hnerg hnerl hnewk htop hbot hi hv' him
    hAN hNB hwkB hrgB hrlB
    (p₀ := p₀) (p₁ := κ.emb .a1) (p₂ := κ.emb .a2) (p₂b := κ.emb .a2b)
    (p₃ := κ.emb .a3) (p₄ := κ.emb .a4) (fc := fc)
    h₀ h₁
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t restB m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrlB]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .clear) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .set) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 => (has_of_rule hrules (ρ := .stay) (Or.inl h1)).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk) ⟨hrgOff k r hno, hwkOff k r hbnd⟩).2 not_false)
    (fun k r hbnd _hno =>
      (has_of_rule hrules (ρ := .stay) (Or.inr (hwkOff k r hbnd))).2 not_false)
    (fun _g hg => (has_of_rule hrules (ρ := .stay) (Or.inr hg)).2 not_false) (w := w) hgap

include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hi hv' him hAN hNB hNwk hNoth
  hwkB hrgB hrlB in
/-- **The kit runs one round of a sweep**, the budget forgotten. -/
theorem reaches
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt F.cell κ.t restA m v) (κ.emb .a1) fc
      (PR.passTracksAt F.cell κ.t restN m v)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .a4) fc), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell κ.t restB m') (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hnerg hnerl hnewk htop hbot hi hv' him hAN hNB hNwk hNoth
    hwkB hrgB hrlB
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) h₀).reflTransGen

end Discharge

end AdvKit

end Pfp

end DescriptiveComplexity
