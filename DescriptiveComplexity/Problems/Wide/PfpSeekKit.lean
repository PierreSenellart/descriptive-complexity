/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSeek
import DescriptiveComplexity.Problems.Wide.PfpKit

/-!
# The seek kit: random access

The kit wrapping `DescriptiveComplexity.Pfp.Prog.reaches_fileSeekTo` – the whole
random-access loop: from the checkpoint with the working-cell marker and its
mirror at the empty address, rounds of turnaround, file test MIRROR = TARGET,
and ADVANCE, until the test passes on the target's cell.

Its seventeen rule families are the loop's nine phases' worth of the shapes
the other kits established – the test trip's, the advance's – plus the two
marker steps `a0`/`put1` whose guards (`wk = one ∧ rg ≠ one`, `⊤`) the
successive hardenings of the layer made dischargeable. The target register
`tg` appears only in the test rules' guards: the per-register question is
*the walked mirror digit agrees with the target digit*, a comparison of two
slots of one symbol.

Exit is the caller's: a rule at the passing phase `ty`, at the marker,
guarded `wk = one ∧ rg ≠ one` – disjoint from every rule here.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The seek loop's shapes -/

/-- **The phases of a seek**: the loop head, the test trip's four, and the
advance's four. -/
inductive SeekPh : Type
  /-- The loop head, at the marker. -/
  | chk : SeekPh
  /-- Scanning up to the file top, for the test. -/
  | scan : SeekPh
  /-- Bounced off the top, about to re-enter the test. -/
  | t2b : SeekPh
  /-- Every register so far agreed (also: returning with verdict *yes*). -/
  | ty : SeekPh
  /-- Some register differed (also: returning with verdict *no*). -/
  | tn : SeekPh
  /-- On the fresh marker cell, about to write it. -/
  | a1 : SeekPh
  /-- Scanning up to the file top, for the increment. -/
  | a2 : SeekPh
  /-- Bounced off the top, about to re-enter the increment. -/
  | a2b : SeekPh
  /-- Running the increment: clearing set digits. -/
  | a3 : SeekPh
  deriving DecidableEq

instance : Finite SeekPh :=
  Finite.of_injective
    (fun p => match p with
      | .chk => (0 : Fin 9) | .scan => 1 | .t2b => 2 | .ty => 3 | .tn => 4
      | .a1 => 5 | .a2 => 6 | .a2b => 7 | .a3 => 8)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule families of a seek**, one constructor each. -/
inductive SeekRule : Type
  /-- Turn off the marker into the test's scan. -/
  | turn : SeekRule
  /-- Scan right while the file-top mark is clear (test). -/
  | scanT : SeekRule
  /-- At the file top: step left into the bounce phase (test). -/
  | bT1 : SeekRule
  /-- Bounce: step back right into the test. -/
  | bT2 : SeekRule
  /-- At a register whose mirror digit agrees with the target's: carry on. -/
  | pass : SeekRule
  /-- At a register where they differ: switch to the failing phase. -/
  | fail : SeekRule
  /-- Walk left over unmarked cells, and return, in the passing phase. -/
  | walkTy : SeekRule
  /-- Hold at registers, walk and return, in the failing phase. -/
  | stayTn : SeekRule
  /-- At the marker with verdict *no*: erase it and step right. -/
  | a0 : SeekRule
  /-- Write the marker at the fresh cell, stepping on. -/
  | put1 : SeekRule
  /-- Scan right while the file-top mark is clear (increment). -/
  | scanA : SeekRule
  /-- At the file top: step left into the bounce phase (increment). -/
  | bA1 : SeekRule
  /-- Bounce: step back right into the increment. -/
  | bA2 : SeekRule
  /-- At a register with a set mirror digit: clear it, carry on. -/
  | clear : SeekRule
  /-- At a register with a clear mirror digit: set it, back to the head. -/
  | set : SeekRule
  /-- Walk left over unmarked cells while carrying. -/
  | walkA : SeekRule
  /-- Hold at registers, walk and return, at the loop head. -/
  | stayChk : SeekRule
  deriving DecidableEq

instance : Finite SeekRule :=
  Finite.of_injective
    (fun p => match p with
      | .turn => (0 : Fin 17) | .scanT => 1 | .bT1 => 2 | .bT2 => 3 | .pass => 4
      | .fail => 5 | .walkTy => 6 | .stayTn => 7 | .a0 => 8 | .put1 => 9
      | .scanA => 10 | .bA1 => 11 | .bA2 => 12 | .clear => 13 | .set => 14
      | .walkA => 15 | .stayChk => 16)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **A seek kit**: the walked mirror track, the target track, the service
slots, and the phases. -/
structure SeekKit (A Q W P : Type) where
  /-- The walked mirror track. -/
  t : W
  /-- The target track the mirror is compared against. -/
  tg : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : SeekPh → P

namespace SeekKit

variable {A Q W P : Type} [DecidableEq W] (κ : SeekKit A Q W P) (zero one : A)

/-- **The kit's rules.** -/
def rule : SeekRule → Rule A Q W P
  | .turn =>
    { guard := fun _ g => g κ.wk = one ∧ g κ.rg ≠ one
      srcPh := κ.emb .chk
      dstPh := κ.emb .scan
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .scanT =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .scan
      dstPh := κ.emb .scan
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .bT1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .scan
      dstPh := κ.emb .t2b
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .bT2 =>
    { guard := fun _ _ => True
      srcPh := κ.emb .t2b
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .pass =>
    { guard := fun _ g => (g κ.t = one ↔ g κ.tg = one) ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .fail =>
    { guard := fun _ g => ¬(g κ.t = one ↔ g κ.tg = one) ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .walkTy =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayTn =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb .tn
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .a0 =>
    { guard := fun _ g => g κ.wk = one ∧ g κ.rg ≠ one
      srcPh := κ.emb .tn
      dstPh := κ.emb .a1
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.wk zero
      moveRight := True }
  | .put1 =>
    { guard := fun _ _ => True
      srcPh := κ.emb .a1
      dstPh := κ.emb .a2
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.wk one
      moveRight := True }
  | .scanA =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .a2
      dstPh := κ.emb .a2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .bA1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .a2
      dstPh := κ.emb .a2b
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .bA2 =>
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
      dstPh := κ.emb .chk
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t one
      moveRight := False }
  | .walkA =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .a3
      dstPh := κ.emb .a3
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayChk =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb .chk
      dstPh := κ.emb .chk
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **A seek stays inside its own phases**: every rule of the kit lands in one
of the phases the kit was given. -/
theorem dstPh_emb (ρ : SeekRule) :
    ∃ p : SeekPh, (κ.rule (Q := Q) zero one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩

/-- **In-shape separation.** -/
theorem sep (hzo : zero ≠ one) (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : SeekRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd (hg.1.symm.trans hg'.1) hzo
    | exact absurd (hg'.1.symm.trans hg.1) hzo
    | exact absurd hg.1 hg'.1
    | exact absurd hg'.1 hg.1
    | exact absurd hg.2 hg'.1
    | exact absurd hg'.2 hg.1
    | exact hg'.elim (fun h1 => absurd h1 hg.2) (fun h2 => absurd hg.1 h2)
    | exact hg.elim (fun h1 => absurd h1 hg'.2) (fun h2 => absurd hg'.1 h2)
    | (have hbb := hemb hph; cases hbb)

/-- **Exit disjointness** at the kit's passing verdict phase, where the
caller's exit rule reads the sought cell. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : SeekRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .ty → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg.2 hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)

/-! ### The discharge -/

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : SeekKit A Q W P}
variable {rEmb : SeekRule → R}
variable (hrules : ∀ ρ : SeekRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)
variable {I : Type} [Finite I] {ile : I → I → Prop}
variable (F : IxFile (Univ A R P K dd) I ile)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hix : IsLinOrd ile)
variable {elt : I → Univ A R P K dd} {Use : I → Prop}
variable (hinj : Function.Injective elt)
variable (hmono : ∀ u u', WMLt ile u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P K dd), Use u → WMLt WMLe (elt u) x →
  ∃ u', Use u' ∧ elt u' = x)
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable (hnetg : κ.tg ≠ κ.t)
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)
variable {T : Univ A R P K dd → Prop} (hTh : IxHolds elt Use T)
variable (hT : WMSetLt WMLe T (F.cell gbot))
variable {bg : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
variable {bgN : (Univ A R P K dd → Prop) → W → A}
variable (hbgwk : ∀ v r, bg v r κ.wk = bitVal PR.zero PR.one (r = v))
variable (hbgNwk : ∀ r, bgN r κ.wk = PR.zero)
variable (hbgNoth : ∀ v r s, s ≠ κ.wk → bgN r s = bg v r s)
variable (hbgrg : ∀ v r, bg v r κ.rg = bitVal PR.zero PR.one
  (∃ u : I, r = F.cell u))
variable (hbgrl : ∀ v r, bg v r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))
variable (hbgtg : ∀ v (u : I), bg v (F.cell u) κ.tg =
  bitVal PR.zero PR.one (ixMark elt T u))
variable {fc : Q → A}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : SeekRule} {f : Q → A} {g : W → A}
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
include hrules F hR hlin hix hinj hmono hup hnerg hnerl hnewk hnetg htop hbot hTh hT
  hbgwk hbgNwk hbgNoth
  hbgrg hbgrl hbgtg hgap in
/-- **The kit seeks the working cell to the target**: from the loop head with
the marker and mirror at the empty address, to the passing verdict phase on
the target's cell. -/
theorem reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank T *
          (1 + (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
              wideRank (F.cell gbot)) +
            (wideRank (F.cell gtop) + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
              wideRank (F.cell gbot) + 4)) + 1 +
        (wideRank (F.cell gtop) + 3 + (ixRank ile gtop - ixRank ile gbot) * w +
          wideRank (F.cell gbot)))
      ⟨Sum.inr (PR.stElt (κ.emb .chk) fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell κ.t (bg fun _ => False) fun _ => False)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl T,
        wideTape (PR.trackTapeAt F.cell κ.t (bg T) (ixMark elt T)) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- an address at or below the target is nobody's register
  have hnonregV : ∀ v : Univ A R P K dd → Prop, WMSetLt WMLe v (F.cell gbot) →
      ∀ u : I, v ≠ F.cell u := by
    intro v hv u hvu
    subst hvu
    exact ((F.lt_iff hix u gbot).mp hv).2 (hbot u)
  -- the two marker steps' symbol equations
  have hputDn : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      Function.update (PR.passTracksAt F.cell κ.t (bg v) (ixMark elt v) v) κ.wk PR.zero =
        PR.passTracksAt F.cell κ.t bgN (ixMark elt v) v := by
    intro v v' _hi _hub
    refine funext fun s => ?_
    by_cases hs : s = κ.wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hnewk, hbgNwk]
    · rw [Function.update_of_ne hs]
      by_cases hst : s = κ.t
      · subst hst
        change (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell (ixMark elt v) v)
          else bg v v κ.t) =
          (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell (ixMark elt v) v) else bgN v κ.t)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne (show s ≠ κ.t from hst),
          Prog.passTracks_of_ne (show s ≠ κ.t from hst)]
        exact (hbgNoth v v s hs).symm
  have hputUp : ∀ v v' : Univ A R P K dd → Prop, WMIncr WMLe v v' → WMSetLe WMLe v' T →
      Function.update (PR.passTracksAt F.cell κ.t bgN (ixMark elt v) v') κ.wk PR.one =
        PR.passTracksAt F.cell κ.t (bg v') (ixMark elt v) v' := by
    intro v v' _hi _hub
    refine funext fun s => ?_
    by_cases hs : s = κ.wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hnewk, hbgwk v']
      exact (bitVal_pos rfl).symm
    · rw [Function.update_of_ne hs]
      by_cases hst : s = κ.t
      · subst hst
        change (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell (ixMark elt v) v')
          else bgN v' κ.t) =
          (if κ.t = κ.t then bitVal PR.zero PR.one (bitAtOf F.cell (ixMark elt v) v')
            else bg v' v' κ.t)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne (show s ≠ κ.t from hst),
          Prog.passTracks_of_ne (show s ≠ κ.t from hst)]
        exact hbgNoth v' v' s hs
  -- ≤-<-transitivity at addresses
  have hlelt : ∀ {a b c : Univ A R P K dd → Prop}, WMSetLe WMLe a b → WMSetLt WMLe b c →
      WMSetLt WMLe a c := by
    intro a b c hab hbc
    refine (wmSetLt_iff _ _).mpr
      ⟨hlinSet.2.1 _ _ _ hab ((wmSetLt_iff _ _).mp hbc).1, fun he => ?_⟩
    subst he
    exact ((wmSetLt_iff _ _).mp hbc).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hbc).1 hab)
  exact Prog.reachesIn_ixSeekTo F hR hlin hix hinj hmono hup (t := κ.t) (rg := κ.rg) (rl := κ.rl)
    (wk := κ.wk) (tg := κ.tg) hnerg hnerl hnewk hnetg htop hbot hTh hT
    (bg := bg) (bgN := bgN) hbgwk hbgNwk hbgNoth hbgrg hbgrl hbgtg
    (pChk := κ.emb .chk) (pScan := κ.emb .scan) (pT2b := κ.emb .t2b)
    (pTy := κ.emb .ty) (pTn := κ.emb .tn) (pA1 := κ.emb .a1) (pA2 := κ.emb .a2)
    (pA2b := κ.emb .a2b) (pA3 := κ.emb .a3) (fc := fc)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .turn) ⟨h1, h2⟩).1 trivial)
    (fun _g hg => (has_of_rule hrules (ρ := .scanT) hg).1 trivial)
    (fun _g hg => (has_of_rule hrules (ρ := .bT1) hg).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .bT2) trivial).1 trivial)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .pass) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .fail) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 => (has_of_rule hrules (ρ := .stayTn) (Or.inl h1)).2 not_false)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .walkTy) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 => (has_of_rule hrules (ρ := .stayTn) (Or.inr h1)).2 not_false)
    (fun v v' hi hub => by
      have ha0 : PR.HasRight (κ.emb .tn) fc (PR.passTracksAt F.cell κ.t (bg v) (ixMark elt v) v)
          (κ.emb .a1) fc
          (Function.update (PR.passTracksAt F.cell κ.t (bg v) (ixMark elt v) v) κ.wk PR.zero) :=
        (has_of_rule hrules (ρ := .a0)
          ⟨by
            rw [Prog.passTracks_of_ne hnewk, hbgwk v]
            exact bitVal_pos rfl,
          by
            rw [Prog.passTracks_of_ne (Ne.symm hnerg), hbgrg v,
              bitVal_neg fun hc => hc.elim fun u hu =>
                hnonregV v (hlelt (hlinSet.2.1 _ _ _ (wmSetLe_of_wmIncr hi) hub) hT)
                  u hu]
            exact PR.zero_ne_one⟩).1 trivial
      rw [hputDn v v' hi hub] at ha0
      exact ha0)
    (fun v v' hi hub => by
      have ha1 : PR.HasRight (κ.emb .a1) fc (PR.passTracksAt F.cell κ.t bgN (ixMark elt v) v')
          (κ.emb .a2) fc
          (Function.update (PR.passTracksAt F.cell κ.t bgN (ixMark elt v) v') κ.wk PR.one) :=
        (has_of_rule hrules (ρ := .put1) trivial).1 trivial
      rw [hputUp v v' hi hub] at ha1
      exact ha1)
    (fun _g hg => (has_of_rule hrules (ρ := .scanA) hg).1 trivial)
    (fun _g hg => (has_of_rule hrules (ρ := .bA1) hg).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .bA2) trivial).1 trivial)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .clear) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .set) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 => (has_of_rule hrules (ρ := .stayChk) (Or.inl h1)).2 not_false)
    (fun _g h1 h2 => (has_of_rule hrules (ρ := .walkA) ⟨h1, h2⟩).2 not_false)
    (fun _g h1 => (has_of_rule hrules (ρ := .stayChk) (Or.inr h1)).2 not_false)
    (w := w) hgap

include hrules F hR hlin hix hinj hmono hup hnerg hnerl hnewk hnetg htop hbot hTh hT
  hbgwk hbgNwk hbgNoth
  hbgrg hbgrl hbgtg in
/-- **The kit seeks the working cell to the target**, the budget forgotten. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .chk) fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell κ.t (bg fun _ => False) fun _ => False)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl T,
        wideTape (PR.trackTapeAt F.cell κ.t (bg T) (ixMark elt T)) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hinj hmono hup hnerg hnerl hnewk hnetg htop hbot hTh hT
    hbgwk hbgNwk hbgNoth hbgrg hbgrl hbgtg
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))).reflTransGen

end Discharge

end SeekKit

end Pfp

end DescriptiveComplexity
