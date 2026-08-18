/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawTrip
import DescriptiveComplexity.Problems.Wide.DrawKit

/-!
# Resetting the working cell to the bottom

A random access starts at the checkpoint: marker and mirror at the empty
address. Getting there from wherever the marker is –
`DescriptiveComplexity.Draw.Prog.reaches_reset` – is the one itinerary of the
program that runs *down* the working area: erase the marker **and step
right** (never left, so the empty address needs no special case), scan left
to the cell the permanent `bot` mark identifies, write the marker there
stepping right, and bounce back left onto it. The mirror is cleared by a
separate `DescriptiveComplexity.Draw.ClearKit` trip afterwards.

`DescriptiveComplexity.Draw.ResetKit` is the kit: the scan and the two
bounce steps; the erasing entry is the caller's rule, and the landing phase
hosts nothing – the machine arrives exactly once, at the bottom cell, where
the caller's exit fires.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Prog

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)

/-- **The reset, on a clock**: from the caller's phase at the marker – whose
erasing step, rightwards, is the caller's rule – scan left to the bottom cell,
write the marker there stepping right, and bounce back onto it. The empty
address is identified by the permanent `bot` mark, and no leftward step is ever
taken at it. The scan is a walk down the whole order below the marker, so the
cost is the marker's rank and the three steps around it. -/
theorem reachesIn_reset (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t bt wk : W} (hnebt : bt ≠ t) (hnewk : wk ≠ t)
    {v : Univ A R P K dd → Prop} (hv : ∃ x : Univ A R P K dd, ¬v x)
    {m : I → Prop}
    {restA restN restB : (Univ A R P K dd → Prop) → W → A}
    (hAN : ∀ r, r ≠ v → restN r = restA r)
    (hNB : ∀ r, r ≠ (fun _ => False) → restB r = restN r)
    (hbtN : ∀ r, restN r bt = bitVal PR.zero PR.one (r = fun _ => False))
    (hwkB : ∀ r, restB r wk = bitVal PR.zero PR.one (r = fun _ => False))
    (hNBslot : ∀ s : W, s ≠ wk → restB (fun _ => False) s = restN (fun _ => False) s)
    {p₀ pScan pB pDone : P} {fc : Q → A}
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt RF.cell t restA m v) pScan fc
      (PR.passTracksAt RF.cell t restN m v))
    (hdown : ∀ g : W → A, g bt ≠ PR.one → PR.HasLeft pScan fc g pScan fc g)
    (hput : ∀ g : W → A, g bt = PR.one → PR.HasRight pScan fc g pB fc
      (Function.update g wk PR.one))
    (hback : ∀ g : W → A, PR.HasLeft pB fc g pDone fc g) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank v + 4)
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pDone fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt RF.cell t restB m) (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  -- the marker's successor, for the erasing entry step
  obtain ⟨v₂, hi₂⟩ := exists_wmIncr hlin hv
  -- the empty address's successor, for the marker write
  have hne0 : ∃ x : Univ A R P K dd, ¬(fun _ => False) x := ⟨hv.choose, fun hc => hc⟩
  obtain ⟨e₂, hie⟩ := exists_wmIncr hlin hne0
  -- step 1: erase the marker, moving right
  have s₁ := PR.step_move (t := t) (rest := restA) (rest' := restN) (m := m)
    hR hlin hi₂ hAN h₀
  -- the scan down to the bottom cell
  have hscan := reachesIn_toCellBackC (cell := RF.cell) (StopG := fun g => g bt = PR.one) hR hlin
    (t := t) (rest := restN) (m := m) (p := pScan) (f := fc)
    (fun r _ hstop => hdown _ hstop)
    (u := fun _ => False) (s := v₂)
    (by rw [passTracks_of_ne hnebt, hbtN]; exact bitVal_pos rfl)
    (wmSetLe_of_empty hlin (fun _ hc => hc) v₂)
    (fun r _ hstop => by
      rw [passTracks_of_ne hnebt, hbtN] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- the marker write's symbol equation
  have hputEq : Function.update (PR.passTracksAt RF.cell t restN m (fun _ => False)) wk PR.one =
      PR.passTracksAt RF.cell t restB m (fun _ => False) := by
    refine funext fun s => ?_
    by_cases hs : s = wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hnewk, hwkB]
      exact (bitVal_pos rfl).symm
    · rw [Function.update_of_ne hs]
      by_cases hst : s = t
      · rw [hst]
        change (if t = t then bitVal PR.zero PR.one (bitAtOf RF.cell m fun _ => False)
            else restN (fun _ => False) t) =
          (if t = t then bitVal PR.zero PR.one (bitAtOf RF.cell m fun _ => False)
            else restB (fun _ => False) t)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne (show s ≠ t from hst),
          Prog.passTracks_of_ne (show s ≠ t from hst)]
        exact (hNBslot s hs).symm
  -- step 2: write the marker at the bottom, moving right
  have hNB' : ∀ r, r ≠ (fun _ => False) → restB r = restN r := hNB
  have s₂ : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt pScan fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt RF.cell t restN m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pB fc), Sum.inl e₂,
        wideTape (PR.trackTapeAt RF.cell t restB m) (PR.syElt PR.blank)⟩ := by
    have hrule := hput (PR.passTracksAt RF.cell t restN m (fun _ => False))
      (by rw [passTracks_of_ne hnebt, hbtN]; exact bitVal_pos rfl)
    rw [hputEq] at hrule
    exact PR.step_move (t := t) (rest := restN) (rest' := restB) (m := m)
      hR hlin hie hNB' hrule
  -- step 3: bounce back left onto the bottom cell
  have s₃ := PR.step_moveBack (t := t) (rest := restB) (rest' := restB) (m := m)
    hR hlin hie (fun _ _ => rfl) (p := pB) (p' := pDone) (f := fc) (f' := fc)
    (hback (PR.passTracksAt RF.cell t restB m e₂))
  refine TMData.ReachesIn.mono ?_
    ((TMData.reachesIn_of_step s₁).trans
      (hscan.trans ((TMData.reachesIn_of_step s₂).tail s₃)))
  rw [wideRank_bot hlin, wideRank_incr hlin hi₂]
  omega

/-- **The reset**, the budget forgotten. -/
theorem reaches_reset (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t bt wk : W} (hnebt : bt ≠ t) (hnewk : wk ≠ t)
    {v : Univ A R P K dd → Prop} (hv : ∃ x : Univ A R P K dd, ¬v x)
    {m : I → Prop}
    {restA restN restB : (Univ A R P K dd → Prop) → W → A}
    (hAN : ∀ r, r ≠ v → restN r = restA r)
    (hNB : ∀ r, r ≠ (fun _ => False) → restB r = restN r)
    (hbtN : ∀ r, restN r bt = bitVal PR.zero PR.one (r = fun _ => False))
    (hwkB : ∀ r, restB r wk = bitVal PR.zero PR.one (r = fun _ => False))
    (hNBslot : ∀ s : W, s ≠ wk → restB (fun _ => False) s = restN (fun _ => False) s)
    {p₀ pScan pB pDone : P} {fc : Q → A}
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt RF.cell t restA m v) pScan fc
      (PR.passTracksAt RF.cell t restN m v))
    (hdown : ∀ g : W → A, g bt ≠ PR.one → PR.HasLeft pScan fc g pScan fc g)
    (hput : ∀ g : W → A, g bt = PR.one → PR.HasRight pScan fc g pB fc
      (Function.update g wk PR.one))
    (hback : ∀ g : W → A, PR.HasLeft pB fc g pDone fc g) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pDone fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt RF.cell t restB m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_reset RF hR hlin hnebt hnewk hv hAN hNB hbtN hwkB hNBslot h₀ hdown hput
    hback).reflTransGen

end Prog

/-! ### The reset kit -/

/-- **The phases of a reset**: the down-scan, the bounce, and the landing –
which hosts no rule, the caller's exit firing on arrival. -/
inductive ResetPh : Type
  /-- Scanning left to the bottom cell. -/
  | scan : ResetPh
  /-- The marker written, bouncing back. -/
  | b : ResetPh
  /-- At the bottom cell, marker set. -/
  | done : ResetPh
  deriving DecidableEq

instance : Finite ResetPh :=
  Finite.of_injective
    (fun p => match p with | .scan => (0 : Fin 3) | .b => 1 | .done => 2)
    (by intro a₁ a₂ h; cases a₁ <;> cases a₂ <;> simp_all)

/-- **The rule families of a reset.** -/
inductive ResetRule : Type
  /-- Scan left while the bottom mark is clear. -/
  | down : ResetRule
  /-- At the bottom cell: write the marker, step right. -/
  | put : ResetRule
  /-- Bounce back left onto the marker. -/
  | back : ResetRule
  deriving DecidableEq

instance : Finite ResetRule :=
  Finite.of_injective
    (fun p => match p with | .down => (0 : Fin 3) | .put => 1 | .back => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **A reset kit**: the walked track, the bottom-mark and marker slots, and
the phases. -/
structure ResetKit (A Q W P : Type) where
  /-- The walked track (rides along unchanged). -/
  t : W
  /-- The bottom mark, planted at the empty address at startup. -/
  bt : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : ResetPh → P

namespace ResetKit

variable {A Q W P : Type} [DecidableEq W] (κ : ResetKit A Q W P) (one : A)

/-- **The kit's rules.** -/
noncomputable def rule : ResetRule → Rule A Q W P
  | .down =>
    { guard := fun _ g => g κ.bt ≠ one
      srcPh := κ.emb .scan
      dstPh := κ.emb .scan
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .put =>
    { guard := fun _ g => g κ.bt = one
      srcPh := κ.emb .scan
      dstPh := κ.emb .b
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.wk one
      moveRight := True }
  | .back =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b
      dstPh := κ.emb .done
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **A reset stays inside its own phases**: every rule of the kit lands in one
of the three the kit was given. -/
theorem dstPh_emb (ρ : ResetRule) :
    ∃ p : ResetPh, (κ.rule (Q := Q) one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩

/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : ResetRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd hg' hg
    | exact absurd hg hg'
    | (have hbb := hemb hph; cases hbb)

/-- **Exit disjointness** at the landing phase: no kit rule fires from it at
all. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : ResetRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      (κ.rule one ρ).srcPh = κ.emb .done → False := by
  intro ρ f g _hg hph
  cases ρ <;> simp only [rule] at hph <;> (have hbb := hemb hph; cases hbb)

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : ResetKit A Q W P}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)
variable {rEmb : ResetRule → R}
variable (hrules : ∀ ρ : ResetRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnebt : κ.bt ≠ κ.t) (hnewk : κ.wk ≠ κ.t)
variable {v : Univ A R P K dd → Prop} (hv : ∃ x : Univ A R P K dd, ¬v x)
variable {m : I → Prop}
variable {restA restN restB : (Univ A R P K dd → Prop) → W → A}
variable (hAN : ∀ r, r ≠ v → restN r = restA r)
variable (hNB : ∀ r, r ≠ (fun _ => False) → restB r = restN r)
variable (hbtN : ∀ r, restN r κ.bt = bitVal PR.zero PR.one (r = fun _ => False))
variable (hwkB : ∀ r, restB r κ.wk = bitVal PR.zero PR.one (r = fun _ => False))
variable (hNBslot : ∀ s : W, s ≠ κ.wk →
  restB (fun _ => False) s = restN (fun _ => False) s)
variable {p₀ : P} {fc : Q → A}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : ResetRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩

include hrules hR hlin hnebt hnewk hv hAN hNB hbtN hwkB hNBslot in
/-- **The kit resets the marker to the bottom, on a clock**: from the caller's
phase at the marker – whose erasing step is the caller's rule, the one
hypothesis beyond the slot equations – to the landing phase on the empty
address, down the whole order below the marker. -/
theorem reachesIn
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt RF.cell κ.t restA m v) (κ.emb .scan) fc
      (PR.passTracksAt RF.cell κ.t restN m v)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank v + 4)
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell κ.t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .done) fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt RF.cell κ.t restB m) (PR.syElt PR.blank)⟩ :=
  Prog.reachesIn_reset RF hR hlin hnebt hnewk hv hAN hNB hbtN hwkB hNBslot
    (p₀ := p₀) (pScan := κ.emb .scan) (pB := κ.emb .b) (pDone := κ.emb .done)
    (fc := fc) h₀
    (fun _g hg => (has_of_rule hrules (ρ := .down) hg).2 not_false)
    (fun _g hg => (has_of_rule hrules (ρ := .put) hg).1 trivial)
    (fun _g => (has_of_rule hrules (ρ := .back) trivial).2 not_false)

include hrules hR hlin hnebt hnewk hv hAN hNB hbtN hwkB hNBslot in
/-- **The kit resets the marker to the bottom**, the budget forgotten. -/
theorem reaches
    (h₀ : PR.HasRight p₀ fc (PR.passTracksAt RF.cell κ.t restA m v) (κ.emb .scan) fc
      (PR.passTracksAt RF.cell κ.t restN m v)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell κ.t restA m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .done) fc), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt RF.cell κ.t restB m) (PR.syElt PR.blank)⟩ :=
  (reachesIn RF hrules hR hlin hnebt hnewk hv hAN hNB hbtN hwkB hNBslot h₀).reflTransGen

end Discharge

end ResetKit

/-! ### Going home

After a plain sweep the machine stands at the top of the stretch while the
marker never moved: getting back is a scan, not a reset. One phase, one
rule – walk left unless the marker is under the head – and the caller's
exit fires on arrival. -/

namespace Prog

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)

/-- **The walk home, on a budget**: from anywhere at or above the marker, scan
left to it, in the difference of the two ranks. The marker's cell is identified
by its own slot, and nothing on the way is rewritten. -/
theorem reachesIn_home (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t wk : W} (hnewk : wk ≠ t)
    {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {v : Univ A R P K dd → Prop}
    (hwkS : ∀ r : Univ A R P K dd → Prop,
      rest r wk = bitVal PR.zero PR.one (r = v))
    {p : P} {fc : Q → A}
    (hdown : ∀ r : Univ A R P K dd → Prop,
      PR.passTracksAt RF.cell t rest m r wk ≠ PR.one →
      PR.HasLeft p fc (PR.passTracksAt RF.cell t rest m r) p fc (PR.passTracksAt RF.cell t rest m
        r))
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe v s) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank v)
      ⟨Sum.inr (PR.stElt p fc), Sum.inl s,
        wideTape (PR.trackTapeAt RF.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_toCellBackC (cell := RF.cell) (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := rest) (m := m) (p := p) (f := fc)
    (fun r _ hstop => hdown r hstop) (u := v) (s := s)
    (by rw [passTracks_of_ne hnewk, hwkS]; exact bitVal_pos rfl)
    hle
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkS] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)

/-- **The walk home**: from anywhere at or above the marker, scan left to
it. The marker's cell is identified by its own slot, and nothing on the way
is rewritten. -/
theorem reaches_home (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t wk : W} (hnewk : wk ≠ t)
    {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {v : Univ A R P K dd → Prop}
    (hwkS : ∀ r : Univ A R P K dd → Prop,
      rest r wk = bitVal PR.zero PR.one (r = v))
    {p : P} {fc : Q → A}
    (hdown : ∀ r : Univ A R P K dd → Prop,
      PR.passTracksAt RF.cell t rest m r wk ≠ PR.one →
      PR.HasLeft p fc (PR.passTracksAt RF.cell t rest m r) p fc (PR.passTracksAt RF.cell t rest m
        r))
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p fc), Sum.inl s,
        wideTape (PR.trackTapeAt RF.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t rest m) (PR.syElt PR.blank)⟩ :=
  reaches_toCellBackC (cell := RF.cell) (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := rest) (m := m) (p := p) (f := fc)
    (fun r _ hstop => hdown r hstop) (u := v) (s := s)
    (by rw [passTracks_of_ne hnewk, hwkS]; exact bitVal_pos rfl)
    hle
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkS] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)

end Prog

/-- **A home kit**: one phase, one rule – walk left unless the marker is
under the head. The caller's exit, guarded `wk = one ∧ rg ≠ one`, is
disjoint by construction. -/
structure HomeKit (A Q W P : Type) where
  /-- The walked track (rides along unchanged). -/
  t : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phase in the program. -/
  ph : P

namespace HomeKit

/-- **The rule of a home kit.** -/
inductive HomeRule : Type
  /-- Walk left unless the marker is under the head. -/
  | down : HomeRule
  deriving DecidableEq

instance : Finite HomeRule :=
  Finite.of_injective (fun _ => (0 : Fin 1)) (by intro a b _; cases a; cases b; rfl)

variable {A Q W P : Type} (κ : HomeKit A Q W P) (one : A)

/-- **The kit's rule.** -/
def rule : HomeRule → Rule A Q W P
  | .down =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.ph
      dstPh := κ.ph
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

/-- **In-shape separation**: one rule, nothing to separate. -/
theorem sep : ∀ (ρ ρ' : HomeRule) (f : Q → A) (g : W → A),
    (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
    (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' _f _g _hg _hg' _hph
  cases ρ; cases ρ'; rfl

/-- **Exit disjointness**: the rule never fires at the marker. -/
theorem exit_disjoint : ∀ (ρ : HomeRule) (f : Q → A) (g : W → A),
    (κ.rule one ρ).guard f g → g κ.wk = one → False := by
  intro ρ f g hg hwk
  cases ρ
  exact absurd hwk hg

section Discharge

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd} {κ : HomeKit A Q W P}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R P K dd) I ile)
variable {rEmb : HomeRule → R}
variable (hrules : ∀ ρ : HomeRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable (hnewk : κ.wk ≠ κ.t)
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
variable {v : Univ A R P K dd → Prop}
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = v))
variable {fc : Q → A}

include hrules hR hlin hnewk hwkS in
/-- **The kit walks home, on a budget**: from anywhere at or above the marker,
down to it, in the difference of the two ranks. -/
theorem reachesIn {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe v s) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank v)
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s,
        wideTape (PR.trackTapeAt RF.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  Prog.reachesIn_home RF hR hlin hnewk (rest := rest) (m := m) hwkS (p := κ.ph)
    (fc := fc)
    (fun _r hstop =>
      ⟨rEmb .down, by rw [hrules]; exact hstop, by rw [hrules]; rfl,
        by rw [hrules]; rfl, by rw [hrules]; rfl, by rw [hrules]; rfl,
        fun hc => by rw [hrules] at hc; exact hc⟩)
    hle

include hrules hR hlin hnewk hwkS in
/-- **The kit walks home**: from anywhere at or above the marker, down to
it. -/
theorem reaches {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl s,
        wideTape (PR.trackTapeAt RF.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt κ.ph fc), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  Prog.reaches_home RF hR hlin hnewk (rest := rest) (m := m) hwkS (p := κ.ph)
    (fc := fc)
    (fun _r hstop =>
      ⟨rEmb .down, by rw [hrules]; exact hstop, by rw [hrules]; rfl,
        by rw [hrules]; rfl, by rw [hrules]; rfl, by rw [hrules]; rfl,
        fun hc => by rw [hrules] at hc; exact hc⟩)
    hle

end Discharge

end HomeKit

end Draw

end DescriptiveComplexity
