/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpScan

/-!
# One-cell writes, and tests the tracks can decide

Two corrections to the pass interface, found by trying to discharge it.

**A single-cell write is a step, not a pass.** `Prog.reaches_write` asks for
rules writing `m' u` at *every* pair of a symbol and a cell, which only a
cell-independent `m'` can supply – a rule computes its written symbol from the
tracks it reads, and at a decoupled pair the tracks say nothing about the
cell. Writing one named bit therefore goes: navigate to the cell
(`DescriptiveComplexity.Pfp.Prog.reaches_toCell`), then **one step**
(`DescriptiveComplexity.Pfp.Prog.step_writeReg` and its rightward twin): the
walked track changes at that cell and nowhere else, which is the coherence
condition `DescriptiveComplexity.Pfp.Prog.trackTape_coh` discharges.
`DescriptiveComplexity.Pfp.Prog.passTracks_update_wmSeg` is the equation the
rule's written symbol is checked against. (A single-cell *read* needs nothing
new at all: it is `DescriptiveComplexity.Pfp.Prog.step_move` or its twin with
an unchanged background, the phase branching on the digit the rule reads.)

**A file test must be decided by the tracks.** `Prog.reaches_test` takes its
question as a predicate of the *cell*, quantified independently of the symbol,
so a deterministic table cannot serve both its pass and its fail hypotheses.
`DescriptiveComplexity.Pfp.Prog.reaches_testG` restates it with the question a
predicate `TestG` of the **tracks**, tied to the cell-level question by one
compatibility hypothesis – which is how the machine actually asks it: MIRROR =
TARGET is one slot against another, a well-shapedness check is the name marks,
and so on.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}

/-! ### Updating a track at one cell -/

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **The tracks at a cell whose walked track was updated there**: the update of
the tracks. This is the equation a writing rule's symbol is checked against. -/
theorem passTracks_update_wmSeg
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A}
    (m : Univ A R P K dd → Prop) {b : Prop} (u : Univ A R P K dd) :
    PR.passTracks t rest (fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v)) (wmSeg u) =
      Function.update (PR.passTracks t rest m (wmSeg u)) t (bitVal PR.zero PR.one b) := by
  rw [passTracks_wmSeg hlin, passTracks_wmSeg hlin]
  refine funext fun s => ?_
  by_cases hs : s = t
  · subst hs
    rw [Function.update_self, if_pos rfl]
    exact bitVal_congr ⟨fun hc => hc.elim (fun h => h.2) fun h => absurd rfl h.1,
      fun hb => Or.inl ⟨rfl, hb⟩⟩
  · rw [Function.update_of_ne hs, if_neg hs, if_neg hs]

/-- **One step writing the walked track at a register cell**, moving left: the
program stands on the cell, one rule rewrites the track's digit there – to
`b`, whatever it read – and the head steps to the predecessor. The rest of the
track and every other track ride along. -/
theorem step_writeReg (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {u : Univ A R P K dd} {v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v' (wmSeg u))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
    {b : Prop} {p p' : P} {f f' : Q → A}
    (hrule : PR.HasLeft p f (PR.passTracks t rest m (wmSeg u)) p' f'
      (Function.update (PR.passTracks t rest m (wmSeg u)) t (bitVal PR.zero PR.one b))) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl (wmSeg u),
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTape t rest fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v))
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasLeft hR hrule
  rw [← trackTape_eq] at hread
  rw [← passTracks_update_wmSeg hlin m u] at hwrite
  rw [← trackTape_eq] at hwrite
  refine step_wideTape_left hlin hi htr hsrc hread hdst hwrite hright fun r hr => ?_
  exact PR.trackTape_coh t rest _ m u (fun v hv => ⟨fun hc => (hc.resolve_left
    fun h => absurd h.1 hv).2, fun hm => Or.inr ⟨hv, hm⟩⟩) r hr

/-- **One step writing the walked track at a register cell**, moving right. -/
theorem step_writeRegRight (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {u : Univ A R P K dd} {v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe (wmSeg u) v')
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
    {b : Prop} {p p' : P} {f f' : Q → A}
    (hrule : PR.HasRight p f (PR.passTracks t rest m (wmSeg u)) p' f'
      (Function.update (PR.passTracks t rest m (wmSeg u)) t (bitVal PR.zero PR.one b))) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl (wmSeg u),
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTape t rest fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v))
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasRight hR hrule
  rw [← trackTape_eq] at hread
  rw [← passTracks_update_wmSeg hlin m u] at hwrite
  rw [← trackTape_eq] at hwrite
  refine step_wideTape_right hlin hi htr hsrc hread hdst hwrite hright fun r hr => ?_
  exact PR.trackTape_coh t rest _ m u (fun v hv => ⟨fun hc => (hc.resolve_left
    fun h => absurd h.1 hv).2, fun hm => Or.inr ⟨hv, hm⟩⟩) r hr

/-! ### A file test the tracks decide -/

/-- **A program tests its register file by a question of the tracks.** As
`DescriptiveComplexity.Pfp.Prog.reaches_test`, but the question is a predicate
of the *symbol* – which is what a deterministic rule can branch on – tied to
the per-cell question by the compatibility hypothesis. The verdict comes back
in the phase: the passing one exactly when every register passed. -/
theorem reaches_testG (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {Test : Univ A R P K dd → Prop} {TestG : (W → A) → Prop} {m : Univ A R P K dd → Prop}
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
    (hcompat : ∀ u : Univ A R P K dd,
      TestG (PR.passTracks t rest m (wmSeg u)) ↔ Test u)
    {py pn : P} {f : Q → A}
    (hpass : ∀ g : W → A, TestG g → g rg = PR.one → PR.HasLeft py f g py f g)
    (hfail : ∀ g : W → A, ¬TestG g → g rg = PR.one → PR.HasLeft py f g pn f g)
    (hheld : ∀ g : W → A, g rg = PR.one → PR.HasLeft pn f g pn f g)
    (hwalkY : ∀ r : Univ A R P K dd → Prop,
      (∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : Univ A R P K dd, r ≠ wmSeg x) →
      PR.HasLeft py f (PR.passTracks t rest m r) py f (PR.passTracks t rest m r))
    (hwalkN : ∀ r : Univ A R P K dd → Prop,
      (∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : Univ A R P K dd, r ≠ wmSeg x) →
      PR.HasLeft pn f (PR.passTracks t rest m r) pn f (PR.passTracks t rest m r))
    {top bot : Univ A R P K dd} (htop : ∀ v, WMLe v top) (hbot : ∀ v, WMLe bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (wmSeg bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt py f), Sum.inl (wmSeg top),
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (accStateAfter Test (PR.stElt py f) (PR.stElt pn f) bot), Sum.inl q,
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ u : Univ A R P K dd, PR.passTracks t rest m (wmSeg u) rg = PR.one := fun u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine reaches_fileTest (P := Test) hlin (b := PR.syElt PR.blank)
    (f := PR.trackTape t rest m) (qy := PR.stElt py f) (qn := PR.stElt pn f)
    (fun u hu => ?_) (fun u hu => ?_) (fun w => ?_) (fun q hq r hbnd hno => ?_) htop hbot
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hpass _ ((hcompat u).mpr hu) (hrgSeg u))
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hfail _ (fun hc => hu ((hcompat u).mp hc)) (hrgSeg u))
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hheld _ (hrgSeg w))
  · rw [trackTape_eq]
    rcases hq with rfl | rfl
    · exact step_of_hasLeft hR (hwalkY r hbnd hno)
    · exact step_of_hasLeft hR (hwalkN r hbnd hno)

/-! ### Whole-track writes the tracks can decide

The two whole-track writes the program needs – clearing a register and copying
one register into another – have their written value computable from the
symbol under the head (a constant, or another slot of the same cell), which is
exactly what a deterministic rule can do. They are
`DescriptiveComplexity.reaches_fileWrite` with the coupling supplied. -/

/-- **Clearing a track**: one pass down the file writing the clear digit at
every register. -/
theorem reaches_clearTrack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
    {m : Univ A R P K dd → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t PR.zero))
    (hwalk : ∀ k r : Univ A R P K dd → Prop,
      (∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : Univ A R P K dd, r ≠ wmSeg x) →
      PR.HasLeft p f (PR.passTracks t rest k r) p f (PR.passTracks t rest k r))
    {top bot : Univ A R P K dd} (htop : ∀ v, WMLe v top) (hbot : ∀ v, WMLe bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (wmSeg bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (wmSeg top),
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTape t rest fun _ => False) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : Univ A R P K dd → Prop) (u : Univ A R P K dd),
      PR.passTracks t rest k (wmSeg u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine reaches_fileWrite (t := fun _ => False) hlin (b := PR.syElt PR.blank)
    (tapeOf := PR.trackTape t rest) (q := PR.stElt p f)
    (PR.trackTape_coh t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hwrite : PR.passTracks t rest
        (fun v => (v = u ∧ False) ∨ (v ≠ u ∧ k v)) (wmSeg u) =
        Function.update (PR.passTracks t rest k (wmSeg u)) t PR.zero := by
      rw [passTracks_update_wmSeg hlin]
      rw [bitVal_neg not_false]
    rw [trackTape_eq, trackTape_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

/-- **Copying one track into another**: one pass down the file, each register's
walked digit replaced by its digit on the source slot, which must be a bit
there. SAV := MIRROR and TARGET := SAV are this pass. -/
theorem reaches_copyTrack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t rg src : W} (hne : t ≠ rg) (hnesrc : src ≠ t)
    {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
    (hsrcBit : ∀ u : Univ A R P K dd,
      rest (wmSeg u) src = PR.zero ∨ rest (wmSeg u) src = PR.one)
    {m : Univ A R P K dd → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (g src)))
    (hwalk : ∀ k r : Univ A R P K dd → Prop,
      (∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : Univ A R P K dd, r ≠ wmSeg x) →
      PR.HasLeft p f (PR.passTracks t rest k r) p f (PR.passTracks t rest k r))
    {top bot : Univ A R P K dd} (htop : ∀ v, WMLe v top) (hbot : ∀ v, WMLe bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (wmSeg bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (wmSeg top),
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTape t rest fun u => rest (wmSeg u) src = PR.one)
            (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : Univ A R P K dd → Prop) (u : Univ A R P K dd),
      PR.passTracks t rest k (wmSeg u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine reaches_fileWrite (t := fun u => rest (wmSeg u) src = PR.one) hlin
    (b := PR.syElt PR.blank) (tapeOf := PR.trackTape t rest) (q := PR.stElt p f)
    (PR.trackTape_coh t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hsrcVal : PR.passTracks t rest k (wmSeg u) src = rest (wmSeg u) src :=
      passTracks_of_ne hnesrc k (wmSeg u)
    have hpredEq : (fun v => (v = u ∧ rest (wmSeg v) src = PR.one) ∨ (v ≠ u ∧ k v)) =
        fun v => (v = u ∧ rest (wmSeg u) src = PR.one) ∨ (v ≠ u ∧ k v) :=
      funext fun v => propext
        (or_congr (and_congr_right fun hv => by rw [hv]) Iff.rfl)
    have hwrite : PR.passTracks t rest
        (fun v => (v = u ∧ rest (wmSeg v) src = PR.one) ∨ (v ≠ u ∧ k v)) (wmSeg u) =
        Function.update (PR.passTracks t rest k (wmSeg u)) t
          (PR.passTracks t rest k (wmSeg u) src) := by
      rw [hpredEq, passTracks_update_wmSeg hlin, hsrcVal]
      rcases hsrcBit u with h0 | h1
      · rw [h0, bitVal_neg PR.zero_ne_one]
      · rw [h1, bitVal_pos rfl]
    rw [trackTape_eq, trackTape_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

/-- **Rewriting a track by a function of the other tracks**: one pass down
the file, each register's walked digit replaced by a bit the tracks at that
cell decide – provided the function ignores the walked slot itself, which is
what makes the written value independent of the pass's own progress.
Clearing and copying are special cases; the pattern writes of the program –
a target register loaded with a pattern of the marks – are the general
one. -/
theorem reaches_mapTrack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : Univ A R P K dd, r = wmSeg u))
    {Fb : (W → A) → Prop}
    (hFb : ∀ g g' : W → A, (∀ s : W, s ≠ t → g s = g' s) → (Fb g ↔ Fb g'))
    {m : Univ A R P K dd → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (bitVal PR.zero PR.one (Fb g))))
    (hwalk : ∀ k r : Univ A R P K dd → Prop,
      (∃ x : Univ A R P K dd, WMSetLe WMLe (wmSeg x) r) →
      (∀ x : Univ A R P K dd, r ≠ wmSeg x) →
      PR.HasLeft p f (PR.passTracks t rest k r) p f (PR.passTracks t rest k r))
    {top bot : Univ A R P K dd} (htop : ∀ v, WMLe v top) (hbot : ∀ v, WMLe bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (wmSeg bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (wmSeg top),
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTape t rest
            fun u => Fb (PR.passTracks t rest m (wmSeg u))) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : Univ A R P K dd → Prop) (u : Univ A R P K dd),
      PR.passTracks t rest k (wmSeg u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  -- the target digit at a cell does not depend on the walked track there
  have hsame : ∀ (k : Univ A R P K dd → Prop) (u : Univ A R P K dd),
      Fb (PR.passTracks t rest k (wmSeg u)) ↔ Fb (PR.passTracks t rest m (wmSeg u)) :=
    fun k u => hFb _ _ fun s hs => by
      rw [passTracks_of_ne hs, passTracks_of_ne hs]
  refine reaches_fileWrite (t := fun u => Fb (PR.passTracks t rest m (wmSeg u))) hlin
    (b := PR.syElt PR.blank) (tapeOf := PR.trackTape t rest) (q := PR.stElt p f)
    (PR.trackTape_coh t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hpredEq : (fun v => (v = u ∧ Fb (PR.passTracks t rest m (wmSeg v))) ∨
        (v ≠ u ∧ k v)) =
        fun v => (v = u ∧ Fb (PR.passTracks t rest m (wmSeg u))) ∨ (v ≠ u ∧ k v) :=
      funext fun v => propext
        (or_congr (and_congr_right fun hv => by rw [hv]) Iff.rfl)
    have hwrite : PR.passTracks t rest
        (fun v => (v = u ∧ Fb (PR.passTracks t rest m (wmSeg v))) ∨ (v ≠ u ∧ k v))
          (wmSeg u) =
        Function.update (PR.passTracks t rest k (wmSeg u)) t
          (bitVal PR.zero PR.one (Fb (PR.passTracks t rest k (wmSeg u)))) := by
      rw [hpredEq, passTracks_update_wmSeg hlin]
      exact congrArg _ (bitVal_congr (hsame k u).symm)
    rw [trackTape_eq, trackTape_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTape_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

end Prog

end Pfp

end DescriptiveComplexity
