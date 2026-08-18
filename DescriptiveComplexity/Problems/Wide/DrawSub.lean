/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawScan

/-!
# One-cell writes, and tests the tracks can decide

Two corrections to the pass interface, found by trying to discharge it.

**A single-cell write is a step, not a pass.** `Prog.reaches_write` asks for
rules writing `m' u` at *every* pair of a symbol and a cell, which only a
cell-independent `m'` can supply – a rule computes its written symbol from the
tracks it reads, and at a decoupled pair the tracks say nothing about the
cell. Writing one named bit therefore goes: navigate to the cell
(`DescriptiveComplexity.Draw.Prog.reaches_toCell`), then **one step**
(`DescriptiveComplexity.Draw.Prog.step_writeCell` and its rightward twin): the
walked track changes at that cell and nowhere else, which is the coherence
condition `DescriptiveComplexity.Draw.Prog.trackTape_coh` discharges.
`DescriptiveComplexity.Draw.Prog.passTracks_update_cell` is the equation the
rule's written symbol is checked against. (A single-cell *read* needs nothing
new at all: it is `DescriptiveComplexity.Draw.Prog.step_move` or its twin with
an unchanged background, the phase branching on the digit the rule reads.)

**A file test must be decided by the tracks.** `Prog.reaches_test` takes its
question as a predicate of the *cell*, quantified independently of the symbol,
so a deterministic table cannot serve both its pass and its fail hypotheses.
`DescriptiveComplexity.Draw.Prog.reaches_fileTestG` restates it with the question a
predicate `TestG` of the **tracks**, tied to the cell-level question by one
compatibility hypothesis – which is how the machine actually asks it: MIRROR =
TARGET is one slot against another, a well-shapedness check is the name marks,
and so on.

What indexes the register file is a parameter throughout, as it is from
`DescriptiveComplexity.IxFile` upwards: a program on a clock cannot give every
element of the universe a register, and none of these passes care which does.
A *track* is a predicate on the index and an *address* is a predicate on the
universe; at the file a space-bounded program uses the two are the same type,
which is why the diagonal reads as it does.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {I : Type} [Finite I] {ile : I → I → Prop}
variable {PR : Prog A R P Q W K dd}

/-! ### Updating a track at one cell -/

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Finite I] in
/-- **The tracks at a cell whose walked track was updated there**: the update of
the tracks. This is the equation a writing rule's symbol is checked against. -/
theorem passTracks_update_cell (F : IxFile (Univ A R P K dd) I ile) (hix : IsLinOrd ile)
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A}
    (m : I → Prop) {b : Prop} (u : I) :
    PR.passTracksAt F.cell t rest (fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v)) (F.cell u) =
      Function.update (PR.passTracksAt F.cell t rest m (F.cell u)) t
        (bitVal PR.zero PR.one b) := by
  rw [passTracks_cell F hix, passTracks_cell F hix]
  refine funext fun s => ?_
  by_cases hs : s = t
  · subst hs
    rw [Function.update_self, if_pos rfl]
    exact bitVal_congr ⟨fun hc => hc.elim (fun h => h.2) fun h => absurd rfl h.1,
      fun hb => Or.inl ⟨rfl, hb⟩⟩
  · rw [Function.update_of_ne hs, if_neg hs, if_neg hs]

omit [Finite I] in
/-- **One step writing the walked track at a register cell**, moving left: the
program stands on the cell, one rule rewrites the track's digit there – to
`b`, whatever it read – and the head steps to the predecessor. The rest of the
track and every other track ride along. -/
theorem step_writeCell (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {u : I} {v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v' (F.cell u))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {b : Prop} {p p' : P} {f f' : Q → A}
    (hrule : PR.HasLeft p f (PR.passTracksAt F.cell t rest m (F.cell u)) p' f'
      (Function.update (PR.passTracksAt F.cell t rest m (F.cell u)) t
        (bitVal PR.zero PR.one b))) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t rest fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v))
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasLeft hR hrule
  rw [← trackTapeAt_eq] at hread
  rw [← passTracks_update_cell F hix m u] at hwrite
  rw [← trackTapeAt_eq] at hwrite
  refine step_wideTape_left hlin hi htr hsrc hread hdst hwrite hright fun r hr => ?_
  exact PR.trackTapeAt_coh F.cell t rest _ m u (fun v hv => ⟨fun hc => (hc.resolve_left
    fun h => absurd h.1 hv).2, fun hm => Or.inr ⟨hv, hm⟩⟩) r hr

omit [Finite I] in
/-- **One step writing the walked track at a register cell**, moving right. -/
theorem step_writeCellRight (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {u : I} {v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe (F.cell u) v')
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {b : Prop} {p p' : P} {f f' : Q → A}
    (hrule : PR.HasRight p f (PR.passTracksAt F.cell t rest m (F.cell u)) p' f'
      (Function.update (PR.passTracksAt F.cell t rest m (F.cell u)) t
        (bitVal PR.zero PR.one b))) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell t rest fun v => (v = u ∧ b) ∨ (v ≠ u ∧ m v))
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasRight hR hrule
  rw [← trackTapeAt_eq] at hread
  rw [← passTracks_update_cell F hix m u] at hwrite
  rw [← trackTapeAt_eq] at hwrite
  refine step_wideTape_right hlin hi htr hsrc hread hdst hwrite hright fun r hr => ?_
  exact PR.trackTapeAt_coh F.cell t rest _ m u (fun v hv => ⟨fun hc => (hc.resolve_left
    fun h => absurd h.1 hv).2, fun hm => Or.inr ⟨hv, hm⟩⟩) r hr

/-! ### A file test the tracks decide -/

/-- **A program tests its register file by a question of the tracks.** As
`DescriptiveComplexity.Draw.Prog.reaches_test`, but the question is a predicate
of the *symbol* – which is what a deterministic rule can branch on – tied to
the per-cell question by the compatibility hypothesis. The verdict comes back
in the phase: the passing one exactly when every register passed. -/
theorem reachesIn_fileTestG (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {Test : I → Prop} {TestG : (W → A) → Prop} {m : I → Prop}
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hcompat : ∀ u : I,
      TestG (PR.passTracksAt F.cell t rest m (F.cell u)) ↔ Test u)
    {py pn : P} {f : Q → A}
    (hpass : ∀ g : W → A, TestG g → g rg = PR.one → PR.HasLeft py f g py f g)
    (hfail : ∀ g : W → A, ¬TestG g → g rg = PR.one → PR.HasLeft py f g pn f g)
    (hheld : ∀ g : W → A, g rg = PR.one → PR.HasLeft pn f g pn f g)
    (hwalkY : ∀ r : Univ A R P K dd → Prop,
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft py f (PR.passTracksAt F.cell t rest m r) py f (PR.passTracksAt F.cell t rest m r))
    (hwalkN : ∀ r : Univ A R P K dd → Prop,
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pn f (PR.passTracksAt F.cell t rest m r) pn f (PR.passTracksAt F.cell t rest m r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt py f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (accStateAfter ile Test (PR.stElt py f) (PR.stElt pn f) bot), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ u : I,
      PR.passTracksAt F.cell t rest m (F.cell u) rg = PR.one := fun u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine F.reachesIn_fileTest (P := Test) hix hlin (w := w) hgap (b := PR.syElt PR.blank)
    (f := PR.trackTapeAt F.cell t rest m) (qy := PR.stElt py f) (qn := PR.stElt pn f)
    (fun u hu => ?_) (fun u hu => ?_) (fun w => ?_) (fun q hq r hbnd hno => ?_) htop hbot
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hpass _ ((hcompat u).mpr hu) (hrgSeg u))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hfail _ (fun hc => hu ((hcompat u).mp hc)) (hrgSeg u))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hheld _ (hrgSeg w))
  · rw [trackTapeAt_eq]
    rcases hq with rfl | rfl
    · exact step_of_hasLeft hR (hwalkY r hbnd hno)
    · exact step_of_hasLeft hR (hwalkN r hbnd hno)

/-- **A program tests its register file by a question of the tracks**, the budget
forgotten. -/
theorem reaches_fileTestG (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {Test : I → Prop} {TestG : (W → A) → Prop} {m : I → Prop}
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hcompat : ∀ u : I,
      TestG (PR.passTracksAt F.cell t rest m (F.cell u)) ↔ Test u)
    {py pn : P} {f : Q → A}
    (hpass : ∀ g : W → A, TestG g → g rg = PR.one → PR.HasLeft py f g py f g)
    (hfail : ∀ g : W → A, ¬TestG g → g rg = PR.one → PR.HasLeft py f g pn f g)
    (hheld : ∀ g : W → A, g rg = PR.one → PR.HasLeft pn f g pn f g)
    (hwalkY : ∀ r : Univ A R P K dd → Prop,
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft py f (PR.passTracksAt F.cell t rest m r) py f (PR.passTracksAt F.cell t rest m r))
    (hwalkN : ∀ r : Univ A R P K dd → Prop,
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pn f (PR.passTracksAt F.cell t rest m r) pn f (PR.passTracksAt F.cell t rest m r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt py f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (accStateAfter ile Test (PR.stElt py f) (PR.stElt pn f) bot), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hrun⟩ := reachesIn_fileTestG F hR hlin hix hne hrest hcompat hpass hfail
    hheld hwalkY hwalkN
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) htop hbot
  exact ⟨q, hq, hrun.reflTransGen⟩

/-! ### Whole-track writes the tracks can decide

The two whole-track writes the program needs – clearing a register and copying
one register into another – have their written value computable from the
symbol under the head (a constant, or another slot of the same cell), which is
exactly what a deterministic rule can do. They are
`DescriptiveComplexity.reaches_fileWrite` with the coupling supplied. -/

/-- **Clearing a track**: one pass down the file writing the clear digit at
every register. -/
theorem reachesIn_fileClearTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t PR.zero))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest fun _ => False) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : I → Prop) (u : I),
      PR.passTracksAt F.cell t rest k (F.cell u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine F.reachesIn_fileWrite hix hlin (t := fun _ => False) (w := w) hgap
    (b := PR.syElt PR.blank)
    (tapeOf := PR.trackTapeAt F.cell t rest) (q := PR.stElt p f)
    (PR.trackTapeAt_coh F.cell t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hwrite : PR.passTracksAt F.cell t rest
        (fun v => (v = u ∧ False) ∨ (v ≠ u ∧ k v)) (F.cell u) =
        Function.update (PR.passTracksAt F.cell t rest k (F.cell u)) t PR.zero := by
      rw [passTracks_update_cell F hix]
      rw [bitVal_neg not_false]
    rw [trackTapeAt_eq, trackTapeAt_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

/-- **Clearing a track**, the budget forgotten. -/
theorem reaches_fileClearTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t PR.zero))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest fun _ => False) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hrun⟩ := reachesIn_fileClearTrack F hR hlin hix hne hrest hput hwalk
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) htop hbot
  exact ⟨q, hq, hrun.reflTransGen⟩

/-- **Copying one track into another**: one pass down the file, each register's
walked digit replaced by its digit on the source slot, which must be a bit
there. SAV := MIRROR and TARGET := SAV are this pass. -/
theorem reachesIn_fileCopyTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg src : W} (hne : t ≠ rg) (hnesrc : src ≠ t)
    {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hsrcBit : ∀ u : I,
      rest (F.cell u) src = PR.zero ∨ rest (F.cell u) src = PR.one)
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (g src)))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest fun u => rest (F.cell u) src = PR.one)
            (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : I → Prop) (u : I),
      PR.passTracksAt F.cell t rest k (F.cell u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  refine F.reachesIn_fileWrite hix hlin (t := fun u => rest (F.cell u) src = PR.one)
    (w := w) hgap
    (b := PR.syElt PR.blank) (tapeOf := PR.trackTapeAt F.cell t rest) (q := PR.stElt p f)
    (PR.trackTapeAt_coh F.cell t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hsrcVal : PR.passTracksAt F.cell t rest k (F.cell u) src = rest (F.cell u) src :=
      passTracks_of_ne hnesrc k (F.cell u)
    have hpredEq : (fun v => (v = u ∧ rest (F.cell v) src = PR.one) ∨ (v ≠ u ∧ k v)) =
        fun v => (v = u ∧ rest (F.cell u) src = PR.one) ∨ (v ≠ u ∧ k v) :=
      funext fun v => propext
        (or_congr (and_congr_right fun hv => by rw [hv]) Iff.rfl)
    have hwrite : PR.passTracksAt F.cell t rest
        (fun v => (v = u ∧ rest (F.cell v) src = PR.one) ∨ (v ≠ u ∧ k v)) (F.cell u) =
        Function.update (PR.passTracksAt F.cell t rest k (F.cell u)) t
          (PR.passTracksAt F.cell t rest k (F.cell u) src) := by
      rw [hpredEq, passTracks_update_cell F hix, hsrcVal]
      rcases hsrcBit u with h0 | h1
      · rw [h0, bitVal_neg PR.zero_ne_one]
      · rw [h1, bitVal_pos rfl]
    rw [trackTapeAt_eq, trackTapeAt_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

/-- **Copying one track into another**, the budget forgotten. -/
theorem reaches_fileCopyTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg src : W} (hne : t ≠ rg) (hnesrc : src ≠ t)
    {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    (hsrcBit : ∀ u : I,
      rest (F.cell u) src = PR.zero ∨ rest (F.cell u) src = PR.one)
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (g src)))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest fun u => rest (F.cell u) src = PR.one)
            (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hrun⟩ := reachesIn_fileCopyTrack F hR hlin hix hne hnesrc hrest hsrcBit hput hwalk
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) htop hbot
  exact ⟨q, hq, hrun.reflTransGen⟩

/-- **Rewriting a track by a function of the other tracks**: one pass down
the file, each register's walked digit replaced by a bit the tracks at that
cell decide – provided the function ignores the walked slot itself, which is
what makes the written value independent of the pass's own progress.
Clearing and copying are special cases; the pattern writes of the program –
a target register loaded with a pattern of the marks – are the general
one. -/
theorem reachesIn_fileMapTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {Fb : (W → A) → Prop}
    (hFb : ∀ g g' : W → A, (∀ s : W, s ≠ t → g s = g' s) → (Fb g ↔ Fb g'))
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (bitVal PR.zero PR.one (Fb g))))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest
            fun u => Fb (PR.passTracksAt F.cell t rest m (F.cell u))) (PR.syElt PR.blank)⟩ := by
  have hrgSeg : ∀ (k : I → Prop) (u : I),
      PR.passTracksAt F.cell t rest k (F.cell u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  -- the target digit at a cell does not depend on the walked track there
  have hsame : ∀ (k : I → Prop) (u : I),
      Fb (PR.passTracksAt F.cell t rest k (F.cell u)) ↔
        Fb (PR.passTracksAt F.cell t rest m (F.cell u)) :=
    fun k u => hFb _ _ fun s hs => by
      rw [passTracks_of_ne hs, passTracks_of_ne hs]
  refine F.reachesIn_fileWrite hix hlin
    (t := fun u => Fb (PR.passTracksAt F.cell t rest m (F.cell u)))
    (w := w) hgap
    (b := PR.syElt PR.blank) (tapeOf := PR.trackTapeAt F.cell t rest) (q := PR.stElt p f)
    (PR.trackTapeAt_coh F.cell t rest) (fun k u => ?_) (fun k r hbnd hno => ?_) htop hbot
  · have hpredEq : (fun v => (v = u ∧ Fb (PR.passTracksAt F.cell t rest m (F.cell v))) ∨
        (v ≠ u ∧ k v)) =
        fun v => (v = u ∧ Fb (PR.passTracksAt F.cell t rest m (F.cell u))) ∨ (v ≠ u ∧ k v) :=
      funext fun v => propext
        (or_congr (and_congr_right fun hv => by rw [hv]) Iff.rfl)
    have hwrite : PR.passTracksAt F.cell t rest
        (fun v => (v = u ∧ Fb (PR.passTracksAt F.cell t rest m (F.cell v))) ∨ (v ≠ u ∧ k v))
          (F.cell u) =
        Function.update (PR.passTracksAt F.cell t rest k (F.cell u)) t
          (bitVal PR.zero PR.one (Fb (PR.passTracksAt F.cell t rest k (F.cell u)))) := by
      rw [hpredEq, passTracks_update_cell F hix]
      exact congrArg _ (bitVal_congr (hsame k u).symm)
    rw [trackTapeAt_eq, trackTapeAt_eq, hwrite]
    exact step_of_hasLeft hR (hput _ (hrgSeg k u))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hwalk k r hbnd hno)

/-- **Rewriting a track by a function of the other tracks**, the budget
forgotten. -/
theorem reaches_fileMapTrack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {Fb : (W → A) → Prop}
    (hFb : ∀ g g' : W → A, (∀ s : W, s ≠ t → g s = g' s) → (Fb g ↔ Fb g'))
    {m : I → Prop} {p : P} {f : Q → A}
    (hput : ∀ g : W → A, g rg = PR.one →
      PR.HasLeft p f g p f (Function.update g t (bitVal PR.zero PR.one (Fb g))))
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft p f (PR.passTracksAt F.cell t rest k r) p f (PR.passTracksAt F.cell t rest k r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell t rest
            fun u => Fb (PR.passTracksAt F.cell t rest m (F.cell u))) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hrun⟩ := reachesIn_fileMapTrack F hR hlin hix hne hrest hFb hput hwalk
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) htop hbot
  exact ⟨q, hq, hrun.reflTransGen⟩

end Prog

end Draw

end DescriptiveComplexity
