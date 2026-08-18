/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltPos

/-!
# The intended run: the guessing sweeps

The `k` sweeps of the machine, run against a tuple of block assignments. The
whole point is `DescriptiveComplexity.AltQbf.valAfter`: the truth value the cell of a
variable holds once the sweeps below `i` have run is the disjunction, over the
blocks *below `i`* marking it, of what they assigned it. At `i = k` that is
`DescriptiveComplexity.qbfVal` exactly
(`DescriptiveComplexity.AltQbf.valAfter_top`), which is why one bit per cell suffices
even though a variable may carry several block marks.

A sweep runs rightwards writing, turns at `⊣`, runs back leftwards unchanged,
and hands over at `⊢`. The tape during the rightward pass is
`DescriptiveComplexity.AltQbf.sweepTape`: cells strictly below the head already hold
the new value, cells at or above still hold the old one. Junk cells – a cell's
tag on a tuple that is not a position – are frozen at `false`, which is what
`DescriptiveComplexity.AltQbf.AltInp` gives them and what the frame condition of every
step then preserves.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Sweep

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The value a cell holds between sweeps -/

open Classical in
/-- The truth value the cell of `x` holds once the sweeps below `i` have run. -/
noncomputable def valAfter (νs : Fin k → A → Prop) (i : ℕ) (x : A) : Bool :=
  decide (∃ j : Fin k, (j : ℕ) < i ∧ QbfBlk j x ∧ νs j x)

variable {νs : Fin k → A → Prop} {x : A}

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Reading `DescriptiveComplexity.AltQbf.valAfter` back. -/
theorem valAfter_eq_true {i : ℕ} :
    valAfter νs i x = true ↔ ∃ j : Fin k, (j : ℕ) < i ∧ QbfBlk j x ∧ νs j x := by
  classical
  simp only [valAfter, decide_eq_true_eq]

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem valAfter_zero : valAfter νs 0 x = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨j, hj, -⟩ := valAfter_eq_true.mp h
  omega

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **After the last sweep a cell holds the truth value of its variable.** -/
theorem valAfter_top : valAfter νs k x = true ↔ qbfVal νs x := by
  refine valAfter_eq_true.trans ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, -, hb, hv⟩ := h
    exact ⟨j, hb, hv⟩
  · obtain ⟨j, hb, hv⟩ := h
    exact ⟨j, j.isLt, hb, hv⟩

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- A sweep leaves a cell alone when its block does not set it. -/
theorem valAfter_succ_of_keep {i : ℕ}
    (h : ¬∃ j : Fin k, (j : ℕ) = i ∧ QbfBlk j x ∧ νs j x) :
    valAfter νs (i + 1) x = valAfter νs i x := by
  rcases Bool.eq_false_or_eq_true (valAfter νs i x) with hv | hv
  · rw [hv]
    obtain ⟨j, hj, hb, hν⟩ := valAfter_eq_true.mp hv
    exact valAfter_eq_true.mpr ⟨j, by omega, hb, hν⟩
  · rw [hv, Bool.eq_false_iff]
    intro hcon
    obtain ⟨j, hj, hb, hν⟩ := valAfter_eq_true.mp hcon
    rcases Nat.lt_or_ge (j : ℕ) i with hlt | hge
    · exact absurd (valAfter_eq_true.mpr ⟨j, hlt, hb, hν⟩) (by rw [hv]; simp)
    · exact h ⟨j, by omega, hb, hν⟩

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- A sweep sets a cell when its block marks the variable and assigns it
`true`. -/
theorem valAfter_succ_of_set {i : ℕ}
    (h : ∃ j : Fin k, (j : ℕ) = i ∧ QbfBlk j x ∧ νs j x) :
    valAfter νs (i + 1) x = true := by
  obtain ⟨j, hj, hb, hν⟩ := h
  exact valAfter_eq_true.mpr ⟨j, by omega, hb, hν⟩

/-! ### Changing one block's assignment

The read-off of a round replaces the assignment of the block that has just
played, and leaves the others alone. These are the two facts that makes such a
replacement invisible to the sweeps below it and exactly visible to its own. -/

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Only the blocks below `m` matter to what a cell holds after `m` sweeps. -/
theorem valAfter_congr {ρ σ : Fin k → A → Prop} {m : ℕ}
    (h : ∀ j : Fin k, (j : ℕ) < m → (ρ j x ↔ σ j x)) : valAfter ρ m x = valAfter σ m x := by
  refine Bool.eq_iff_iff.mpr ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨j, hj, hb, hν⟩ := valAfter_eq_true.mp hh
    exact valAfter_eq_true.mpr ⟨j, hj, hb, (h j hj).mp hν⟩
  · obtain ⟨j, hj, hb, hν⟩ := valAfter_eq_true.mp hh
    exact valAfter_eq_true.mpr ⟨j, hj, hb, (h j hj).mpr hν⟩

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **Replacing block `i`'s assignment does not change what the sweeps below it
wrote.** -/
theorem valAfter_update_le {i : Fin k} {ν' : A → Prop} {m : ℕ} (hm : m ≤ (i : ℕ)) :
    valAfter (Function.update νs i ν') m x = valAfter νs m x := by
  classical
  refine valAfter_congr fun j hj => ?_
  have hne : j ≠ i := fun hcon => by
    rw [hcon] at hj
    omega
  rw [Function.update_of_ne hne]

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **Replacing block `i`'s assignment changes exactly what its own sweep
writes.** -/
theorem valAfter_update_succ {i : Fin k} {ν' : A → Prop} :
    valAfter (Function.update νs i ν') ((i : ℕ) + 1) x = true ↔
      (valAfter νs (i : ℕ) x = true ∨ (QbfBlk i x ∧ ν' x)) := by
  classical
  rw [valAfter_eq_true]
  constructor
  · rintro ⟨j, hj, hb, hν⟩
    rcases eq_or_ne j i with rfl | hne
    · refine Or.inr ⟨hb, ?_⟩
      rwa [Function.update_self] at hν
    · refine Or.inl (valAfter_eq_true.mpr ⟨j, ?_, hb, by rwa [Function.update_of_ne hne] at hν⟩)
      have : (j : ℕ) ≠ (i : ℕ) := fun hcon => hne (Fin.ext hcon)
      omega
  · rintro (h | ⟨hb, hν⟩)
    · obtain ⟨j, hj, hbj, hνj⟩ := valAfter_eq_true.mp h
      have hne : j ≠ i := fun hcon => by
        rw [hcon] at hj
        omega
      exact ⟨j, by omega, hbj, by rwa [Function.update_of_ne hne]⟩
    · exact ⟨i, by omega, hb, by rwa [Function.update_self]⟩

/-! ### The tape between and during the sweeps -/

/-- Whether a tuple carrying a cell's tag is a real cell of the tape. -/
def IsCellTup (q : AltV k A) : Prop := (q.1.2 : ℕ) = 0 ∧ ∀ a : A, q.2 1 ≤ a

open Classical in
/-- The tape once the sweeps below `i` have run: every real cell holds the
value its variable has accumulated, the markers hold their own symbols, junk
cells are frozen at `false`, and everything else reads blank. -/
noncomputable def tapeAfter (νs : Fin k → A → Prop) (i : ℕ) (q : AltV k A) : AltV k A :=
  match q.1.1 with
  | .pStart => symStart
  | .pEnd => symEnd
  | .pCell => if IsCellTup q then symV (valAfter νs i (q.2 0)) (q.2 0) else symV false (q.2 0)
  | _ => symBlank

open Classical in
/-- The tape during the rightward pass of the sweep of index `i`, with the head
at `p`: a real cell strictly below the head already holds the new value. -/
noncomputable def sweepTape (νs : Fin k → A → Prop) (i : ℕ) (p q : AltV k A) : AltV k A :=
  match q.1.1 with
  | .pStart => symStart
  | .pEnd => symEnd
  | .pCell =>
      if IsCellTup q then
        (if tagTupleLe q p ∧ q ≠ p then symV (valAfter νs (i + 1) (q.2 0)) (q.2 0)
          else symV (valAfter νs i (q.2 0)) (q.2 0))
      else symV false (q.2 0)
  | _ => symBlank

/-- At the left marker nothing has been written yet. -/
theorem sweepTape_posStart (νs : Fin k → A → Prop) (i : ℕ) :
    sweepTape νs i (posStart : AltV k A) = tapeAfter νs i := by
  classical
  funext q
  obtain ⟨⟨t, j⟩, w⟩ := q
  cases t <;> simp only [sweepTape, tapeAfter]
  refine if_congr Iff.rfl ?_ rfl
  refine if_neg ?_
  rintro ⟨hle, -⟩
  have h := altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hle)
  exact absurd h (show ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart) by decide)

/-- At the right marker the sweep is over. -/
theorem sweepTape_posEnd (νs : Fin k → A → Prop) (i : ℕ) :
    sweepTape νs i (posEnd : AltV k A) = tapeAfter νs (i + 1) := by
  classical
  funext q
  obtain ⟨⟨t, j⟩, w⟩ := q
  cases t <;> simp only [sweepTape, tapeAfter]
  refine if_congr Iff.rfl ?_ rfl
  refine if_pos ⟨altTagTupleLe_of_tag_lt (altTag_lt_of_base_lt (by decide) j 0), ?_⟩
  intro hcon
  exact absurd (congrArg (fun p => p.1.1) hcon) (show ¬(AltBase.pCell = AltBase.pEnd) by decide)

/-- **The rightward pass only ever changes the cell under the head.** Every
other element reads the same before and after: markers and non-cells do not
depend on the head at all, junk cells are frozen, and a real cell is below the
new head exactly when it was below the old one. -/
theorem sweepTape_frame (νs : Fin k → A → Prop) (i : ℕ) {p q r : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hr : r ≠ p) :
    sweepTape νs i q r = sweepTape νs i p r := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := r
  cases t <;> simp only [sweepTape]
  by_cases hcell : IsCellTup (((AltBase.pCell, j), w) : AltV k A)
  · rw [if_pos hcell, if_pos hcell]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hr⟩
      by_contra hcon
      rcases isLinOrd_altTagTupleLe.2.2.2 p (((AltBase.pCell, j), w) : AltV k A) with h | h
      · rcases hsucc.2.2.2.2 (((AltBase.pCell, j), w) : AltV k A) hcell h hle with h' | h'
        · exact hr h'
        · exact hne h'
      · exact hcon h
    · rintro ⟨hle, -⟩
      refine ⟨isLinOrd_altTagTupleLe.2.1 _ p q hle hsucc.2.2.1, ?_⟩
      rintro rfl
      exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
  · rw [if_neg hcell, if_neg hcell]

/-! ### The rightward pass -/

variable (νs)

/-- The configuration during the rightward pass of the sweep of index `i`. -/
noncomputable def confSweep (i : Fin (k + 1)) (p : AltV k A) : Config (AltV k A) where
  state := stG i true
  head := p
  tape := sweepTape νs (i : ℕ) p

/-- At the first cell nothing has been written yet either: no cell is strictly
below the cell of the least element. -/
theorem sweepTape_posCell_bot (i : ℕ) :
    sweepTape νs i (posCell (qbotA (A := A)) : AltV k A) = tapeAfter νs i := by
  classical
  funext q
  obtain ⟨⟨t, j⟩, w⟩ := q
  cases t <;> simp only [sweepTape, tapeAfter]
  by_cases hcell : IsCellTup (((AltBase.pCell, j), w) : AltV k A)
  · rw [if_pos hcell, if_pos hcell]
    refine if_neg ?_
    rintro ⟨hle, hne⟩
    refine hne ?_
    have hq : (((AltBase.pCell, j), w) : AltV k A) = posCell (w 0) :=
      eq_posCell_of_posn (show AltPosn (((AltBase.pCell, j), w) : AltV k A) from hcell) rfl
    have hx : w 0 ≤ qbotA := posCell_le_iff.mp (hq ▸ hle)
    rw [hq, le_antisymm hx (qbotA_le _)]
  · rw [if_neg hcell, if_neg hcell]

/-- **A sweep starts from the tape the sweeps below it left.** -/
theorem tape_confSweep_bot (i : Fin (k + 1)) :
    (confSweep νs i (posCell qbotA)).tape = tapeAfter νs (i : ℕ) :=
  sweepTape_posCell_bot νs _

/-- **The run starts at the first sweep.** -/
theorem isInit_confSweep (cnf : Bool) :
    (altMachine k A cnf).IsInit (confSweep νs 0 posStart) := by
  classical
  refine ⟨⟨rfl, isMinTup2_qbot⟩, minPos_posStart, fun q => ?_⟩
  change TMData.InitTape (altMachine k A cnf).toTMData q (sweepTape νs 0 posStart q)
  rw [sweepTape_posStart]
  obtain ⟨⟨t, j⟩, w⟩ := q
  cases t <;> simp only [tapeAfter] <;>
    first
      | exact Or.inl (Or.inl ⟨rfl, rfl, isMinTup2_qbot⟩)
      | exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, isMinTup2_qbot⟩))
      | (refine Or.inr ⟨fun b hb => ?_, rfl, isMinTup2_qbot⟩
         rcases hb with ⟨h, -⟩ | ⟨h, -, -, -⟩ | ⟨h, -⟩ <;> simp at h)
      | (by_cases hcell : IsCellTup (((AltBase.pCell, j), w) : AltV k A)
         · rw [if_pos hcell, valAfter_zero]
           exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl, fun b => qbotA_le b⟩))
         · rw [if_neg hcell]
           exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl, fun b => qbotA_le b⟩)))

variable {νs}

/-- The value under the head is the old one. -/
theorem sweepTape_at_head {i : ℕ} {p : AltV k A} (hp : AltPosn p) (hb : p.1.1 = AltBase.pCell) :
    sweepTape νs i p p = symV (valAfter νs i (p.2 0)) (p.2 0) := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := p
  simp only at hb
  subst hb
  simp only [sweepTape]
  rw [if_pos (show IsCellTup (((AltBase.pCell, j), w) : AltV k A) from hp),
    if_neg (fun hc => hc.2 rfl)]

/-- The value written under the head is the new one. -/
theorem sweepTape_written {i : ℕ} {p q : AltV k A} (hp : AltPosn p) (hb : p.1.1 = AltBase.pCell)
    (hsucc : SuccPos tagTupleLe AltPosn p q) :
    sweepTape νs i q p = symV (valAfter νs (i + 1) (p.2 0)) (p.2 0) := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := p
  simp only at hb
  subst hb
  simp only [sweepTape]
  rw [if_pos (show IsCellTup (((AltBase.pCell, j), w) : AltV k A) from hp),
    if_pos ⟨hsucc.2.2.1, hsucc.2.2.2.1⟩]

/-- **One step of a rightward pass.** At a cell the machine writes the value
its block gives the variable – keeping the old one, or setting it – and moves
on; at the left marker it steps over it. -/
theorem step_sweep {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) < k) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hb : tagTupleLe q posEnd)
    (hstart : p.1.1 = AltBase.pStart → (i : ℕ) = 0) :
    (altMachine k A cnf).Step (confSweep νs i p) (confSweep νs i q) := by
  classical
  have hframe : ∀ r, r ≠ p → sweepTape νs (i : ℕ) q r = sweepTape νs (i : ℕ) p r :=
    fun r hr => sweepTape_frame νs (i : ℕ) hsucc hr
  have hpe : altBaseIdx p.1.1 ≤ altBaseIdx AltBase.pEnd :=
    altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le
      (isLinOrd_altTagTupleLe.2.1 p q posEnd hsucc.2.2.1 hb))
  have hcases : p.1.1 = AltBase.pStart ∨ p.1.1 = AltBase.pCell ∨ p.1.1 = AltBase.pEnd := by
    revert hpe
    generalize p.1.1 = t
    revert t
    decide
  rcases hcases with h | h | h
  · -- the left marker, and then only at the first sweep
    have hi0 : (i : ℕ) = 0 := hstart h
    refine ⟨acstI .tGStart i, ⟨isMinTup2_qbot, hi0, by omega⟩, rfl, ?_, rfl, ?_, hframe,
      Or.inl ⟨trivial, hsucc⟩⟩
    · change sweepTape νs (i : ℕ) p p = symStart
      obtain ⟨⟨t, j⟩, w⟩ := p
      simp only at h
      subst h
      rfl
    · change sweepTape νs (i : ℕ) q p = symStart
      obtain ⟨⟨t, j⟩, w⟩ := p
      simp only at h
      subst h
      rfl
  · -- a cell: keep the value, or set it
    have hread := sweepTape_at_head (νs := νs) (i := (i : ℕ)) hsucc.1 h
    have hwrite := sweepTape_written (νs := νs) (i := (i : ℕ)) hsucc.1 h hsucc
    have hpos : ∀ a : A, p.2 1 ≤ a := by
      have := hsucc.1
      rw [AltPosn, h] at this
      exact this.2
    by_cases hset : ∃ j : Fin k, (j : ℕ) = (i : ℕ) ∧ QbfBlk j (p.2 0) ∧ νs j (p.2 0)
    · by_cases hold : valAfter νs (i : ℕ) (p.2 0) = true
      · -- already true: keep it
        refine ⟨aoneI (.tGKeep true) i (p.2 0), ⟨fun a => qbotA_le a, hi⟩, rfl, ?_, rfl, ?_,
          hframe, Or.inl ⟨trivial, hsucc⟩⟩
        · change sweepTape νs (i : ℕ) p p = symV true (p.2 0)
          rw [hread, hold]
        · change sweepTape νs (i : ℕ) q p = symV true (p.2 0)
          rw [hwrite, valAfter_succ_of_set hset]
      · -- still false: set it
        refine ⟨aoneI .tGSet i (p.2 0), ⟨fun a => qbotA_le a, ?_⟩, rfl, ?_, rfl, ?_,
          hframe, Or.inl ⟨trivial, hsucc⟩⟩
        · obtain ⟨j, hj, hbk, hν⟩ := hset
          exact ⟨j, hj, hbk⟩
        · change sweepTape νs (i : ℕ) p p = symV false (p.2 0)
          have hold' : valAfter νs (i : ℕ) (p.2 0) = false := by
            rcases Bool.eq_false_or_eq_true (valAfter νs (i : ℕ) (p.2 0)) with h' | h'
            · exact absurd h' hold
            · exact h'
          rw [hread, hold']
        · change sweepTape νs (i : ℕ) q p = symV true (p.2 0)
          rw [hwrite, valAfter_succ_of_set hset]
    · -- the block does not set it: keep whatever it holds
      refine ⟨aoneI (.tGKeep (valAfter νs (i : ℕ) (p.2 0))) i (p.2 0),
        ⟨fun a => qbotA_le a, hi⟩, rfl, ?_, rfl, ?_, hframe, Or.inl ⟨trivial, hsucc⟩⟩
      · change sweepTape νs (i : ℕ) p p = symV (valAfter νs (i : ℕ) (p.2 0)) (p.2 0)
        exact hread
      · change sweepTape νs (i : ℕ) q p = symV (valAfter νs (i : ℕ) (p.2 0)) (p.2 0)
        rw [hwrite, valAfter_succ_of_keep hset]
  · exact absurd (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1
      ((eq_posEnd_of_posn hsucc.1 h) ▸ hb)) hsucc.2.2.2.1

/-- **The whole rightward pass**: from the first cell to the right marker, the
sweep of index `i` writes its block's value in every cell. -/
theorem steps_sweepR {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) < k) :
    (altMachine k A cnf).StepsIn
      (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
        bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A))
      (confSweep νs i (posCell qbotA)) (confSweep νs i posEnd) := by
  refine TMData.stepsIn_of_segment isLinOrd_altTagTupleLe (altPosn_posCell _)
    (fun p q hsucc hlb hb => step_sweep hi hsucc hb fun hst => ?_) posEnd altPosn_posEnd
    (posCell_le_posEnd _) (altTagTupleLe_refl _)
  exfalso
  have h := altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlb)
  simp only [hst] at h
  exact absurd h (show ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart) by decide)

/-- **The first sweep steps over the left marker.** Later sweeps do not: they
enter at the first cell, the handover at `⊢` having already moved the head. -/
theorem step_sweepStart {cnf : Bool} (hk : 0 < k) :
    (altMachine k A cnf).Step (confSweep νs 0 posStart) (confSweep νs 0 (posCell qbotA)) :=
  step_sweep (by simpa using hk) succPos_posStart_posCell (posCell_le_posEnd _) fun _ => rfl

/-! ### The turn, the leftward pass and the handover -/

variable (νs)

/-- The configuration during the leftward pass of the sweep of index `i`: the
tape is the one the sweep has just finished writing, and does not change
again. -/
noncomputable def confBack (i : Fin (k + 1)) (p : AltV k A) : Config (AltV k A) where
  state := stG i false
  head := p
  tape := tapeAfter νs ((i : ℕ) + 1)

variable {νs}

/-- The tape reads a real cell as the value its variable has accumulated. -/
theorem tapeAfter_at_cell {m : ℕ} {p : AltV k A} (hp : AltPosn p) (hb : p.1.1 = AltBase.pCell) :
    tapeAfter νs m p = symV (valAfter νs m (p.2 0)) (p.2 0) := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := p
  simp only at hb
  subst hb
  simp only [tapeAfter]
  rw [if_pos (show IsCellTup (((AltBase.pCell, j), w) : AltV k A) from hp)]

theorem tapeAfter_posCell (i : ℕ) (x : A) :
    tapeAfter νs i (posCell x : AltV k A) = symV (valAfter νs i x) x :=
  tapeAfter_at_cell (altPosn_posCell x) rfl

/-- **The turn at the right marker**: the sweep has written every cell and
turns round. -/
theorem step_turnBack {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) < k) :
    (altMachine k A cnf).Step (confSweep νs i posEnd) (confBack νs i (posCell qtopA)) := by
  refine ⟨acstI .tGTurn i, ⟨isMinTup2_qbot, hi⟩, rfl, ?_, rfl, ?_, ?_,
    Or.inr ⟨id, succPos_posCell_posEnd⟩⟩
  · change sweepTape νs (i : ℕ) posEnd posEnd = symEnd
    rw [sweepTape_posEnd]
    rfl
  · change tapeAfter νs ((i : ℕ) + 1) posEnd = symEnd
    rfl
  · intro r _
    change tapeAfter νs ((i : ℕ) + 1) r = sweepTape νs (i : ℕ) posEnd r
    rw [sweepTape_posEnd]

/-- **One step of the leftward pass**: the head steps back over a cell,
changing nothing. -/
theorem step_back {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) < k) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hlb : tagTupleLe posStart p)
    (hub : tagTupleLe q (posCell qtopA)) :
    (altMachine k A cnf).Step (confBack νs i q) (confBack νs i p) := by
  classical
  -- the position `q` is a real cell: it is above the left marker and at most the last one
  have hq : q.1.1 = AltBase.pCell := by
    have h1 : altBaseIdx AltBase.pStart ≤ altBaseIdx q.1.1 :=
      altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le
        (isLinOrd_altTagTupleLe.2.1 posStart p q hlb hsucc.2.2.1))
    have h2 : altBaseIdx q.1.1 ≤ altBaseIdx AltBase.pCell :=
      altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hub)
    rcases base_le_pCell h2 with h | h
    · exfalso
      have hqs : q = posStart := eq_posStart_of_posn hsucc.2.1 h
      exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1 (hqs ▸ hlb))
    · exact h
  have hcell : q = posCell (q.2 0) := eq_posCell_of_posn hsucc.2.1 hq
  refine ⟨aoneI (.tGBack (valAfter νs ((i : ℕ) + 1) (q.2 0))) i (q.2 0),
    ⟨fun a => qbotA_le a, hi⟩, rfl, ?_, rfl, ?_, fun r _ => rfl, Or.inr ⟨id, hsucc⟩⟩
  · exact tapeAfter_at_cell hsucc.2.1 hq
  · exact tapeAfter_at_cell hsucc.2.1 hq

/-- **The whole leftward pass**: from the last cell back to the left marker. -/
theorem steps_back {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) < k) :
    (altMachine k A cnf).StepsIn
      (bitRank tagTupleLe AltPosn (posCell qtopA : AltV k A) -
        bitRank tagTupleLe AltPosn (posStart : AltV k A))
      (confBack νs i (posCell qtopA)) (confBack νs i posStart) :=
  TMData.stepsIn_of_segment_down isLinOrd_altTagTupleLe (altPosn_posCell _)
    (fun _ _ hsucc hlb hub => step_back hi hsucc hlb hub) posStart altPosn_posStart
    (altTagTupleLe_refl _) (posStart_le_posCell _)

/-- **The handover to the next sweep**: at the left marker the machine steps
right into the first cell and the next block takes over. -/
theorem step_next {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) + 1 < k) :
    (altMachine k A cnf).Step (confBack νs i posStart) (confSweep νs (i + 1) (posCell qbotA)) := by
  have hval : ((i + 1 : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 := by
    refine Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr fun hcon => ?_)
    rw [hcon] at hi
    simp only [Fin.val_last] at hi
    omega
  refine ⟨acstI .tGNext i, ⟨isMinTup2_qbot, hi⟩, rfl, rfl, rfl, ?_, ?_,
    Or.inl ⟨trivial, succPos_posStart_posCell⟩⟩
  · change sweepTape νs ((i + 1 : Fin (k + 1)) : ℕ) (posCell qbotA) posStart = symStart
    rw [sweepTape_posCell_bot]
    rfl
  · intro r _
    change sweepTape νs ((i + 1 : Fin (k + 1)) : ℕ) (posCell qbotA) r =
      tapeAfter νs ((i : ℕ) + 1) r
    rw [sweepTape_posCell_bot, hval]

/-- **The handover to the check phase**: after the last sweep the machine takes
the lowest clause with an empty flag and sweeps rightwards. -/
theorem step_toChk {cnf : Bool} {i : Fin (k + 1)} (hlast : (i : ℕ) + 1 = k) {c₀ : A}
    (hc₀ : QbfMinCl k c₀) :
    (altMachine k A cnf).Step (confBack νs i posStart)
      { state := stChk false true c₀, head := posCell qbotA, tape := tapeAfter νs k } := by
  refine ⟨aoneI .tGEndChk i c₀, ⟨fun a => qbotA_le a, hlast, hc₀⟩, rfl, rfl, rfl, ?_, ?_,
    Or.inl ⟨trivial, succPos_posStart_posCell⟩⟩
  · change tapeAfter νs k posStart = symStart
    rfl
  · intro r _
    change tapeAfter νs k r = tapeAfter νs ((i : ℕ) + 1) r
    rw [hlast]

/-- **The handover to acceptance**: an instance with no clause at all is
vacuously satisfied by a conjunctive matrix, and the machine accepts. -/
theorem step_toAcc {cnf : Bool} {i : Fin (k + 1)} (hlast : (i : ℕ) + 1 = k) (hcnf : cnf = true)
    (hno : ∀ e : A, ¬QbfCl k e) :
    (altMachine k A cnf).Step (confBack νs i posStart)
      { state := stAcc, head := posCell qbotA, tape := tapeAfter νs k } := by
  refine ⟨acstI .tGEndAcc i, ⟨isMinTup2_qbot, hlast, hcnf, hno⟩, rfl, rfl, rfl, ?_, ?_,
    Or.inl ⟨trivial, succPos_posStart_posCell⟩⟩
  · change tapeAfter νs k posStart = symStart
    rfl
  · intro r _
    change tapeAfter νs k r = tapeAfter νs ((i : ℕ) + 1) r
    rw [hlast]

/-! ### One sweep, end to end -/

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- Two runs compose. (`DescriptiveComplexity.TMData.stepsIn_split` is the
converse; this direction is not in `DescriptiveComplexity.Machines` and could
be hoisted there.) -/
theorem stepsIn_add {M : TMData (AltV k A)} :
    ∀ {m n : ℕ} {c d e : Config (AltV k A)}, M.StepsIn m c d → M.StepsIn n d e →
      M.StepsIn (m + n) c e := by
  intro m
  induction m with
  | zero =>
    intro n c d e h1 h2
    rw [Nat.zero_add]
    exact (show c = d from h1) ▸ h2
  | succ m ih =>
    intro n c d e h1 h2
    obtain ⟨c', hstep, hrest⟩ := h1
    rw [Nat.succ_add]
    exact ⟨c', hstep, ih hrest h2⟩

/-- The number of steps a sweep takes: right to the marker, turn, back to the
other marker, and over it. -/
noncomputable def sweepLen (k : ℕ) (A : Type) [LinearOrder A] [Finite A] [Nonempty A] : ℕ :=
  (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
      bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) + 1 +
    (bitRank tagTupleLe AltPosn (posCell qtopA : AltV k A) -
      bitRank tagTupleLe AltPosn (posStart : AltV k A)) + 1

/-- **The whole of sweep `i`**, from the first cell to the first cell of the
sweep that follows it: the round of block `i` is exactly this run. -/
theorem steps_sweep {cnf : Bool} {i : Fin (k + 1)} (hi : (i : ℕ) + 1 < k) :
    (altMachine k A cnf).StepsIn (sweepLen k A)
      (confSweep νs i (posCell qbotA)) (confSweep νs (i + 1) (posCell qbotA)) := by
  have h1 := steps_sweepR (νs := νs) (cnf := cnf) (i := i) (by omega)
  have h2 := step_turnBack (νs := νs) (cnf := cnf) (i := i) (by omega)
  have h3 := steps_back (νs := νs) (cnf := cnf) (i := i) (by omega)
  have h4 := step_next (νs := νs) (cnf := cnf) (i := i) hi
  exact stepsIn_add (stepsIn_add (stepsIn_add h1 ⟨_, h2, rfl⟩) h3) ⟨_, h4, rfl⟩

end Sweep

end AltQbf

end DescriptiveComplexity
