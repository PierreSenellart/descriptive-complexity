/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltSweep

/-!
# The intended run: the check phase

Once the `k` sweeps have written `DescriptiveComplexity.qbfVal` in every cell,
the machine walks the clauses one by one, sweeping the tape and accumulating a
flag. The tape never changes again, so the frame condition of every step here
is `rfl`.

**The flag means two different things, and that is the whole of the disjunctive
case.** For a conjunctive matrix it records that some literal of the clause is
*satisfied*; for a disjunctive one, that some literal of the term is
*violated*. The two are the same test at the flipped truth value
(`DescriptiveComplexity.xorB`), so one transition family serves both, and the
accepting turn fires at the flag `cnf`: set for a conjunctive matrix, where it
means the clause is satisfied, clear for a disjunctive one, where it means no
literal of the term is violated.

A sweep alternates direction with each clause, as in
`DescriptiveComplexity.Problems.Machine.Hardness`: the first runs rightwards
from the first cell, having been entered by
`DescriptiveComplexity.step_toChk`.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Check

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### What the check tests -/

variable (k) in
/-- **The literal test of the check phase**: for a conjunctive matrix, that the
cell of `x` holding `v` satisfies the clause `c`; for a disjunctive one, that
it violates it. -/
def QGood (cnf : Bool) (c x : A) (v : Bool) : Prop := QbfLit k c x (xorB cnf v)

variable {νs : Fin k → A → Prop}

/-- The value the tape holds in the cell of `x` once every sweep has run. -/
noncomputable def chkVal (νs : Fin k → A → Prop) (x : A) : Bool := valAfter νs k x

/-- The tape of the check phase reads a real cell as the truth value of its
variable. -/
theorem tapeAfter_top_at_cell {p : AltV k A} (hp : AltPosn p) (hb : p.1.1 = AltBase.pCell) :
    tapeAfter νs k p = symV (chkVal νs (p.2 0)) (p.2 0) :=
  tapeAfter_at_cell hp hb

/-! ### A rightward check sweep -/

open Classical in
/-- The flag of a rightward check sweep with the head at `p`: some cell already
visited – that is, strictly below `p` – is good for the clause `c`. -/
noncomputable def chkFlagR (cnf : Bool) (νs : Fin k → A → Prop) (c : A) (p : AltV k A) : Bool :=
  decide (∃ y : A, tagTupleLe (posCell y : AltV k A) p ∧ (posCell y : AltV k A) ≠ p ∧
    QGood k cnf c y (chkVal νs y))

/-- The configuration during a rightward check sweep of the clause `c`. -/
noncomputable def confChkR (cnf : Bool) (νs : Fin k → A → Prop) (c : A) (p : AltV k A) :
    Config (AltV k A) where
  state := stChk (chkFlagR cnf νs c p) true c
  head := p
  tape := tapeAfter νs k

/-- **A rightward sweep starts with an empty flag**: nothing lies below the
lowest cell. -/
theorem chkFlagR_bot (cnf : Bool) (c : A) :
    chkFlagR cnf νs c (posCell (qbotA (A := A))) = false := by
  classical
  simp only [chkFlagR, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (posCell_le_iff.mp hle) (qbotA_le y)))

/-- **Stepping up adds exactly one literal to the flag.** Moving the head from
`p` to the position above it brings `p`'s own cell into view and nothing else,
because `DescriptiveComplexity.SuccPos` leaves no room between them. -/
theorem chkFlagR_succ (cnf : Bool) (c : A) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hp : p.1.1 = AltBase.pCell) :
    chkFlagR cnf νs c q = true ↔
      (chkFlagR cnf νs c p = true ∨ QGood k cnf c (p.2 0) (chkVal νs (p.2 0))) := by
  classical
  have hpc : p = posCell (p.2 0) := eq_posCell_of_posn hsucc.1 hp
  simp only [chkFlagR, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe (posCell y : AltV k A) p ∧ (posCell y : AltV k A) ≠ p
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyp : (posCell y : AltV k A) = p := by
        by_cases hle' : tagTupleLe (posCell y : AltV k A) p
        · exact not_not.mp (by simpa [hle'] using hcase)
        · rcases hsucc.2.2.2.2 (posCell y) (altPosn_posCell y)
            ((isLinOrd_altTagTupleLe.2.2.2 p (posCell y)).resolve_right hle') hle with h | h
          · exact h
          · exact absurd h hne
      have hy : y = p.2 0 := by
        have := congrArg (fun z : AltV k A => z.2 0) (hyp.trans hpc)
        simpa [aoneI] using this
      rwa [← hy]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_altTagTupleLe.2.1 _ p q hle hsucc.2.2.1, ?_, hlit⟩
      rintro rfl
      exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
    · exact ⟨p.2 0, hpc ▸ hsucc.2.2.1, hpc ▸ hsucc.2.2.2.1, hlit⟩

/-- **One step of a rightward check sweep.** The machine reads the cell it is
on, folds that literal into the flag, and moves one place right. -/
theorem step_chkR {cnf : Bool} {c : A} (hc : QbfCl k c) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hp : p.1.1 = AltBase.pCell) :
    (altMachine k A cnf).Step (confChkR cnf νs c p) (confChkR cnf νs c q) := by
  classical
  have hread : tapeAfter νs k p = symV (chkVal νs (p.2 0)) (p.2 0) :=
    tapeAfter_top_at_cell hsucc.1 hp
  refine ⟨((AltBase.tChk (chkVal νs (p.2 0)) (chkFlagR cnf νs c p) true, 0), ![c, p.2 0]),
    ⟨hc, rfl⟩, rfl, hread, ?_, hread, fun r _ => rfl, Or.inl ⟨rfl, hsucc⟩⟩
  by_cases hflag : chkFlagR cnf νs c q = true
  · refine Or.inl ⟨?_, ?_⟩
    · change stChk (chkFlagR cnf νs c q) true c = stChk true true c
      rw [hflag]
    · exact (chkFlagR_succ cnf c hsucc hp).mp hflag
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stChk (chkFlagR cnf νs c q) true c = stChk false true c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((chkFlagR_succ cnf c hsucc hp).mpr (Or.inl (by simpa using hcon)))
    · intro hlit
      exact hflag ((chkFlagR_succ cnf c hsucc hp).mpr (Or.inr hlit))

/-- **A whole rightward check sweep**: from the lowest cell to the right
marker, the flag accumulating the literals of `c` met along the way. -/
theorem steps_chkR {cnf : Bool} {c : A} (hc : QbfCl k c) :
    (altMachine k A cnf).StepsIn
      (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
        bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A))
      (confChkR cnf νs c (posCell qbotA)) (confChkR cnf νs c posEnd) := by
  refine TMData.stepsIn_of_segment isLinOrd_altTagTupleLe (altPosn_posCell _)
    (fun p q hsucc hlb hub => step_chkR hc hsucc ?_) posEnd altPosn_posEnd
    (posCell_le_posEnd _) (altTagTupleLe_refl _)
  -- every position strictly below the right marker and at or above the first cell is a cell
  have h1 : altBaseIdx AltBase.pCell ≤ altBaseIdx p.1.1 :=
    altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlb)
  have h2 : altBaseIdx p.1.1 ≤ altBaseIdx AltBase.pEnd :=
    altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le
      (isLinOrd_altTagTupleLe.2.1 p q posEnd hsucc.2.2.1 hub))
  rcases base_between h1 h2 with h | h
  · exact h
  · exfalso
    have hpe : p = posEnd := eq_posEnd_of_posn hsucc.1 h
    exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1 (hpe ▸ hub))

/-! ### A leftward check sweep -/

open Classical in
/-- The flag of a leftward check sweep with the head at `p`: some cell already
visited – that is, strictly above `p` – is good for the clause `c`. -/
noncomputable def chkFlagL (cnf : Bool) (νs : Fin k → A → Prop) (c : A) (p : AltV k A) : Bool :=
  decide (∃ y : A, tagTupleLe p (posCell y : AltV k A) ∧ p ≠ (posCell y : AltV k A) ∧
    QGood k cnf c y (chkVal νs y))

/-- The configuration during a leftward check sweep of the clause `c`. -/
noncomputable def confChkL (cnf : Bool) (νs : Fin k → A → Prop) (c : A) (p : AltV k A) :
    Config (AltV k A) where
  state := stChk (chkFlagL cnf νs c p) false c
  head := p
  tape := tapeAfter νs k

/-- **A leftward sweep starts with an empty flag**: nothing lies above the
highest cell. -/
theorem chkFlagL_top (cnf : Bool) (c : A) :
    chkFlagL cnf νs c (posCell (qtopA (A := A))) = false := by
  classical
  simp only [chkFlagL, decide_eq_false_iff_not]
  rintro ⟨y, hle, hne, -⟩
  exact hne (congrArg _ (le_antisymm (le_qtopA y) (posCell_le_iff.mp hle))).symm

/-- **Stepping down adds exactly one literal to the flag.** -/
theorem chkFlagL_succ (cnf : Bool) (c : A) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hq : q.1.1 = AltBase.pCell) :
    chkFlagL cnf νs c p = true ↔
      (chkFlagL cnf νs c q = true ∨ QGood k cnf c (q.2 0) (chkVal νs (q.2 0))) := by
  classical
  have hqc : q = posCell (q.2 0) := eq_posCell_of_posn hsucc.2.1 hq
  simp only [chkFlagL, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hle, hne, hlit⟩
    by_cases hcase : tagTupleLe q (posCell y : AltV k A) ∧ q ≠ (posCell y : AltV k A)
    · exact Or.inl ⟨y, hcase.1, hcase.2, hlit⟩
    · refine Or.inr ?_
      have hyq : (posCell y : AltV k A) = q := by
        by_cases hle' : tagTupleLe q (posCell y : AltV k A)
        · have h : q = (posCell y : AltV k A) := not_not.mp (by simpa [hle'] using hcase)
          exact h.symm
        · rcases hsucc.2.2.2.2 (posCell y) (altPosn_posCell y) hle
            ((isLinOrd_altTagTupleLe.2.2.2 (posCell y) q).resolve_right hle') with h | h
          · exact absurd h.symm hne
          · exact h
      have hy : y = q.2 0 := by
        have := congrArg (fun z : AltV k A => z.2 0) (hyq.trans hqc)
        simpa [aoneI] using this
      rwa [← hy]
  · rintro (⟨y, hle, hne, hlit⟩ | hlit)
    · refine ⟨y, isLinOrd_altTagTupleLe.2.1 p q _ hsucc.2.2.1 hle, ?_, hlit⟩
      rintro rfl
      exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 _ _ hsucc.2.2.1 hle)
    · exact ⟨q.2 0, hqc ▸ hsucc.2.2.1, hqc ▸ hsucc.2.2.2.1, hlit⟩

/-- **One step of a leftward check sweep.** -/
theorem step_chkL {cnf : Bool} {c : A} (hc : QbfCl k c) {p q : AltV k A}
    (hsucc : SuccPos tagTupleLe AltPosn p q) (hq : q.1.1 = AltBase.pCell) :
    (altMachine k A cnf).Step (confChkL cnf νs c q) (confChkL cnf νs c p) := by
  classical
  have hread : tapeAfter νs k q = symV (chkVal νs (q.2 0)) (q.2 0) :=
    tapeAfter_top_at_cell hsucc.2.1 hq
  refine ⟨((AltBase.tChk (chkVal νs (q.2 0)) (chkFlagL cnf νs c q) false, 0), ![c, q.2 0]),
    ⟨hc, rfl⟩, rfl, hread, ?_, hread, fun r _ => rfl, Or.inr ⟨Bool.false_ne_true, hsucc⟩⟩
  by_cases hflag : chkFlagL cnf νs c p = true
  · refine Or.inl ⟨?_, ?_⟩
    · change stChk (chkFlagL cnf νs c p) false c = stChk true false c
      rw [hflag]
    · exact (chkFlagL_succ cnf c hsucc hq).mp hflag
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · change stChk (chkFlagL cnf νs c p) false c = stChk false false c
      rw [Bool.not_eq_true] at hflag
      rw [hflag]
    · by_contra hcon
      exact hflag ((chkFlagL_succ cnf c hsucc hq).mpr (Or.inl (by simpa using hcon)))
    · intro hlit
      exact hflag ((chkFlagL_succ cnf c hsucc hq).mpr (Or.inr hlit))

/-- **A whole leftward check sweep**: from the highest cell down to the left
marker. -/
theorem steps_chkL {cnf : Bool} {c : A} (hc : QbfCl k c) :
    (altMachine k A cnf).StepsIn
      (bitRank tagTupleLe AltPosn (posCell qtopA : AltV k A) -
        bitRank tagTupleLe AltPosn (posStart : AltV k A))
      (confChkL cnf νs c (posCell qtopA)) (confChkL cnf νs c posStart) := by
  refine TMData.stepsIn_of_segment_down isLinOrd_altTagTupleLe (altPosn_posCell _)
    (fun p q hsucc _ hub => step_chkL hc hsucc ?_) posStart altPosn_posStart
    (altTagTupleLe_refl _) (posStart_le_posCell _)
  rcases base_le_pCell (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hub)) with h | h
  · exfalso
    refine hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 p q hsucc.2.2.1 ?_)
    rw [eq_posStart_of_posn hsucc.2.1 h]
    exact minPos_posStart.2 p hsucc.1
  · exact h

/-! ### The turns -/

/-- **The turn at the right marker**, when another clause follows. -/
theorem step_turnNextR {cnf : Bool} {c c' : A} (hnext : QbfNextCl k c c')
    (hflag : chkFlagR cnf νs c posEnd = true) :
    (altMachine k A cnf).Step (confChkR cnf νs c posEnd) (confChkL cnf νs c' (posCell qtopA)) := by
  refine ⟨((AltBase.tTurnNext true, 0), ![c, c']), ⟨hnext, rfl⟩, ?_, rfl, ?_, rfl,
    fun r _ => rfl, Or.inr ⟨fun h => Bool.noConfusion h, succPos_posCell_posEnd⟩⟩
  · change stChk (chkFlagR cnf νs c posEnd) true c = stChk true true c
    rw [hflag]
  · change stChk (chkFlagL cnf νs c' (posCell qtopA)) false c' = stChk false (!true) c'
    rw [chkFlagL_top]
    rfl

/-- **The turn at the right marker**, when the clause settles the run. -/
theorem step_turnAccR {cnf : Bool} {c : A} (hc : QbfCl k c) (hmax : cnf = true → QbfMaxCl k c)
    (hflag : chkFlagR cnf νs c posEnd = cnf) :
    (altMachine k A cnf).Step (confChkR cnf νs c posEnd)
      { state := stAcc, head := posCell qtopA, tape := tapeAfter νs k } := by
  refine ⟨((AltBase.tTurnAcc true, 0), ![c, qbotA]),
    ⟨fun a => qbotA_le a, rfl, hc, hmax⟩, ?_, rfl, rfl, rfl,
    fun r _ => rfl, Or.inr ⟨fun h => Bool.noConfusion h, succPos_posCell_posEnd⟩⟩
  change stChk (chkFlagR cnf νs c posEnd) true c = stChk cnf true c
  rw [hflag]

/-- **The turn at the left marker**, when another clause follows. -/
theorem step_turnNextL {cnf : Bool} {c c' : A} (hnext : QbfNextCl k c c')
    (hflag : chkFlagL cnf νs c posStart = true) :
    (altMachine k A cnf).Step (confChkL cnf νs c posStart)
      (confChkR cnf νs c' (posCell qbotA)) := by
  refine ⟨((AltBase.tTurnNext false, 0), ![c, c']), ⟨hnext, rfl⟩, ?_, rfl, ?_, rfl,
    fun r _ => rfl, Or.inl ⟨rfl, succPos_posStart_posCell⟩⟩
  · change stChk (chkFlagL cnf νs c posStart) false c = stChk true false c
    rw [hflag]
  · change stChk (chkFlagR cnf νs c' (posCell qbotA)) true c' = stChk false (!false) c'
    rw [chkFlagR_bot]
    rfl

/-- **The turn at the left marker**, when the clause settles the run. -/
theorem step_turnAccL {cnf : Bool} {c : A} (hc : QbfCl k c) (hmax : cnf = true → QbfMaxCl k c)
    (hflag : chkFlagL cnf νs c posStart = cnf) :
    (altMachine k A cnf).Step (confChkL cnf νs c posStart)
      { state := stAcc, head := posCell qbotA, tape := tapeAfter νs k } := by
  refine ⟨((AltBase.tTurnAcc false, 0), ![c, qbotA]),
    ⟨fun a => qbotA_le a, rfl, hc, hmax⟩, ?_, rfl, rfl, rfl,
    fun r _ => rfl, Or.inl ⟨rfl, succPos_posStart_posCell⟩⟩
  change stChk (chkFlagL cnf νs c posStart) false c = stChk cnf false c
  rw [hflag]

/-! ### One clause, checked end to end -/

/-- **At the far marker the flag has seen every cell.** -/
theorem chkFlagR_posEnd (cnf : Bool) (c : A) :
    chkFlagR cnf νs c (posEnd : AltV k A) = true ↔
      ∃ y : A, QGood k cnf c y (chkVal νs y) := by
  classical
  simp only [chkFlagR, decide_eq_true_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, -, -, hg⟩ := h
    exact ⟨y, hg⟩
  · obtain ⟨y, hg⟩ := h
    refine ⟨y, posCell_le_posEnd y, ?_, hg⟩
    intro hcon
    exact absurd (congrArg (fun p => p.1.1) hcon) (show ¬(AltBase.pCell = AltBase.pEnd) by decide)

/-- **At the far marker the flag has seen every cell.** -/
theorem chkFlagL_posStart (cnf : Bool) (c : A) :
    chkFlagL cnf νs c (posStart : AltV k A) = true ↔
      ∃ y : A, QGood k cnf c y (chkVal νs y) := by
  classical
  simp only [chkFlagL, decide_eq_true_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, -, -, hg⟩ := h
    exact ⟨y, hg⟩
  · obtain ⟨y, hg⟩ := h
    refine ⟨y, posStart_le_posCell y, ?_, hg⟩
    intro hcon
    exact absurd (congrArg (fun p => p.1.1) hcon) (show ¬(AltBase.pStart = AltBase.pCell) by decide)

omit [(Language.qbf k).Structure A] in
/-- The left marker has rank `0`. -/
theorem bitRank_posStart : bitRank tagTupleLe AltPosn (posStart : AltV k A) = 0 :=
  bitRank_eq_zero_of_minPos isLinOrd_altTagTupleLe minPos_posStart

omit [(Language.qbf k).Structure A] in
/-- The right marker sits one step above the last cell. -/
theorem bitRank_posEnd_eq :
    bitRank tagTupleLe AltPosn (posEnd : AltV k A) =
      bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) + 1 :=
  bitRank_succPos isLinOrd_altTagTupleLe succPos_posCell_posEnd

omit [(Language.qbf k).Structure A] in
/-- The first cell has rank `1`. -/
theorem bitRank_posCell_qbotA :
    bitRank tagTupleLe AltPosn (posCell (qbotA (A := A)) : AltV k A) = 1 := by
  rw [bitRank_succPos isLinOrd_altTagTupleLe succPos_posStart_posCell, bitRank_posStart]

/-- Checking `c` rightwards and moving on to the next clause. -/
theorem steps_clauseR {cnf : Bool} {c c' : A} (hc : QbfCl k c) (hnext : QbfNextCl k c c')
    (hgood : ∃ y : A, QGood k cnf c y (chkVal νs y)) :
    ∃ n ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A),
      (altMachine k A cnf).StepsIn n (confChkR cnf νs c (posCell qbotA))
        (confChkL cnf νs c' (posCell qtopA)) := by
  refine ⟨_, ?_,
    (steps_chkR hc).trans_step (step_turnNextR hnext ((chkFlagR_posEnd cnf c).mpr hgood))⟩
  have h1 := bitRank_posCell_qbotA (k := k) (A := A)
  have h2 := bitRank_posEnd_eq (k := k) (A := A)
  omega

/-- Checking `c` leftwards and moving on to the next clause. -/
theorem steps_clauseL {cnf : Bool} {c c' : A} (hc : QbfCl k c) (hnext : QbfNextCl k c c')
    (hgood : ∃ y : A, QGood k cnf c y (chkVal νs y)) :
    ∃ n ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A),
      (altMachine k A cnf).StepsIn n (confChkL cnf νs c (posCell qtopA))
        (confChkR cnf νs c' (posCell qbotA)) := by
  refine ⟨_, ?_,
    (steps_chkL hc).trans_step (step_turnNextL hnext ((chkFlagL_posStart cnf c).mpr hgood))⟩
  have h1 := bitRank_posStart (k := k) (A := A)
  have h2 := bitRank_posEnd_eq (k := k) (A := A)
  omega

/-- Checking `c` rightwards and accepting. -/
theorem steps_clauseAccR {cnf : Bool} {c : A} (hc : QbfCl k c) (hmax : cnf = true → QbfMaxCl k c)
    (hflag : chkFlagR cnf νs c (posEnd : AltV k A) = cnf) :
    ∃ n ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A), ∃ cfin : Config (AltV k A),
      (altMachine k A cnf).StepsIn n (confChkR cnf νs c (posCell qbotA)) cfin ∧
        AltAccSt cfin.state := by
  refine ⟨_, ?_, _, (steps_chkR hc).trans_step (step_turnAccR hc hmax hflag), rfl⟩
  have h1 := bitRank_posCell_qbotA (k := k) (A := A)
  have h2 := bitRank_posEnd_eq (k := k) (A := A)
  omega

/-- Checking `c` leftwards and accepting. -/
theorem steps_clauseAccL {cnf : Bool} {c : A} (hc : QbfCl k c) (hmax : cnf = true → QbfMaxCl k c)
    (hflag : chkFlagL cnf νs c (posStart : AltV k A) = cnf) :
    ∃ n ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A), ∃ cfin : Config (AltV k A),
      (altMachine k A cnf).StepsIn n (confChkL cnf νs c (posCell qtopA)) cfin ∧
        AltAccSt cfin.state := by
  refine ⟨_, ?_, _, (steps_chkL hc).trans_step (step_turnAccL hc hmax hflag), rfl⟩
  have h1 := bitRank_posStart (k := k) (A := A)
  have h2 := bitRank_posEnd_eq (k := k) (A := A)
  omega

/-! ### Walking the clauses -/

omit [Nonempty A] in
/-- **Every clause but the last has a next one.** -/
theorem exists_qNextCl {c : A} (hc : QbfCl k c) (hnmax : ¬QbfMaxCl k c) :
    ∃ c', QbfNextCl k c c' := by
  have hne : ∃ e : A, QbfCl k e ∧ c < e := by
    by_contra hcon
    push Not at hcon
    exact hnmax ⟨hc, hcon⟩
  obtain ⟨c', ⟨hc', hlt⟩, hmin⟩ :=
    exists_minPos (Le := (· ≤ ·)) (Posn := fun e : A => QbfCl k e ∧ c < e)
      ⟨le_refl, fun a b c => le_trans, fun a b => le_antisymm, le_total⟩ hne
  exact ⟨c', hc, hc', hlt, fun e he hce => hmin e ⟨he, hce⟩⟩

omit [Nonempty A] in
/-- Passing to the next clause removes exactly one clause from those still to
be checked. -/
theorem ncard_qclauses_next {c c' : A} (hnext : QbfNextCl k c c') :
    {e : A | QbfCl k e ∧ c ≤ e}.ncard = {e : A | QbfCl k e ∧ c' ≤ e}.ncard + 1 := by
  obtain ⟨hc, hc', hlt, hmin⟩ := hnext
  have hset : {e : A | QbfCl k e ∧ c ≤ e} = insert c {e : A | QbfCl k e ∧ c' ≤ e} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨he, hce⟩
      rcases eq_or_lt_of_le hce with rfl | hlt'
      · exact Or.inl rfl
      · exact Or.inr ⟨he, hmin e he hlt'⟩
    · rintro (rfl | ⟨he, hce⟩)
      · exact ⟨hc, le_refl _⟩
      · exact ⟨he, le_trans hlt.le hce⟩
  rw [hset,
    Set.ncard_insert_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr hlt)) (Set.toFinite _)]

/-- **A conjunctive matrix: the machine checks every remaining clause and
accepts**, in at most one sweep's worth of steps per clause. -/
theorem accepts_from_chk_cnf {cnf : Bool} (hcnf : cnf = true)
    (hsat : ∀ e : A, QbfCl k e → ∃ y : A, QGood k cnf e y (chkVal νs y)) :
    ∀ c : A, QbfCl k c →
      (∃ (n : ℕ) (cfin : Config (AltV k A)),
          n ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) ∧
          (altMachine k A cnf).StepsIn n (confChkL cnf νs c (posCell qtopA)) cfin ∧
            AltAccSt cfin.state) ∧
        ∃ (n : ℕ) (cfin : Config (AltV k A)),
          n ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) ∧
          (altMachine k A cnf).StepsIn n (confChkR cnf νs c (posCell qbotA)) cfin ∧
            AltAccSt cfin.state := by
  subst hcnf
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc
    have hpos : 0 < {e : A | QbfCl k e ∧ c ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hc, le_refl c⟩
    by_cases hmax : QbfMaxCl k c
    · have hflagL : chkFlagL true νs c (posStart : AltV k A) = true :=
        (chkFlagL_posStart true c).mpr (hsat c hc)
      have hflagR : chkFlagR true νs c (posEnd : AltV k A) = true :=
        (chkFlagR_posEnd true c).mpr (hsat c hc)
      obtain ⟨nL, hnL, cfL, hL, haL⟩ := steps_clauseAccL hc (fun _ => hmax) hflagL
      obtain ⟨nR, hnR, cfR, hR, haR⟩ := steps_clauseAccR hc (fun _ => hmax) hflagR
      exact ⟨⟨nL, cfL, hnL.trans (Nat.le_mul_of_pos_left _ hpos), hL, haL⟩,
        ⟨nR, cfR, hnR.trans (Nat.le_mul_of_pos_left _ hpos), hR, haR⟩⟩
    · obtain ⟨c', hnext⟩ := exists_qNextCl hc hmax
      obtain ⟨⟨nL, cfL, hnL, hL, haL⟩, ⟨nR, cfR, hnR, hR, haR⟩⟩ := IH c' hnext.2.2.1 hnext.2.1
      obtain ⟨j, hj, hstepL⟩ := steps_clauseL hc hnext (hsat c hc)
      obtain ⟨j', hj', hstepR⟩ := steps_clauseR hc hnext (hsat c hc)
      have hcount : ∀ {a b : ℕ}, a ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A) →
          b ≤ {e : A | QbfCl k e ∧ c' ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) →
          a + b ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) := by
        intro a b ha hb
        rw [ncard_qclauses_next hnext, Nat.succ_mul]
        exact (Nat.add_le_add ha hb).trans (le_of_eq (Nat.add_comm _ _))
      exact ⟨⟨j + nR, cfR, hcount hj hnR, stepsIn_add hstepL hR, haR⟩,
        ⟨j' + nL, cfL, hcount hj' hnL, stepsIn_add hstepR hL, haL⟩⟩

/-- **A disjunctive matrix: the machine walks the terms until one has no
violated literal, and accepts there.** The flag is *clear* at such a term,
which is exactly what the accepting turn fires at when `cnf` is `false`. -/
theorem accepts_from_chk_dnf {cnf : Bool} (hcnf : cnf = false) {c₀ : A} (hc₀ : QbfCl k c₀)
    (hgood : ∀ y : A, ¬QGood k cnf c₀ y (chkVal νs y)) :
    ∀ c : A, QbfCl k c → c ≤ c₀ →
      (∃ (n : ℕ) (cfin : Config (AltV k A)),
          n ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) ∧
          (altMachine k A cnf).StepsIn n (confChkL cnf νs c (posCell qtopA)) cfin ∧
            AltAccSt cfin.state) ∧
        ∃ (n : ℕ) (cfin : Config (AltV k A)),
          n ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) ∧
          (altMachine k A cnf).StepsIn n (confChkR cnf νs c (posCell qbotA)) cfin ∧
            AltAccSt cfin.state := by
  subst hcnf
  intro c
  induction c using WellFoundedGT.induction with
  | ind c IH =>
    intro hc hle
    have hpos : 0 < {e : A | QbfCl k e ∧ c ≤ e}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hc, le_refl c⟩
    have hnotmax : (false : Bool) = true → QbfMaxCl k c := fun h => absurd h (by simp)
    by_cases hsome : ∃ y : A, QGood k false c y (chkVal νs y)
    · -- some literal of this term is violated: take the next one
      have hne : c ≠ c₀ := by
        rintro rfl
        obtain ⟨y, hy⟩ := hsome
        exact hgood y hy
      have hlt : c < c₀ := lt_of_le_of_ne hle hne
      have hnmax : ¬QbfMaxCl k c := fun hm => absurd (hm.2 c₀ hc₀) (not_le.mpr hlt)
      obtain ⟨c', hnext⟩ := exists_qNextCl hc hnmax
      obtain ⟨⟨nL, cfL, hnL, hL, haL⟩, ⟨nR, cfR, hnR, hR, haR⟩⟩ :=
        IH c' hnext.2.2.1 hnext.2.1 (hnext.2.2.2 c₀ hc₀ hlt)
      obtain ⟨j, hj, hstepL⟩ := steps_clauseL hc hnext hsome
      obtain ⟨j', hj', hstepR⟩ := steps_clauseR hc hnext hsome
      have hcount : ∀ {a b : ℕ}, a ≤ bitRank tagTupleLe AltPosn (posEnd : AltV k A) →
          b ≤ {e : A | QbfCl k e ∧ c' ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) →
          a + b ≤ {e : A | QbfCl k e ∧ c ≤ e}.ncard *
            bitRank tagTupleLe AltPosn (posEnd : AltV k A) := by
        intro a b ha hb
        rw [ncard_qclauses_next hnext, Nat.succ_mul]
        exact (Nat.add_le_add ha hb).trans (le_of_eq (Nat.add_comm _ _))
      exact ⟨⟨j + nR, cfR, hcount hj hnR, stepsIn_add hstepL hR, haR⟩,
        ⟨j' + nL, cfL, hcount hj' hnL, stepsIn_add hstepR hL, haL⟩⟩
    · -- no literal of this term is violated: accept here
      have hflagL : chkFlagL false νs c (posStart : AltV k A) = false := by
        rw [Bool.eq_false_iff]
        intro hcon
        exact hsome ((chkFlagL_posStart false c).mp hcon)
      have hflagR : chkFlagR false νs c (posEnd : AltV k A) = false := by
        rw [Bool.eq_false_iff]
        intro hcon
        exact hsome ((chkFlagR_posEnd false c).mp hcon)
      obtain ⟨nL, hnL, cfL, hL, haL⟩ := steps_clauseAccL hc hnotmax hflagL
      obtain ⟨nR, hnR, cfR, hR, haR⟩ := steps_clauseAccR hc hnotmax hflagR
      exact ⟨⟨nL, cfL, hnL.trans (Nat.le_mul_of_pos_left _ hpos), hL, haL⟩,
        ⟨nR, cfR, hnR.trans (Nat.le_mul_of_pos_left _ hpos), hR, haR⟩⟩

/-! ### A deterministic run accepts at either polarity

The check phase is deterministic, so its run is a legitimate move for the
universal player as much as for the existential one: “every successor accepts”
and “some successor accepts” say the same thing when there is exactly one. -/

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- **A deterministic run accepts whatever the polarity of its block.** The
existential half is `DescriptiveComplexity.ATMData.altAcc_of_steps`; this is
the version that also serves a universal block, and could be hoisted to
`DescriptiveComplexity.MachinesAltPlay`. -/
theorem altAcc_of_stepsIn_det {M : ATMData (AltV k A)} {start : Bool}
    {P : Config (AltV k A) → Prop}
    (hclosed : ∀ e e', P e → M.Step e e' → P e')
    (hdet : ∀ e e' e'', P e → M.Step e e' → M.Step e e'' → e' = e'') :
    ∀ (m n : ℕ) (c d : Config (AltV k A)), m ≤ n → P c → M.StepsIn m c d → M.Acc d.state →
      M.AltAcc start n c := by
  intro m
  induction m with
  | zero =>
    intro n c d _ _ hrun hacc
    exact ATMData.altAcc_of_acc ((show c = d from hrun) ▸ hacc)
  | succ m ih =>
    intro n c d hmn hP hrun hacc
    obtain ⟨c₁, hstep, hrest⟩ := hrun
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hrec : M.AltAcc start n' c₁ :=
      ih n' c₁ d (by omega) (hclosed c c₁ hP hstep) hrest hacc
    by_cases hu : M.IsUniv start c.state
    · exact Or.inr (Or.inl ⟨hu, ⟨c₁, hstep⟩, fun c' hc' => (hdet c c' c₁ hP hc' hstep) ▸ hrec⟩)
    · exact Or.inr (Or.inr ⟨hu, c₁, hstep, hrec⟩)

/-! ### The check phase is deterministic -/

/-- Being in the check phase: the state is a checking state or the accepting
one. -/
def InCheck (c : Config (AltV k A)) : Prop :=
  (∃ (f d : Bool) (cl : A), c.state = stChk f d cl) ∨ c.state = stAcc

/-- The check phase never returns to a sweep. -/
theorem inCheck_closed {cnf : Bool} (c c' : Config (AltV k A)) (hP : InCheck c)
    (hstep : (altMachine k A cnf).Step c c') : InCheck c' := by
  obtain ⟨τ, hτ, hsrc, -, hdst, -⟩ := hstep
  have hne : ∀ (i : Fin (k + 1)) (b : Bool), c.state ≠ stG i b := by
    intro i b h
    rcases hP with ⟨f, d, cl, hc⟩ | hc <;>
      exact absurd (congrArg (fun p => p.1.1) (hc.symm.trans h)) (by simp [acstI, aoneI])
  revert hτ hsrc hdst
  change AltTr cnf τ → AltSrc cnf τ c.state → AltDst cnf τ c'.state → InCheck c'
  unfold AltTr AltSrc AltDst
  cases hb : τ.1.1 <;> intro hτ hsrc hdst <;>
    first
      | exact hτ.elim
      | exact absurd hsrc (hne _ _)
      | (rcases hdst with ⟨h, -⟩ | ⟨h, -, -⟩ <;> exact Or.inl ⟨_, _, _, h⟩)
      | exact Or.inl ⟨_, _, _, hdst⟩
      | exact Or.inr hdst

/-- The check phase is deterministic: none of its configurations is a guessing
choice. -/
theorem inCheck_det {cnf : Bool} (c c' c'' : Config (AltV k A)) (hP : InCheck c)
    (h₁ : (altMachine k A cnf).Step c c') (h₂ : (altMachine k A cnf).Step c c'') : c' = c'' := by
  refine step_functional_off_guess ?_ h₁ h₂
  rintro ⟨i, x, hc, -⟩
  rcases hP with ⟨f, d, cl, hc'⟩ | hc' <;>
    exact absurd (congrArg (fun p => p.1.1) (hc'.symm.trans hc)) (by simp [acstI, aoneI])

/-- **The check phase accepts**, at either polarity of its block, as soon as a
run through it reaches an accepting state. -/
theorem altAcc_of_check {cnf : Bool} {start : Bool} {m n : ℕ} {c d : Config (AltV k A)}
    (hmn : m ≤ n) (hP : InCheck c) (hrun : (altMachine k A cnf).StepsIn m c d)
    (hacc : AltAccSt d.state) : (altMachine k A cnf).AltAcc start n c :=
  altAcc_of_stepsIn_det (fun e e' => inCheck_closed e e') (fun e e' e'' => inCheck_det e e' e'')
    m n c d hmn hP hrun hacc

/-! ### The run is short enough

The budget of `DescriptiveComplexity.ATMData.AltAccepts` counts the positions
of the tape, of which the fillers alone supply `8(k+1)n²`. A sweep, by
contrast, costs about as many steps as the instance has *elements*: only the
left marker and the cells lie below the right marker. -/

omit [(Language.qbf k).Structure A] in
/-- Only the three bracketing base tags are at or below the right marker's. -/
theorem base_le_pEnd {t : AltBase} (h : altBaseIdx t ≤ altBaseIdx AltBase.pEnd) :
    t = AltBase.pStart ∨ t = AltBase.pCell ∨ t = AltBase.pEnd := by
  revert h; revert t; decide

omit [(Language.qbf k).Structure A] in
/-- **A sweep is short.** Proved by injecting the positions below the right
marker into `Option A` rather than by counting. -/
theorem bitRank_posEnd_le :
    bitRank tagTupleLe AltPosn (posEnd : AltV k A) ≤ Nat.card A + 1 := by
  classical
  have hcell : ∀ r : AltV k A, AltPosn r → tagTupleLe r posEnd → r ≠ posEnd →
      r.1.1 ≠ AltBase.pStart → r.1.1 = AltBase.pCell := by
    intro r hr hle hne hns
    rcases base_le_pEnd (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hle)) with h | h | h
    · exact absurd h hns
    · exact h
    · exact absurd (eq_posEnd_of_posn hr h) hne
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (fun r : AltV k A => if r.1.1 = AltBase.pStart then none else some (r.2 0))
    (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)) ?_
  · rintro r ⟨hr, hle, hne⟩ r' ⟨hr', hle', hne'⟩ heq
    by_cases hs : r.1.1 = AltBase.pStart <;> by_cases hs' : r'.1.1 = AltBase.pStart
    · rw [eq_posStart_of_posn hr hs, eq_posStart_of_posn hr' hs']
    · simp [hs, hs'] at heq
    · simp [hs, hs'] at heq
    · have h0 : r.2 0 = r'.2 0 := by simpa [hs, hs'] using heq
      rw [eq_posCell_of_posn hr (hcell r hr hle hne hs),
        eq_posCell_of_posn hr' (hcell r' hr' hle' hne' hs'), h0]
  · rw [Set.ncard_univ]
    haveI := Fintype.ofFinite A
    simp [Nat.card_eq_fintype_card]

omit [(Language.qbf k).Structure A] in
/-- **A sweep costs about twice the size of the instance**: down the tape and
back. -/
theorem sweepLen_le : sweepLen k A ≤ 2 * (Nat.card A + 1) := by
  have h1 := bitRank_posStart (k := k) (A := A)
  have h2 := bitRank_posEnd_eq (k := k) (A := A)
  have h3 := bitRank_posCell_qbotA (k := k) (A := A)
  have h4 := bitRank_posEnd_le (k := k) (A := A)
  simp only [sweepLen]
  omega

end Check

end AltQbf

end DescriptiveComplexity
