/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.QsatStep
import DescriptiveComplexity.Problems.Machine.DetRun

/-!
# The run of the QBF machine

What the machine computes. This file opens with the dictionary between a *tape*
and a *valuation*, since that is what the evaluation sweep and the game
semantics have to be compared through.

A tape of the machine is `laid out` (`DescriptiveComplexity.QsatTM.TapeOk`) when
every quantified variable's cell holds one of the four `sVal` symbols – which
the initial tape does and every transition preserves. Such a tape *is* a
valuation (`DescriptiveComplexity.QsatTM.TapeTrue`: the variable is true when its
cell holds the value `true`), and under that dictionary the first-order literal
test the transition table performs (`DescriptiveComplexity.QsatTM.QLit`) is the
literal of `DescriptiveComplexity.QsatMatrix`. `DescriptiveComplexity.QsatTM.qsatMatrix_iff`
is the resulting reading of the matrix: it holds exactly when every clause has
a variable whose cell satisfies it, which is what one full sweep of the
`Eval` phase decides.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QsatTM

noncomputable section Run

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {σ : QV A → QV A}

/-! ### A tape is a valuation -/

/-- **A tape is laid out** when every quantified variable's cell holds a value
and a flag. The initial tape is, and every transition preserves it. -/
def TapeOk (σ : QV A → QV A) : Prop :=
  ∀ x : A, IsQVar x → ∃ b f : Bool, σ (posCell x) = symV b f x

/-- **The valuation a tape encodes**: the variable `x` is true when its cell
holds the value `true`. -/
def TapeTrue (σ : QV A → QV A) (x : A) : Prop := ∃ f : Bool, σ (posCell x) = symV true f x

omit [Language.qsat.Structure A] in
/-- Reading the valuation off a cell whose contents are known. -/
theorem tapeTrue_iff {x : A} {b f : Bool} (hσ : σ (posCell x) = symV b f x) :
    TapeTrue σ x ↔ b = true := by
  constructor
  · rintro ⟨f', hf⟩
    have h := (qOne_eq_qOne_iff.mp (hσ.symm.trans hf)).1
    simp only [QTag.sVal.injEq] at h
    exact h.1
  · rintro rfl
    exact ⟨f, hσ⟩

/-- **The transition table's literal test is the literal of the matrix.** The
sweep asks `QLit c x b` of the symbol it reads; the game asks whether the
valuation satisfies the literal. Under the dictionary they agree. -/
theorem qLit_iff_tapeTrue {c x : A} {b f : Bool} (hσ : σ (posCell x) = symV b f x) :
    QLit c x b ↔ ((QPosIn c x ∧ TapeTrue σ x) ∨ (QNegIn c x ∧ ¬TapeTrue σ x)) := by
  rw [QLit, tapeTrue_iff hσ]
  constructor
  · rintro (⟨h, hb⟩ | ⟨h, hb⟩)
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨h, by rw [hb]; exact Bool.false_ne_true⟩
  · rintro (⟨h, hb⟩ | ⟨h, hb⟩)
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨h, Bool.eq_false_iff.mpr hb⟩

/-! ### The matrix, read off the tape -/

/-- **The matrix holds of a laid-out tape exactly when every clause has a cell
satisfying it.** The right-hand side is what one full sweep of the evaluation
phase decides, clause by clause; the left-hand side is what the game asks at a
leaf. -/
theorem qsatMatrix_iff (hok : TapeOk σ) :
    QsatMatrix (TapeTrue σ) ↔
      ∀ c : A, QCl c → ∃ (x : A) (b f : Bool),
        IsQVar x ∧ σ (posCell x) = symV b f x ∧ QLit c x b := by
  constructor
  · intro hm c hc
    obtain ⟨x, hx, hlit⟩ := hm c hc
    obtain ⟨b, f, hσ⟩ := hok x hx
    exact ⟨x, b, f, hx, hσ, (qLit_iff_tapeTrue hσ).mpr hlit⟩
  · intro h c hc
    obtain ⟨x, b, f, hx, hσ, hlit⟩ := h c hc
    exact ⟨x, hx, (qLit_iff_tapeTrue hσ).mp hlit⟩


/-! ### Writing a cell

Every transition that changes the tape changes one cell of one variable, so the
run only ever needs this one update. The step lemmas of
`DescriptiveComplexity.Problems.Machine.QsatStep` take the next tape as an arbitrary
`σ'` pinned at the head; `DescriptiveComplexity.QsatTM.setCell` is the `σ'` the run
will always pass them. -/

open Classical in
/-- The tape `σ` with the cell of `x` set to the value `b` and the flag `f`. -/
noncomputable def setCell (σ : QV A → QV A) (x : A) (b f : Bool) : QV A → QV A :=
  fun r => if r = posCell x then symV b f x else σ r

omit [Language.qsat.Structure A] in
@[simp] theorem setCell_self (x : A) (b f : Bool) :
    setCell σ x b f (posCell x) = symV b f x := by
  simp [setCell]

omit [Language.qsat.Structure A] in
theorem setCell_ne {x : A} {b f : Bool} {r : QV A} (h : r ≠ posCell x) :
    setCell σ x b f r = σ r := by
  simp [setCell, h]

omit [Language.qsat.Structure A] in
/-- Another variable's cell is untouched. -/
theorem setCell_other {x y : A} {b f : Bool} (h : y ≠ x) :
    setCell σ x b f (posCell y) = σ (posCell y) :=
  setCell_ne fun he => h (qOne_eq_qOne_iff.mp he).2

/-- Writing a cell keeps the tape laid out. -/
theorem tapeOk_setCell (hok : TapeOk σ) (x : A) (b f : Bool) : TapeOk (setCell σ x b f) := by
  intro y hy
  rcases eq_or_ne y x with rfl | hne
  · exact ⟨b, f, setCell_self y b f⟩
  · obtain ⟨b', f', h⟩ := hok y hy
    exact ⟨b', f', (setCell_other hne).trans h⟩

omit [Language.qsat.Structure A] in
/-- Writing a cell sets that variable's value. -/
@[simp] theorem tapeTrue_setCell_self {x : A} {b f : Bool} :
    TapeTrue (setCell σ x b f) x ↔ b = true :=
  tapeTrue_iff (setCell_self x b f)

omit [Language.qsat.Structure A] in
/-- Writing a cell leaves every other variable's value alone. -/
theorem tapeTrue_setCell_other {x y : A} {b f : Bool} (h : y ≠ x) :
    TapeTrue (setCell σ x b f) y ↔ TapeTrue σ y := by
  rw [TapeTrue, TapeTrue, setCell_other h]

omit [Language.qsat.Structure A] in
/-- The frame condition the step lemmas ask for, discharged for
`DescriptiveComplexity.QsatTM.setCell`. -/
theorem setCell_frame (x : A) (b f : Bool) :
    ∀ r : QV A, r ≠ posCell x → setCell σ x b f r = σ r :=
  fun _ h => setCell_ne h


/-! ### The descent

The machine's first act, and the act it repeats every time a level switches to
its second value: sweep rightwards to the right marker, resetting every
variable's cell on the way. The sweep is the segment primitive of
`DescriptiveComplexity.Problems.Machine.Program`, whose configuration family is
`p ↦ ⟨stDesc, p, resetSeg σ p₀ p⟩` – the tape with every variable cell of the
half-open segment `[p₀, p)` reset. -/

open Classical in
/-- The tape `σ` with every variable cell of the segment `[p₀, p)` reset. -/
noncomputable def resetSeg (σ : QV A → QV A) (p₀ p r : QV A) : QV A :=
  if QPosn r ∧ r.1 = QTag.pCell ∧ QLe p₀ r ∧ QLe r p ∧ r ≠ p then symV false false (r.2 0)
  else σ r

theorem resetSeg_of_not {p₀ p r : QV A}
    (h : ¬(QPosn r ∧ r.1 = QTag.pCell ∧ QLe p₀ r ∧ QLe r p ∧ r ≠ p)) :
    resetSeg σ p₀ p r = σ r := by
  rw [resetSeg, if_neg h]

theorem resetSeg_self (p₀ p : QV A) : resetSeg σ p₀ p p = σ p :=
  resetSeg_of_not fun h => h.2.2.2.2 rfl

/-- An empty segment changes nothing. -/
theorem resetSeg_bot (hwf : QsatWf A) (p₀ : QV A) : resetSeg σ p₀ p₀ = σ := by
  funext r
  refine resetSeg_of_not fun h => h.2.2.2.2 ?_
  exact (isLinOrd_qLe A hwf).2.2.1 _ _ h.2.2.2.1 h.2.2.1

/-- Extending the segment by one position changes only that position. -/
theorem resetSeg_frame (hwf : QsatWf A) {p₀ p q : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn p q) (hle : QLe p₀ p) :
    ∀ r : QV A, r ≠ p → resetSeg σ p₀ q r = resetSeg σ p₀ p r := by
  obtain ⟨-, htrans, hanti, htotal⟩ := isLinOrd_qLe A hwf
  intro r hr
  have hiff : (QPosn r ∧ r.1 = QTag.pCell ∧ QLe p₀ r ∧ QLe r q ∧ r ≠ q) ↔
      (QPosn r ∧ r.1 = QTag.pCell ∧ QLe p₀ r ∧ QLe r p ∧ r ≠ p) := by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, ?_, hr⟩
      rcases htotal r p with h | h
      · exact h
      · rcases hs.2.2.2.2 r h1 h h4 with rfl | rfl
        · exact absurd rfl hr
        · exact absurd rfl h5
    · rintro ⟨h1, h2, h3, h4, -⟩
      refine ⟨h1, h2, h3, htrans _ _ _ h4 hs.2.2.1, fun he => ?_⟩
      exact hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ h4))
  rw [resetSeg, resetSeg]
  by_cases h : QPosn r ∧ r.1 = QTag.pCell ∧ QLe p₀ r ∧ QLe r p ∧ r ≠ p
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

/-- Extending the segment past a variable's cell resets that cell. -/
theorem resetSeg_at {p₀ p q : QV A} {x : A} (hs : SuccPos (QLe (A := A)) QPosn p q)
    (hle : QLe p₀ p) (hp : p = posCell x) :
    resetSeg σ p₀ q p = symV false false x := by
  rw [resetSeg, if_pos ⟨hs.1, by rw [hp]; rfl, hle, hs.2.2.1, hs.2.2.2.1⟩, hp]
  rfl

/-- **The descent runs to the right marker**, resetting every variable's cell
from `p₀` on. -/
theorem reach_descent (hwf : QsatWf A) (hok : TapeOk σ) (hstart : σ posStart = symStart)
    {p₀ : QV A} (hp₀ : QPosn p₀) :
    Relation.ReflTransGen (qsatMachine A).Step ⟨stDesc, p₀, σ⟩
      ⟨stDesc, posEnd, resetSeg σ p₀ posEnd⟩ := by
  have hlin : IsLinOrd (qsatMachine A).Le := isLinOrd_qLe A hwf
  have hstep : ∀ p q : QV A, SuccPos (QLe (A := A)) QPosn p q → QLe p₀ p → QLe q posEnd →
      (qsatMachine A).Step ⟨stDesc, p, resetSeg σ p₀ p⟩ ⟨stDesc, q, resetSeg σ p₀ q⟩ := by
    intro p q hs hle _
    rcases (qPosn_iff p).mp hs.1 with rfl | ⟨x, hx, rfl⟩ | rfl
    · have heq : resetSeg σ p₀ q = resetSeg σ p₀ (posStart : QV A) := by
        funext r
        rcases eq_or_ne r posStart with rfl | hne
        · rw [resetSeg_self]
          exact resetSeg_of_not fun h => QTag.noConfusion h.2.1
        · exact resetSeg_frame hwf hs hle r hne
      rw [heq]
      exact step_descStart ((resetSeg_self _ _).trans hstart) hs
    · obtain ⟨b, f, hbf⟩ := hok x hx
      exact step_descCell hx ((resetSeg_self _ _).trans hbf) (resetSeg_at hs hle rfl)
        (resetSeg_frame hwf hs hle) hs
    · exact absurd (hlin.2.2.1 _ _ hs.2.2.1 ((maxPos_posEnd hwf).2 q hs.2.1)) hs.2.2.2.1
  have h := TMData.stepsIn_of_segment (M := qsatMachine A) hlin (conf := fun p =>
      ⟨stDesc, p, resetSeg σ p₀ p⟩) hp₀ hstep posEnd qPosn_posEnd
    ((maxPos_posEnd hwf).2 _ hp₀) (hlin.1 _)
  have h' := TMData.reflTransGen_of_stepsIn h
  rwa [resetSeg_bot hwf] at h'


/-! ### The evaluation sweep

One pass over the tape for one clause. The state carries the flag, and the flag
at a position is exactly "some variable's cell already swept satisfies the
clause"; the pass therefore ends at the far marker with the flag set iff the
clause holds of the tape. -/

/-- A variable's cell satisfies the clause `c`. -/
def CellSat (σ : QV A → QV A) (c x : A) : Prop :=
  ∃ b f : Bool, IsQVar x ∧ σ (posCell x) = symV b f x ∧ QLit c x b

/-- Some cell strictly above `p` satisfies the clause: the flag of a leftward
sweep that has reached `p`. -/
def SatAbove (σ : QV A → QV A) (c : A) (p : QV A) : Prop :=
  ∃ x : A, CellSat σ c x ∧ QLe p (posCell x) ∧ posCell x ≠ p

/-- Some cell satisfies the clause: what a whole pass decides. -/
def SatAll (σ : QV A → QV A) (c : A) : Prop := ∃ x : A, CellSat σ c x

open Classical in
/-- The flag of a leftward sweep that has reached `p`. -/
noncomputable def flagAbove (σ : QV A → QV A) (c : A) (p : QV A) : Bool :=
  decide (SatAbove σ c p)

theorem flagAbove_eq_true (σ : QV A → QV A) (c : A) (p : QV A) :
    flagAbove σ c p = true ↔ SatAbove σ c p := by
  classical
  rw [flagAbove, decide_eq_true_iff]

theorem flagAbove_eq_false (σ : QV A → QV A) (c : A) (p : QV A) :
    flagAbove σ c p = false ↔ ¬SatAbove σ c p := by
  rw [← Bool.not_eq_true, flagAbove_eq_true]

/-- **The flag accumulates**: sweeping one cell further adds that cell's
verdict. -/
theorem satAbove_succ (hwf : QsatWf A) {c x b f : _} {p q : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn p q) (hq : q = posCell x) (hx : IsQVar x)
    (hσ : σ (posCell x) = symV b f x) :
    SatAbove σ c p ↔ (SatAbove σ c q ∨ QLit c x b) := by
  obtain ⟨-, htrans, hanti, htotal⟩ := isLinOrd_qLe A hwf
  subst hq
  constructor
  · rintro ⟨y, ⟨b', f', hy, hσy, hlit⟩, hle, hne⟩
    rcases eq_or_ne (posCell y : QV A) (posCell x) with he | hne'
    · obtain rfl : y = x := (qOne_eq_qOne_iff.mp he).2
      have hb : b' = b := by
        have h := (qOne_eq_qOne_iff.mp (hσy.symm.trans hσ)).1
        simp only [QTag.sVal.injEq] at h
        exact h.1
      exact Or.inr (hb ▸ hlit)
    · refine Or.inl ⟨y, ⟨b', f', hy, hσy, hlit⟩, ?_, hne'⟩
      rcases htotal (posCell y : QV A) (posCell x) with h | h
      · rcases hs.2.2.2.2 _ (qPosn_posCell hy) hle h with he | he
        · exact absurd he hne
        · exact absurd he hne'
      · exact h
  · rintro (⟨y, hy, hle, hne⟩ | hlit)
    · refine ⟨y, hy, htrans _ _ _ hs.2.2.1 hle, fun he => ?_⟩
      exact hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ hle))
    · exact ⟨x, ⟨b, f, hx, hσ, hlit⟩, hs.2.2.1, fun he => hs.2.2.2.1 he.symm⟩

/-- At the left marker the flag is the verdict on the whole tape. -/
theorem satAbove_posStart (σ : QV A → QV A) (c : A) :
    SatAbove σ c posStart ↔ SatAll σ c := by
  constructor
  · rintro ⟨x, hx, -, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, qLe_start_cell x, fun he => QTag.noConfusion (congrArg Prod.fst he)⟩

/-- Just below the right marker nothing has been swept yet. -/
theorem not_satAbove_top (σ : QV A → QV A) (c : A) {p₁ : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn p₁ posEnd) : ¬SatAbove σ c p₁ := by
  rintro ⟨x, ⟨-, -, hx, -, -⟩, hle, hne⟩
  rcases hs.2.2.2.2 _ (qPosn_posCell hx) hle (qLe_cell_end x) with he | he
  · exact hne he
  · exact QTag.noConfusion (congrArg Prod.fst he)


/-- **A leftward pass decides the clause.** From just below the right marker,
with the flag down, the machine sweeps to the left marker and arrives with the
flag set exactly when some cell satisfies the clause. -/
theorem reach_sweepDown (hwf : QsatWf A) (hok : TapeOk σ) {c : A} (hc : QCl c) {p₁ : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn p₁ posEnd) :
    Relation.ReflTransGen (qsatMachine A).Step ⟨stEval false false c, p₁, σ⟩
      ⟨stEval (flagAbove σ c posStart) false c, posStart, σ⟩ := by
  have hlin : IsLinOrd (qsatMachine A).Le := isLinOrd_qLe A hwf
  have hstep : ∀ p q : QV A, SuccPos (QLe (A := A)) QPosn p q → QLe posStart p → QLe q p₁ →
      (qsatMachine A).Step ⟨stEval (flagAbove σ c q) false c, q, σ⟩
        ⟨stEval (flagAbove σ c p) false c, p, σ⟩ := by
    intro p q hs' hlb hub
    rcases (qPosn_iff q).mp hs'.2.1 with rfl | ⟨x, hx, rfl⟩ | rfl
    · exact absurd (hlin.2.2.1 _ _ hs'.2.2.1 ((minPos_posStart hwf).2 p hs'.1)) hs'.2.2.2.1
    · obtain ⟨b, f, hbf⟩ := hok x hx
      have hupd := satAbove_succ hwf hs' rfl hx hbf (c := c)
      by_cases hp : SatAbove σ c p
      · have hpt : flagAbove σ c p = true := (flagAbove_eq_true σ c p).mpr hp
        rw [hpt]
        refine step_eval_true hc hx ?_ hbf (Or.inr ⟨rfl, hs'⟩)
        rcases hupd.mp hp with h | h
        · exact Or.inl ((flagAbove_eq_true σ c _).mpr h)
        · exact Or.inr h
      · have hqf : flagAbove σ c (posCell x) = false :=
          (flagAbove_eq_false σ c _).mpr fun h => hp (hupd.mpr (Or.inl h))
        have hpf : flagAbove σ c p = false := (flagAbove_eq_false σ c p).mpr hp
        rw [hqf, hpf]
        exact step_eval_false hc hx (fun h => hp (hupd.mpr (Or.inr h))) hbf (Or.inr ⟨rfl, hs'⟩)
    · exact absurd (hlin.2.2.1 _ _ ((maxPos_posEnd hwf).2 p₁ hs.1) hub) hs.2.2.2.1
  have hfalse : flagAbove σ c p₁ = false :=
    (flagAbove_eq_false σ c p₁).mpr (not_satAbove_top σ c hs)
  have h := TMData.stepsIn_of_segment_down (M := qsatMachine A) hlin
    (conf := fun p => ⟨stEval (flagAbove σ c p) false c, p, σ⟩) hs.1 hstep posStart qPosn_posStart
    (hlin.1 _) ((minPos_posStart hwf).2 p₁ hs.1)
  rw [hfalse] at h
  exact TMData.reflTransGen_of_stepsIn h


/-- Some cell strictly below `p` satisfies the clause: the flag of a rightward
sweep that has reached `p`. -/
def SatBelow (σ : QV A → QV A) (c : A) (p : QV A) : Prop :=
  ∃ x : A, CellSat σ c x ∧ QLe (posCell x) p ∧ posCell x ≠ p

open Classical in
/-- The flag of a rightward sweep that has reached `p`. -/
noncomputable def flagBelow (σ : QV A → QV A) (c : A) (p : QV A) : Bool :=
  decide (SatBelow σ c p)

theorem flagBelow_eq_true (σ : QV A → QV A) (c : A) (p : QV A) :
    flagBelow σ c p = true ↔ SatBelow σ c p := by
  classical
  rw [flagBelow, decide_eq_true_iff]

theorem flagBelow_eq_false (σ : QV A → QV A) (c : A) (p : QV A) :
    flagBelow σ c p = false ↔ ¬SatBelow σ c p := by
  rw [← Bool.not_eq_true, flagBelow_eq_true]

/-- **The flag accumulates**, rightwards. -/
theorem satBelow_succ (hwf : QsatWf A) {c x b f : _} {p q : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn p q) (hp : p = posCell x) (hx : IsQVar x)
    (hσ : σ (posCell x) = symV b f x) :
    SatBelow σ c q ↔ (SatBelow σ c p ∨ QLit c x b) := by
  obtain ⟨-, htrans, hanti, htotal⟩ := isLinOrd_qLe A hwf
  subst hp
  constructor
  · rintro ⟨y, ⟨b', f', hy, hσy, hlit⟩, hle, hne⟩
    rcases eq_or_ne (posCell y : QV A) (posCell x) with he | hne'
    · obtain rfl : y = x := (qOne_eq_qOne_iff.mp he).2
      have hb : b' = b := by
        have h := (qOne_eq_qOne_iff.mp (hσy.symm.trans hσ)).1
        simp only [QTag.sVal.injEq] at h
        exact h.1
      exact Or.inr (hb ▸ hlit)
    · refine Or.inl ⟨y, ⟨b', f', hy, hσy, hlit⟩, ?_, hne'⟩
      rcases htotal (posCell x : QV A) (posCell y) with h | h
      · rcases hs.2.2.2.2 _ (qPosn_posCell hy) h hle with he | he
        · exact absurd he hne'
        · exact absurd he hne
      · exact h
  · rintro (⟨y, hy, hle, hne⟩ | hlit)
    · refine ⟨y, hy, htrans _ _ _ hle hs.2.2.1, fun he => ?_⟩
      exact hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ hle))
    · exact ⟨x, ⟨b, f, hx, hσ, hlit⟩, hs.2.2.1, hs.2.2.2.1⟩

/-- At the right marker the flag is the verdict on the whole tape. -/
theorem satBelow_posEnd (σ : QV A → QV A) (c : A) :
    SatBelow σ c posEnd ↔ SatAll σ c := by
  constructor
  · rintro ⟨x, hx, -, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, qLe_cell_end x, fun he => QTag.noConfusion (congrArg Prod.fst he)⟩

/-- Just above the left marker nothing has been swept yet. -/
theorem not_satBelow_bot (σ : QV A → QV A) (c : A) {p₀ : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn posStart p₀) : ¬SatBelow σ c p₀ := by
  rintro ⟨x, ⟨-, -, hx, -, -⟩, hle, hne⟩
  rcases hs.2.2.2.2 _ (qPosn_posCell hx) (qLe_start_cell x) hle with he | he
  · exact QTag.noConfusion (congrArg Prod.fst he)
  · exact hne he

/-- **A rightward pass decides the clause.** -/
theorem reach_sweepUp (hwf : QsatWf A) (hok : TapeOk σ) {c : A} (hc : QCl c) {p₀ : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn posStart p₀) :
    Relation.ReflTransGen (qsatMachine A).Step ⟨stEval false true c, p₀, σ⟩
      ⟨stEval (flagBelow σ c posEnd) true c, posEnd, σ⟩ := by
  have hlin : IsLinOrd (qsatMachine A).Le := isLinOrd_qLe A hwf
  have hstep : ∀ p q : QV A, SuccPos (QLe (A := A)) QPosn p q → QLe p₀ p → QLe q posEnd →
      (qsatMachine A).Step ⟨stEval (flagBelow σ c p) true c, p, σ⟩
        ⟨stEval (flagBelow σ c q) true c, q, σ⟩ := by
    intro p q hs' hlb _
    rcases (qPosn_iff p).mp hs'.1 with rfl | ⟨x, hx, rfl⟩ | rfl
    · exact absurd (hlin.2.2.1 _ _ ((minPos_posStart hwf).2 p₀ hs.2.1) hlb) hs.2.2.2.1
    · obtain ⟨b, f, hbf⟩ := hok x hx
      have hupd := satBelow_succ hwf hs' rfl hx hbf (c := c)
      by_cases hq : SatBelow σ c q
      · have hqt : flagBelow σ c q = true := (flagBelow_eq_true σ c q).mpr hq
        rw [hqt]
        refine step_eval_true hc hx ?_ hbf (Or.inl ⟨rfl, hs'⟩)
        rcases hupd.mp hq with h | h
        · exact Or.inl ((flagBelow_eq_true σ c _).mpr h)
        · exact Or.inr h
      · have hpf : flagBelow σ c (posCell x) = false :=
          (flagBelow_eq_false σ c _).mpr fun h => hq (hupd.mpr (Or.inl h))
        have hqf : flagBelow σ c q = false := (flagBelow_eq_false σ c q).mpr hq
        rw [hpf, hqf]
        exact step_eval_false hc hx (fun h => hq (hupd.mpr (Or.inr h))) hbf (Or.inl ⟨rfl, hs'⟩)
    · exact absurd (hlin.2.2.1 _ _ hs'.2.2.1 ((maxPos_posEnd hwf).2 q hs'.2.1)) hs'.2.2.2.1
  have hfalse : flagBelow σ c p₀ = false :=
    (flagBelow_eq_false σ c p₀).mpr (not_satBelow_bot σ c hs)
  have h := TMData.stepsIn_of_segment (M := qsatMachine A) hlin
    (conf := fun p => ⟨stEval (flagBelow σ c p) true c, p, σ⟩) hs.2.1 hstep posEnd qPosn_posEnd
    ((maxPos_posEnd hwf).2 p₀ hs.2.1) (hlin.1 _)
  rw [hfalse] at h
  exact TMData.reflTransGen_of_stepsIn h


/-! ### The clause loop

One pass per clause, alternating direction, until a clause fails or the last
one succeeds. The recursion is on the clause in the ambient order, which is
well founded because the instance is finite. -/

open Classical in
/-- The verdict on one clause. -/
noncomputable def satFlag (σ : QV A → QV A) (c : A) : Bool := decide (SatAll σ c)

open Classical in
/-- The verdict on every clause from `c` on: what the loop started at `c`
returns. -/
noncomputable def matrixFrom (σ : QV A → QV A) (c : A) : Bool :=
  decide (∀ e : A, QCl e → c ≤ e → SatAll σ e)

theorem flagAbove_posStart (σ : QV A → QV A) (c : A) :
    flagAbove σ c posStart = satFlag σ c := by
  classical
  rw [flagAbove, satFlag]
  exact decide_eq_decide.mpr (satAbove_posStart σ c)

theorem flagBelow_posEnd (σ : QV A → QV A) (c : A) :
    flagBelow σ c posEnd = satFlag σ c := by
  classical
  rw [flagBelow, satFlag]
  exact decide_eq_decide.mpr (satBelow_posEnd σ c)

/-- Where a sweep in direction `d` starts: one step in from the marker it will
end at going the other way. -/
def SweepStart (d : Bool) (p : QV A) : Prop :=
  if d then SuccPos (QLe (A := A)) QPosn posStart p else SuccPos (QLe (A := A)) QPosn p posEnd

/-- **One pass**: whatever the direction, the machine sweeps from its starting
position to the far marker and arrives with the clause's verdict. -/
theorem reach_pass (hwf : QsatWf A) (hok : TapeOk σ) {c : A} (hc : QCl c) {d : Bool}
    {p : QV A} (hp : SweepStart d p) :
    Relation.ReflTransGen (qsatMachine A).Step ⟨stEval false d c, p, σ⟩
      ⟨stEval (satFlag σ c) d c, markerPos d, σ⟩ := by
  cases d
  · rw [← flagAbove_posStart]
    exact reach_sweepDown hwf hok hc hp
  · rw [← flagBelow_posEnd]
    exact reach_sweepUp hwf hok hc hp

/-- An unsatisfied clause is a counterexample to every clause from `c` on. -/
theorem matrixFrom_eq_false {σ : QV A → QV A} {c : A} (hc : QCl c) (h : ¬SatAll σ c) :
    matrixFrom σ c = false := by
  classical
  rw [matrixFrom, decide_eq_false_iff_not]
  exact fun hall => h (hall c hc le_rfl)

/-- The last clause satisfied settles the loop. -/
theorem matrixFrom_eq_true_of_max {σ : QV A → QV A} {c : A} (hc : QMaxCl c)
    (h : SatAll σ c) : matrixFrom σ c = true := by
  classical
  rw [matrixFrom, decide_eq_true_iff]
  intro e he hle
  exact (le_antisymm (hc.2 e he) hle) ▸ h

/-- Passing a satisfied clause leaves the rest of the loop to decide. -/
theorem matrixFrom_succ {σ : QV A → QV A} {c c₂ : A} (hcc : QNextCl c c₂)
    (h : SatAll σ c) : matrixFrom σ c = matrixFrom σ c₂ := by
  classical
  rw [matrixFrom, matrixFrom]
  refine decide_eq_decide.mpr ⟨fun hall e he hle => hall e he (le_trans (le_of_lt hcc.2.2.1) hle),
    fun hall e he hle => ?_⟩
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · exact hall e he (hcc.2.2.2 e he hlt)


/-- The left marker has a neighbour: the right marker is above it. -/
theorem exists_afterStart (hwf : QsatWf A) :
    ∃ p : QV A, SuccPos (QLe (A := A)) QPosn posStart p := by
  refine TMData.exists_succPos' (M := qsatMachine A) (isLinOrd_qLe A hwf) qPosn_posStart
    fun hmax => ?_
  exact not_qLe_end_start (hmax.2 posEnd qPosn_posEnd)

/-- The right marker has a neighbour: the left marker is below it. -/
theorem exists_beforeEnd (hwf : QsatWf A) :
    ∃ p : QV A, SuccPos (QLe (A := A)) QPosn p posEnd := by
  refine exists_predPos (isLinOrd_qLe A hwf) qPosn_posEnd fun hmin => ?_
  exact not_qLe_end_start (hmin.2 posStart qPosn_posStart)

/-- **Where a turn lands**: one step in from the marker just reached, which is
where the next sweep – in the opposite direction – starts. -/
theorem turn_pos (hwf : QsatWf A) (d : Bool) :
    ∃ p' : QV A, QPosn p' ∧ TurnMove d (markerPos (A := A) d) p' ∧ SweepStart (!d) p' := by
  cases d
  · obtain ⟨p', hp'⟩ := exists_afterStart hwf
    exact ⟨p', hp'.2.1, Or.inl ⟨rfl, hp'⟩, hp'⟩
  · obtain ⟨p', hp'⟩ := exists_beforeEnd hwf
    exact ⟨p', hp'.1, Or.inr ⟨rfl, hp'⟩, hp'⟩

omit [Nonempty A] in
/-- **Every clause is the last one or has a successor.** -/
theorem qMaxCl_or_next {c : A} (hc : QCl c) : QMaxCl c ∨ ∃ c₂ : A, QNextCl c c₂ := by
  classical
  by_cases hmax : ∀ e : A, QCl e → e ≤ c
  · exact Or.inl ⟨hc, hmax⟩
  · have hex : ∃ e : A, QCl e ∧ c < e := by
      by_contra h
      exact hmax fun e he => not_lt.mp fun hlt => h ⟨e, he, hlt⟩
    obtain ⟨e₀, he₀, hlt⟩ := hex
    obtain ⟨c₂, ⟨hc₂, hlt₂⟩, hmin⟩ :=
      Set.exists_min_image {e : A | QCl e ∧ c < e} id (Set.toFinite _) ⟨e₀, he₀, hlt⟩
    exact Or.inr ⟨c₂, hc, hc₂, hlt₂, fun e he hce => hmin e ⟨he, hce⟩⟩

omit [Language.qsat.Structure A] in
theorem marker_tape {σ : QV A → QV A} (hS : σ posStart = symStart) (hE : σ posEnd = symEnd) :
    ∀ d : Bool, σ (markerPos d) = markerSym d := by
  intro d
  cases d
  · exact hS
  · exact hE

/-- **An unsatisfied clause ends the loop**: the matrix is false. -/
theorem turn_unsat (hwf : QsatWf A) (hok : TapeOk σ)
    (hM : ∀ d : Bool, σ (markerPos d) = markerSym d) {c : A} (hc : QCl c)
    (hunsat : ¬SatAll σ c) {d : Bool} {p : QV A} (hp : SweepStart d p) :
    ∃ q : QV A, QPosn q ∧ Relation.ReflTransGen (qsatMachine A).Step
      ⟨stEval false d c, p, σ⟩ ⟨stToEnd (matrixFrom σ c), q, σ⟩ := by
  classical
  obtain ⟨p', hq, hmove, -⟩ := turn_pos hwf d
  have hflag : satFlag σ c = false := by rw [satFlag]; exact decide_eq_false hunsat
  refine ⟨p', hq, (reach_pass hwf hok hc hp).tail ?_⟩
  rw [hflag, matrixFrom_eq_false hc hunsat]
  exact step_turnFalse hc (hM d) hmove

/-- **The last clause ends the loop**, whichever way it goes. -/
theorem turn_final (hwf : QsatWf A) (hok : TapeOk σ)
    (hM : ∀ d : Bool, σ (markerPos d) = markerSym d) {c : A} (hc : QCl c) (hmax : QMaxCl c)
    {d : Bool} {p : QV A} (hp : SweepStart d p) :
    ∃ q : QV A, QPosn q ∧ Relation.ReflTransGen (qsatMachine A).Step
      ⟨stEval false d c, p, σ⟩ ⟨stToEnd (matrixFrom σ c), q, σ⟩ := by
  classical
  by_cases hsat : SatAll σ c
  · obtain ⟨p', hq, hmove, -⟩ := turn_pos hwf d
    have hflag : satFlag σ c = true := by rw [satFlag]; exact decide_eq_true hsat
    refine ⟨p', hq, (reach_pass hwf hok hc hp).tail ?_⟩
    rw [hflag, matrixFrom_eq_true_of_max hmax hsat]
    exact step_turnLast hmax (hM d) hmove
  · exact turn_unsat hwf hok hM hc hsat hp

/-- **The clause loop.** Starting a sweep for the clause `c`, the machine
carries out one pass per clause from `c` on, alternating direction, and hands
the verdict to the carry phase. The recursion is on the number of clauses left
above `c`. -/
theorem reach_evalLoop (hwf : QsatWf A) (hok : TapeOk σ) (hS : σ posStart = symStart)
    (hE : σ posEnd = symEnd) :
    ∀ (n : ℕ) (c : A), {e : A | c < e}.ncard ≤ n → QCl c → ∀ (d : Bool) (p : QV A),
      SweepStart d p → ∃ q : QV A, QPosn q ∧ Relation.ReflTransGen (qsatMachine A).Step
        ⟨stEval false d c, p, σ⟩ ⟨stToEnd (matrixFrom σ c), q, σ⟩ := by
  classical
  have hM := marker_tape hS hE
  intro n
  induction n with
  | zero =>
    intro c hcard hc d p hp
    rcases qMaxCl_or_next hc with hmax | ⟨c₂, hcc⟩
    · exact turn_final hwf hok hM hc hmax hp
    · have hne : ({e : A | c < e}).Nonempty := ⟨c₂, hcc.2.2.1⟩
      have h1 := (Set.ncard_pos (Set.toFinite _)).mpr hne
      omega
  | succ n ih =>
    intro c hcard hc d p hp
    rcases qMaxCl_or_next hc with hmax | ⟨c₂, hcc⟩
    · exact turn_final hwf hok hM hc hmax hp
    · by_cases hsat : SatAll σ c
      · obtain ⟨p', -, hmove, hstart'⟩ := turn_pos hwf d
        have hflag : satFlag σ c = true := by rw [satFlag]; exact decide_eq_true hsat
        have hturn : (qsatMachine A).Step ⟨stEval (satFlag σ c) d c, markerPos d, σ⟩
            ⟨stEval false (!d) c₂, p', σ⟩ := by
          rw [hflag]
          exact step_turnNext hcc (hM d) hmove
        have hsub : {e : A | c₂ < e}.ncard ≤ n := by
          have hss : {e : A | c₂ < e} ⊂ {e : A | c < e} := by
            refine ⟨fun e he => lt_trans hcc.2.2.1 he, fun hsub => ?_⟩
            exact absurd (hsub hcc.2.2.1) (lt_irrefl c₂)
          have := Set.ncard_lt_ncard hss (Set.toFinite _)
          omega
        obtain ⟨q, hq, hrest⟩ := ih c₂ hsub hcc.2.1 (!d) p' hstart'
        refine ⟨q, hq, ((reach_pass hwf hok hc hp).tail hturn).trans ?_⟩
        rwa [matrixFrom_succ hcc hsat]
      · exact turn_unsat hwf hok hM hc hsat hp


/-! ### Carrying the verdict back -/

/-- **The carry phase** walks to the right marker and turns round, leaving the
machine returning the verdict at the innermost variable. -/
theorem reach_toEnd (hwf : QsatWf A) (hok : TapeOk σ) (hS : σ posStart = symStart)
    (hE : σ posEnd = symEnd) (v : Bool) {q : QV A} (hq : QPosn q) {p' : QV A}
    (hp' : SuccPos (QLe (A := A)) QPosn p' posEnd) :
    Relation.ReflTransGen (qsatMachine A).Step ⟨stToEnd v, q, σ⟩ ⟨stProc v, p', σ⟩ := by
  have hlin : IsLinOrd (qsatMachine A).Le := isLinOrd_qLe A hwf
  have hstep : ∀ p r : QV A, SuccPos (QLe (A := A)) QPosn p r → QLe q p → QLe r posEnd →
      (qsatMachine A).Step ⟨stToEnd v, p, σ⟩ ⟨stToEnd v, r, σ⟩ := by
    intro p r hs _ _
    rcases (qPosn_iff p).mp hs.1 with rfl | ⟨x, hx, rfl⟩ | rfl
    · exact step_toEndStart hS hs
    · obtain ⟨b, f, hbf⟩ := hok x hx
      exact step_toEndCell hx hbf hs
    · exact absurd (hlin.2.2.1 _ _ hs.2.2.1 ((maxPos_posEnd hwf).2 r hs.2.1)) hs.2.2.2.1
  have h := TMData.stepsIn_of_segment (M := qsatMachine A) hlin
    (conf := fun p => (⟨stToEnd v, p, σ⟩ : Config (QV A))) hq hstep posEnd qPosn_posEnd
    ((maxPos_posEnd hwf).2 q hq) (hlin.1 _)
  exact (TMData.reflTransGen_of_stepsIn h).tail (step_toEndTurn hE hp')

/-- **The whole evaluation phase**: from the right marker with the descent just
finished, the machine decides the matrix and comes back returning it at the
innermost variable. -/
theorem reach_matrix (hwf : QsatWf A) (hok : TapeOk σ) (hS : σ posStart = symStart)
    (hE : σ posEnd = symEnd) {p' : QV A} (hp' : SuccPos (QLe (A := A)) QPosn p' posEnd) :
    ∃ b : Bool, (b = true ↔ QsatMatrix (TapeTrue σ)) ∧
      Relation.ReflTransGen (qsatMachine A).Step ⟨stDesc, posEnd, σ⟩ ⟨stProc b, p', σ⟩ := by
  classical
  by_cases hcl : ∀ e : A, ¬QCl e
  · refine ⟨true, ⟨fun _ c hc => absurd hc (hcl c), fun _ => rfl⟩, ?_⟩
    exact Relation.ReflTransGen.single (step_descEndTrue hcl hE hp')
  · have hex : ∃ e : A, QCl e := by
      by_contra h
      exact hcl fun e he => h ⟨e, he⟩
    obtain ⟨c₀, hc₀, hmin⟩ := Set.exists_min_image {e : A | QCl e} id (Set.toFinite _) hex
    have hminc : QMinCl c₀ := ⟨hc₀, fun e he => hmin e he⟩
    obtain ⟨p₁, hp₁⟩ := exists_beforeEnd hwf
    obtain ⟨q, hq, hloop⟩ := reach_evalLoop hwf hok hS hE _ c₀ le_rfl hc₀ false p₁
      (show SweepStart false p₁ from hp₁)
    refine ⟨matrixFrom σ c₀, ?_, ?_⟩
    · rw [matrixFrom, decide_eq_true_iff]
      constructor
      · intro hall
        refine (qsatMatrix_iff hok).mpr fun c hc => ?_
        obtain ⟨x, b, f, hx, hσ, hlit⟩ := hall c hc (hminc.2 c hc)
        exact ⟨x, b, f, hx, hσ, hlit⟩
      · intro hm e he _
        obtain ⟨x, b, f, hx, hσ, hlit⟩ := (qsatMatrix_iff hok).mp hm e he
        exact ⟨x, b, f, hx, hσ, hlit⟩
    · exact (Relation.ReflTransGen.single (step_descEndEval hminc hE hp₁)).trans
        (hloop.trans (reach_toEnd hwf hok hS hE _ hq hp'))


/-! ### The position of the game, read off the tape

The dictionary for the *prefix*, as `DescriptiveComplexity.QsatTM.TapeTrue` was the
dictionary for the valuation: the head sitting at `p` means the game has
already quantified exactly the variables whose cells lie strictly below `p`. -/

/-- The variables the prefix binds strictly before the position `p`: the `D` of
the game position the machine is in when its head is at `p`. -/
def Before (p : QV A) (x : A) : Prop := IsQVar x ∧ QLe (posCell x) p ∧ posCell x ≠ p

/-- At the right marker every variable has been quantified, so the game is at a
leaf. -/
theorem before_posEnd (x : A) : Before (posEnd : QV A) x ↔ IsQVar x := by
  refine ⟨fun h => h.1, fun h => ⟨h, qLe_cell_end x, ?_⟩⟩
  exact fun he => QTag.noConfusion (congrArg Prod.fst he)

/-- **At a variable's cell, that variable is the one the prefix binds next.** -/
theorem qLeast_before (hwf : QsatWf A) {v : A} (hv : IsQVar v) :
    QLeast (Before (posCell v)) v := by
  refine ⟨hv, fun h => h.2.2 rfl, fun y hy hny hlt => hny ⟨hy, ?_, ?_⟩⟩
  · exact (qLe_posCell_iff hwf).mpr (Or.inl ⟨hy, hv, Or.inr hlt⟩)
  · exact fun he => hwf.irrefl v ((qOne_eq_qOne_iff.mp he).2 ▸ hlt)

/-- **Stepping the head past a variable's cell quantifies that variable.** -/
theorem before_succ (hwf : QsatWf A) {v : A} (hv : IsQVar v) {q : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn (posCell v) q) :
    Before q = qAdd (Before (posCell v)) v := by
  obtain ⟨-, htrans, hanti, htotal⟩ := isLinOrd_qLe A hwf
  funext x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases htotal (posCell v : QV A) (posCell x) with hle | hle
    · rcases hs.2.2.2.2 _ (qPosn_posCell h.1) hle h.2.1 with he | he
      · exact Or.inl (qOne_eq_qOne_iff.mp he).2
      · exact absurd he h.2.2
    · rcases eq_or_ne x v with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨h.1, hle, fun he => hne (qOne_eq_qOne_iff.mp he).2⟩
  · rcases h with rfl | ⟨hx, hle, hne⟩
    · exact ⟨hv, hs.2.2.1, hs.2.2.2.1⟩
    · refine ⟨hx, htrans _ _ _ hle hs.2.2.1, fun he => ?_⟩
      exact hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ hle))

omit [Language.qsat.Structure A] in
/-- **Writing a cell is updating the valuation.** -/
theorem tapeTrue_setCell (v : A) (b f : Bool) :
    TapeTrue (setCell σ v b f) = qUpd (TapeTrue σ) v b := by
  classical
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_ne y v with rfl | hne
    · exact Or.inl ⟨rfl, tapeTrue_setCell_self.mp h⟩
    · exact Or.inr ⟨hne, (tapeTrue_setCell_other hne).mp h⟩
  · rcases h with ⟨rfl, hb⟩ | ⟨hne, hy⟩
    · exact tapeTrue_setCell_self.mpr hb
    · exact (tapeTrue_setCell_other hne).mpr hy


/-! ### The two ways a level is decided

The `Proc` phase reads a returned value and either settles the level or tries
its second value. These are the two game-theoretic facts behind that, and they
are about `DescriptiveComplexity.QsatWins` alone – no machine. -/

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **A short circuit settles the level.** An existential level reached by a
winning branch is won; a universal level reached by a losing branch is lost. -/
theorem qsatWins_of_short (hwf : QsatWf A) {D τ : A → Prop} {w : A} (hw : QLeast D w)
    {b bw : Bool} (hbr : b = true ↔ QsatWins (qAdd D w) (qUpd τ w bw)) (hsh : QShort b w) :
    b = true ↔ QsatWins D τ := by
  rcases hsh with ⟨hall, hb⟩ | ⟨hall, hb⟩
  · rw [qsatWins_all_iff hwf hw hall, hb]
    refine ⟨fun h => absurd h (by decide), fun h => absurd (hbr.mpr (h bw)) (by rw [hb]; decide)⟩
  · rw [qsatWins_ex_iff hwf hw hall, hb]
    exact ⟨fun _ => ⟨bw, hbr.mp hb⟩, fun _ => rfl⟩

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **Without a short circuit the second branch settles the level.** -/
theorem qsatWins_of_second (hwf : QsatWf A) {D τ : A → Prop} {w : A} (hw : QLeast D w)
    {b₁ b₂ : Bool} (hns : ¬QShort b₁ w)
    (hb1 : b₁ = true ↔ QsatWins (qAdd D w) (qUpd τ w false))
    (hb2 : b₂ = true ↔ QsatWins (qAdd D w) (qUpd τ w true)) :
    b₂ = true ↔ QsatWins D τ := by
  by_cases hall : IsQAll w
  · have hb1t : b₁ = true := by
      rcases Bool.eq_false_or_eq_true b₁ with h | h
      · exact h
      · exact absurd (Or.inl ⟨hall, h⟩) hns
    rw [qsatWins_all_iff hwf hw hall]
    refine ⟨fun h b => ?_, fun h => hb2.mpr (h true)⟩
    cases b
    · exact hb1.mp hb1t
    · exact hb2.mp h
  · have hb1f : b₁ = false := by
      rcases Bool.eq_false_or_eq_true b₁ with h | h
      · exact absurd (Or.inr ⟨hall, h⟩) hns
      · exact h
    rw [qsatWins_ex_iff hwf hw hall]
    refine ⟨fun h => ⟨true, hb2.mp h⟩, fun ⟨b, hb⟩ => ?_⟩
    cases b
    · exact absurd (hb1.mpr hb) (by rw [hb1f]; decide)
    · exact hb2.mpr hb


/-! ### The game induction

The last step, and the one the whole file was preparing: the machine's descent
and return compute the value of the game position its head sits at.

Two nested recursions. The outer one is on the variables still to be quantified
at `p`; the inner one walks the `Proc` phase leftwards from the innermost
variable back to `p`. The inner walk calls the outer one exactly once, at a
switch, and on strictly fewer variables – which is what makes the pair well
founded. -/

/-- The variables the prefix has still to bind when the head is at `p`. -/
def RestCells (p : QV A) : Set A := {x : A | IsQVar x ∧ QLe p (posCell x)}

omit [Language.qsat.Structure A] in
/-- A cell holding its own value updates the valuation to itself. -/
theorem qUpd_tapeTrue {w : A} {bw f : Bool} (hσ : σ (posCell w) = symV bw f w) :
    qUpd (TapeTrue σ) w bw = TapeTrue σ := by
  funext y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨rfl, hb⟩ | ⟨-, hy⟩
    · exact (tapeTrue_iff hσ).mpr hb
    · exact hy
  · rcases eq_or_ne y w with rfl | hne
    · exact Or.inl ⟨rfl, (tapeTrue_iff hσ).mp h⟩
    · exact Or.inr ⟨hne, h⟩

/-- The game position at `p` only reads the cells strictly below `p`, so two
tapes agreeing there decide it alike. -/
theorem qsatWins_before_congr {p : QV A} {σ τ : QV A → QV A}
    (h : ∀ x : A, IsQVar x → QLe (posCell x) p → posCell x ≠ p →
      (TapeTrue σ x ↔ TapeTrue τ x)) :
    QsatWins (Before p) (TapeTrue σ) ↔ QsatWins (Before p) (TapeTrue τ) :=
  ⟨fun hw => qsatWins_congr hw _ fun y hy => h y hy.1 hy.2.1 hy.2.2,
    fun hw => qsatWins_congr hw _ fun y hy => (h y hy.1 hy.2.1 hy.2.2).symm⟩


/-- At the right marker the descent is over and the game is at a leaf. -/
theorem reach_game_posEnd (hwf : QsatWf A) (hok : TapeOk σ) (hS : σ posStart = symStart)
    (hE : σ posEnd = symEnd) {p' : QV A} (hp' : SuccPos (QLe (A := A)) QPosn p' posEnd) :
    ∃ b : Bool, (b = true ↔ QsatWins (Before (posEnd : QV A)) (TapeTrue σ)) ∧
      Relation.ReflTransGen (qsatMachine A).Step ⟨stDesc, posEnd, σ⟩ ⟨stProc b, p', σ⟩ := by
  obtain ⟨b, hb, hrun⟩ := reach_matrix hwf hok hS hE hp'
  exact ⟨b, hb.trans (qsatWins_leaf_iff (fun x hx => (before_posEnd x).mpr hx)).symm, hrun⟩

/-- The left marker has nothing below it. -/
theorem not_succPos_posStart (hwf : QsatWf A) {p' : QV A}
    (hp' : SuccPos (QLe (A := A)) QPosn p' posStart) : False :=
  hp'.2.2.2.1 ((isLinOrd_qLe A hwf).2.2.1 _ _ hp'.2.2.1 ((minPos_posStart hwf).2 p' hp'.1))


/-! ### The tape after a descent -/

theorem resetSeg_posEnd_cell {p₀ : QV A} {x : A} (hx : IsQVar x) (hle : QLe p₀ (posCell x)) :
    resetSeg σ p₀ posEnd (posCell x) = symV false false x := by
  rw [resetSeg, if_pos ⟨qPosn_posCell hx, rfl, hle, qLe_cell_end x,
    fun he => QTag.noConfusion (congrArg Prod.fst he)⟩]
  rfl

theorem resetSeg_of_not_le {p₀ p r : QV A} (h : ¬QLe p₀ r) : resetSeg σ p₀ p r = σ r :=
  resetSeg_of_not fun hh => h hh.2.2.1

theorem resetSeg_posStart {p₀ p : QV A} : resetSeg σ p₀ p posStart = σ posStart :=
  resetSeg_of_not fun h => QTag.noConfusion h.2.1

theorem resetSeg_posEnd {p₀ p : QV A} : resetSeg σ p₀ p posEnd = σ posEnd :=
  resetSeg_of_not fun h => QTag.noConfusion h.2.1

/-- The tape after a descent is laid out. -/
theorem tapeOk_resetSeg (hok : TapeOk σ) (p₀ p : QV A) :
    TapeOk (resetSeg σ p₀ p) := by
  classical
  intro x hx
  by_cases h : QPosn (posCell x : QV A) ∧ (posCell x : QV A).1 = QTag.pCell ∧
      QLe p₀ (posCell x) ∧ QLe (posCell x) p ∧ (posCell x : QV A) ≠ p
  · refine ⟨false, false, ?_⟩
    rw [resetSeg, if_pos h]
    rfl
  · obtain ⟨b, f, hbf⟩ := hok x hx
    exact ⟨b, f, (resetSeg_of_not h).trans hbf⟩


/-- Every variable's cell has a neighbour below it. -/
theorem exists_beforeCell (hwf : QsatWf A) {w : A} (hw : IsQVar w) :
    ∃ r : QV A, SuccPos (QLe (A := A)) QPosn r (posCell w) := by
  refine exists_predPos (isLinOrd_qLe A hwf) (qPosn_posCell hw) fun hmin => ?_
  exact not_qLe_cell_start w (hmin.2 posStart qPosn_posStart)

/-- A position between two variables' cells is a variable's cell. -/
theorem cell_of_between {v w : A} {r : QV A} (hr : QPosn r) (h1 : QLe (posCell v) r)
    (h2 : QLe r (posCell w)) : ∃ u : A, IsQVar u ∧ r = posCell u := by
  rcases (qPosn_iff r).mp hr with rfl | ⟨u, hu, rfl⟩ | rfl
  · exact absurd h1 (not_qLe_cell_start v)
  · exact ⟨u, hu, rfl⟩
  · exact absurd h2 (not_qLe_end_cell w)

/-- The cell of a variable at or after `p` is one of the variables `p` leaves
to be quantified. -/
theorem mem_restCells {p : QV A} {x : A} (hx : IsQVar x) (hle : QLe p (posCell x)) :
    x ∈ RestCells p := ⟨hx, hle⟩


/-- **The machine computes the game.** From the descent at `p` the machine
comes back, at the position just below `p`, returning the value of the game
position whose already-quantified variables are exactly those below `p`.

The outer recursion is on the variables still to be bound at `p`; the inner one
– `walk` – follows the return phase leftwards from the innermost variable back
to `p`, and calls the outer one once, at a switch, on strictly fewer
variables. -/
theorem reach_game (hwf : QsatWf A) :
    ∀ (n : ℕ) (p : QV A), QPosn p → (RestCells p).ncard ≤ n →
      ∀ ρ : QV A → QV A, TapeOk ρ → ρ posStart = symStart → ρ posEnd = symEnd →
      ∀ p' : QV A, SuccPos (QLe (A := A)) QPosn p' p →
      ∃ (b : Bool) (ρ' : QV A → QV A),
        TapeOk ρ' ∧ ρ' posStart = symStart ∧ ρ' posEnd = symEnd ∧
        (∀ x : A, IsQVar x → QLe (posCell x : QV A) p → (posCell x : QV A) ≠ p →
          ρ' (posCell x) = ρ (posCell x)) ∧
        (b = true ↔ QsatWins (Before p) (TapeTrue ρ)) ∧
        Relation.ReflTransGen (qsatMachine A).Step ⟨stDesc, p, ρ⟩ ⟨stProc b, p', ρ'⟩ := by
  classical
  obtain ⟨hrefl, htrans, hanti, htotal⟩ := isLinOrd_qLe A hwf
  intro n
  induction n with
  | zero =>
    intro p hp hcard ρ hok hS hE p' hp'
    rcases (qPosn_iff p).mp hp with rfl | ⟨v, hv, rfl⟩ | rfl
    · exact absurd hp' fun h => not_succPos_posStart hwf h
    · exact absurd hcard (by
        have h1 := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, mem_restCells hv (hrefl _)⟩
        omega)
    · obtain ⟨b, hb, hrun⟩ := reach_game_posEnd hwf hok hS hE hp'
      exact ⟨b, ρ, hok, hS, hE, fun _ _ _ _ => rfl, hb, hrun⟩
  | succ n ih =>
    intro p hp hcard ρ hok hS hE p' hp'
    rcases (qPosn_iff p).mp hp with rfl | ⟨v, hv, rfl⟩ | rfl
    · exact absurd hp' fun h => not_succPos_posStart hwf h
    swap
    · obtain ⟨b, hb, hrun⟩ := reach_game_posEnd hwf hok hS hE hp'
      exact ⟨b, ρ, hok, hS, hE, fun _ _ _ _ => rfl, hb, hrun⟩
    -- The main case: the head is at the cell of the variable `v`.
    have hcell : ∀ {u : A} {r : QV A}, QPosn r → QLe (posCell v : QV A) r →
        QLe r (posCell u) → ∃ y : A, IsQVar y ∧ r = posCell y :=
      fun hr h1 h2 => cell_of_between hr h1 h2
    have walk : ∀ (m : ℕ) (w : A), IsQVar w → QLe (posCell v : QV A) (posCell w) →
        {x : A | IsQVar x ∧ QLe (posCell v : QV A) (posCell x) ∧
          QLe (posCell x : QV A) (posCell w)}.ncard ≤ m →
        ∀ τ : QV A → QV A, TapeOk τ → τ posStart = symStart → τ posEnd = symEnd →
        (∀ x : A, IsQVar x → QLe (posCell v : QV A) (posCell x) →
          QLe (posCell x : QV A) (posCell w) → τ (posCell x) = symV false false x) →
        ∀ (b : Bool) (q₂ : QV A), SuccPos (QLe (A := A)) QPosn (posCell w) q₂ →
        (b = true ↔ QsatWins (Before q₂) (TapeTrue τ)) →
        ∃ (b' : Bool) (τ' : QV A → QV A), TapeOk τ' ∧ τ' posStart = symStart ∧
          τ' posEnd = symEnd ∧
          (∀ x : A, IsQVar x → QLe (posCell x : QV A) (posCell v) →
            (posCell x : QV A) ≠ posCell v → τ' (posCell x) = τ (posCell x)) ∧
          (b' = true ↔ QsatWins (Before (posCell v : QV A)) (TapeTrue τ)) ∧
          Relation.ReflTransGen (qsatMachine A).Step ⟨stProc b, posCell w, τ⟩
            ⟨stProc b', p', τ'⟩ := by
      intro m
      induction m with
      | zero =>
        intro w hw hvw hcard' τ _ _ _ _ b q₂ _ _
        exfalso
        have hmem : w ∈ {x : A | IsQVar x ∧ QLe (posCell v : QV A) (posCell x) ∧
            QLe (posCell x : QV A) (posCell w)} := ⟨hw, hvw, hrefl _⟩
        have h1 := (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hmem⟩
        omega
      | succ m ihm =>
        intro w hw hvw hcard' τ hokτ hSτ hEτ hcells b q₂ hs hb
        have hτw : τ (posCell w) = symV false false w := hcells w hw hvw (hrefl _)
        have hleast : QLeast (Before (posCell w : QV A)) w := qLeast_before hwf hw
        have hBq₂ : Before q₂ = qAdd (Before (posCell w : QV A)) w := before_succ hwf hw hs
        -- the finishing move, shared by the two branches
        have finish : ∀ (bb bw f : Bool) (τ' : QV A → QV A), TapeOk τ' →
            τ' posStart = symStart → τ' posEnd = symEnd →
            (∀ x : A, IsQVar x → QLe (posCell x : QV A) (posCell w) →
              (posCell x : QV A) ≠ posCell w → τ' (posCell x) = τ (posCell x)) →
            τ' (posCell w) = symV bw f w → (QShort bb w ∨ f = true) →
            (bb = true ↔ QsatWins (Before (posCell w : QV A)) (TapeTrue τ')) →
            ∃ (b' : Bool) (τ'' : QV A → QV A), TapeOk τ'' ∧ τ'' posStart = symStart ∧
              τ'' posEnd = symEnd ∧
              (∀ x : A, IsQVar x → QLe (posCell x : QV A) (posCell v) →
                (posCell x : QV A) ≠ posCell v → τ'' (posCell x) = τ (posCell x)) ∧
              (b' = true ↔ QsatWins (Before (posCell v : QV A)) (TapeTrue τ)) ∧
              Relation.ReflTransGen (qsatMachine A).Step ⟨stProc bb, posCell w, τ'⟩
                ⟨stProc b', p', τ''⟩ := by
          intro bb bw f τ' hokτ' hSτ' hEτ' hagree hτ'w hdec hlev
          have hTT : ∀ x : A, IsQVar x → QLe (posCell x : QV A) (posCell w) →
              (posCell x : QV A) ≠ posCell w → (TapeTrue τ' x ↔ TapeTrue τ x) := by
            intro x hx h1 h2
            simp only [TapeTrue, hagree x hx h1 h2]
          rcases eq_or_ne w v with rfl | hne
          · refine ⟨bb, τ', hokτ', hSτ', hEτ', hagree, ?_,
              Relation.ReflTransGen.single (step_procSkip hw hdec hτ'w hp')⟩
            exact hlev.trans (qsatWins_before_congr hTT)
          · obtain ⟨pr, hpr⟩ := exists_beforeCell hwf hw
            have hvpr : QLe (posCell v : QV A) pr := by
              rcases htotal (posCell v : QV A) pr with h | h
              · exact h
              · rcases hpr.2.2.2.2 _ (qPosn_posCell hv) h hvw with he | he
                · exact he ▸ hrefl _
                · exact absurd ((qOne_eq_qOne_iff.mp he).2) fun hh => hne hh.symm
            obtain ⟨u, hu, rfl⟩ := hcell hpr.1 hvpr hpr.2.2.1
            have hagree' : ∀ x : A, IsQVar x → QLe (posCell v : QV A) (posCell x) →
                QLe (posCell x : QV A) (posCell u) → τ' (posCell x) = symV false false x := by
              intro x hx h1 h2
              have h3 : QLe (posCell x : QV A) (posCell w) := htrans _ _ _ h2 hpr.2.2.1
              have h4 : (posCell x : QV A) ≠ posCell w := fun he =>
                hpr.2.2.2.1 (hanti _ _ hpr.2.2.1 (he ▸ h2))
              exact (hagree x hx h3 h4).trans (hcells x hx h1 h3)
            have hmes : {x : A | IsQVar x ∧ QLe (posCell v : QV A) (posCell x) ∧
                QLe (posCell x : QV A) (posCell u)}.ncard ≤ m := by
              have hss : {x : A | IsQVar x ∧ QLe (posCell v : QV A) (posCell x) ∧
                  QLe (posCell x : QV A) (posCell u)} ⊂
                {x : A | IsQVar x ∧ QLe (posCell v : QV A) (posCell x) ∧
                  QLe (posCell x : QV A) (posCell w)} := by
                refine ⟨fun x hx => ⟨hx.1, hx.2.1, htrans _ _ _ hx.2.2 hpr.2.2.1⟩, fun hsub => ?_⟩
                have := hsub ⟨hw, hvw, hrefl _⟩
                exact hpr.2.2.2.1 (hanti _ _ hpr.2.2.1 this.2.2)
              have := Set.ncard_lt_ncard hss (Set.toFinite _)
              omega
            obtain ⟨b', τ'', hok'', hS'', hE'', hag'', hval'', hrun''⟩ :=
              ihm u hu hvpr hmes τ' hokτ' hSτ' hEτ' hagree' bb (posCell w) hpr hlev
            refine ⟨b', τ'', hok'', hS'', hE'', ?_, ?_, ?_⟩
            · intro x hx h1 h2
              refine (hag'' x hx h1 h2).trans (hagree x hx ?_ ?_)
              · exact htrans _ _ _ h1 hvw
              · exact fun he => h2 (hanti _ _ h1 (he ▸ hvw))
            · exact hval''.trans (qsatWins_before_congr fun x hx h1 h2 =>
                hTT x hx (htrans _ _ _ h1 hvw) fun he => h2 (hanti _ _ h1 (he ▸ hvw)))
            · exact (Relation.ReflTransGen.single
                (step_procSkip hw hdec hτ'w hpr)).trans hrun''
        -- the two branches
        have hbr : b = true ↔ QsatWins (qAdd (Before (posCell w : QV A)) w)
            (qUpd (TapeTrue τ) w false) := by
          rw [qUpd_tapeTrue hτw, ← hBq₂]
          exact hb
        by_cases hsh : QShort b w
        · exact finish b false false τ hokτ hSτ hEτ (fun _ _ _ _ => rfl) hτw (Or.inl hsh)
            (qsatWins_of_short hwf hleast hbr hsh)
        · -- switch: write the second value and descend again
          set τ₁ := setCell τ w true true with hτ₁
          have hokτ₁ : TapeOk τ₁ := tapeOk_setCell hokτ w true true
          have hne₁ : ∀ r : QV A, r ≠ posCell w → τ₁ r = τ r := setCell_frame w true true
          have hSτ₁ : τ₁ posStart = symStart :=
            (hne₁ _ fun he => QTag.noConfusion (congrArg Prod.fst he)).trans hSτ
          have hEτ₁ : τ₁ posEnd = symEnd :=
            (hne₁ _ fun he => QTag.noConfusion (congrArg Prod.fst he)).trans hEτ
          have hmes₂ : (RestCells q₂).ncard ≤ n := by
            have hss : RestCells q₂ ⊂ RestCells (posCell v : QV A) := by
              refine ⟨fun x hx => ⟨hx.1, htrans _ _ _ hvw (htrans _ _ _ hs.2.2.1 hx.2)⟩,
                fun hsub => ?_⟩
              have := hsub (mem_restCells hw hvw)
              exact hs.2.2.2.1 (hanti _ _ hs.2.2.1 this.2)
            have := Set.ncard_lt_ncard hss (Set.toFinite _)
            omega
          obtain ⟨b₂, τ₂, hokτ₂, hSτ₂, hEτ₂, hagτ₂, hvalτ₂, hrunτ₂⟩ :=
            ih q₂ hs.2.1 hmes₂ τ₁ hokτ₁ hSτ₁ hEτ₁ (posCell w) hs
          have hτ₂w : τ₂ (posCell w) = symV true true w := by
            refine (hagτ₂ w hw hs.2.2.1 hs.2.2.2.1).trans ?_
            exact setCell_self w true true
          have hTT₂ : ∀ x : A, IsQVar x → QLe (posCell x : QV A) (posCell w) →
              (posCell x : QV A) ≠ posCell w → (TapeTrue τ₂ x ↔ TapeTrue τ x) := by
            intro x hx h1 h2
            have hxw : x ≠ w := fun he => h2 (congrArg _ he)
            rw [TapeTrue, TapeTrue,
              (hagτ₂ x hx (htrans _ _ _ h1 hs.2.2.1) fun he =>
                hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ h1))).trans (setCell_other hxw)]
          have hb2 : b₂ = true ↔ QsatWins (qAdd (Before (posCell w : QV A)) w)
              (qUpd (TapeTrue τ₂) w true) := by
            rw [qUpd_tapeTrue hτ₂w, ← hBq₂]
            refine hvalτ₂.trans ⟨fun hh => qsatWins_congr hh _ ?_, fun hh => qsatWins_congr hh _ ?_⟩
            · intro y hy
              rw [hBq₂] at hy
              rcases hy with rfl | hy
              · rw [tapeTrue_iff (setCell_self y true true), tapeTrue_iff hτ₂w]
              · have hyw : y ≠ w := fun he => hy.2.2 (congrArg _ he)
                exact (tapeTrue_setCell_other hyw).trans (hTT₂ y hy.1 hy.2.1 hy.2.2).symm
            · intro y hy
              rw [hBq₂] at hy
              rcases hy with rfl | hy
              · rw [tapeTrue_iff (setCell_self y true true), tapeTrue_iff hτ₂w]
              · have hyw : y ≠ w := fun he => hy.2.2 (congrArg _ he)
                exact (hTT₂ y hy.1 hy.2.1 hy.2.2).trans (tapeTrue_setCell_other hyw).symm
          have hb1 : b = true ↔ QsatWins (qAdd (Before (posCell w : QV A)) w)
              (qUpd (TapeTrue τ₂) w false) := by
            refine hbr.trans ⟨fun hh => qsatWins_congr hh _ ?_, fun hh => qsatWins_congr hh _ ?_⟩
            · intro y hy
              rcases hy with rfl | hy
              · rw [qUpd_self, qUpd_self]
              · have hyw : y ≠ w := fun he => hy.2.2 (congrArg _ he)
                rw [qUpd_ne _ false hyw, qUpd_ne _ false hyw]
                exact (hTT₂ y hy.1 hy.2.1 hy.2.2).symm
            · intro y hy
              rcases hy with rfl | hy
              · rw [qUpd_self, qUpd_self]
              · have hyw : y ≠ w := fun he => hy.2.2 (congrArg _ he)
                rw [qUpd_ne _ false hyw, qUpd_ne _ false hyw]
                exact hTT₂ y hy.1 hy.2.1 hy.2.2
          have hlev₂ := qsatWins_of_second hwf hleast hsh hb1 hb2
          have hrun₁ : Relation.ReflTransGen (qsatMachine A).Step
              ⟨stProc b, posCell w, τ⟩ ⟨stProc b₂, posCell w, τ₂⟩ :=
            (Relation.ReflTransGen.single (step_procSwitch hw hsh hτw
              (setCell_self w true true) (setCell_frame w true true) hs)).trans hrunτ₂
          obtain ⟨b', τ'', h1, h2, h3, h4, h5, h6⟩ :=
            finish b₂ true true τ₂ hokτ₂ hSτ₂ hEτ₂
              (fun x hx ha hbne => (hagτ₂ x hx (htrans _ _ _ ha hs.2.2.1) fun he =>
                  hs.2.2.2.1 (hanti _ _ hs.2.2.1 (he ▸ ha))).trans
                (setCell_other fun he => hbne (congrArg _ he)))
              hτ₂w (Or.inr rfl) hlev₂
          exact ⟨b', τ'', h1, h2, h3, h4, h5, hrun₁.trans h6⟩
    -- assemble: descend, evaluate, then walk back
    set ρ₀ := resetSeg ρ (posCell v : QV A) posEnd with hρ₀
    have hokρ₀ : TapeOk ρ₀ := tapeOk_resetSeg hok _ _
    have hSρ₀ : ρ₀ posStart = symStart := resetSeg_posStart.trans hS
    have hEρ₀ : ρ₀ posEnd = symEnd := resetSeg_posEnd.trans hE
    obtain ⟨p₁, hp₁⟩ := exists_beforeEnd hwf
    have hvp₁ : QLe (posCell v : QV A) p₁ := by
      rcases htotal (posCell v : QV A) p₁ with h | h
      · exact h
      · rcases hp₁.2.2.2.2 _ (qPosn_posCell hv) h (qLe_cell_end v) with he | he
        · exact he ▸ hrefl _
        · exact absurd he fun hh => QTag.noConfusion (congrArg Prod.fst hh)
    rcases (qPosn_iff p₁).mp hp₁.1 with rfl | ⟨w₁, hw₁, rfl⟩ | rfl
    · exact absurd hvp₁ (not_qLe_cell_start v)
    swap
    · exact absurd rfl hp₁.2.2.2.1
    obtain ⟨b₀, hb₀, hrun₀⟩ := reach_game_posEnd hwf hokρ₀ hSρ₀ hEρ₀ hp₁
    obtain ⟨b', τ', h1, h2, h3, h4, h5, h6⟩ :=
      walk _ w₁ hw₁ hvp₁ le_rfl ρ₀ hokρ₀ hSρ₀ hEρ₀
        (fun x hx ha _ => resetSeg_posEnd_cell hx ha) b₀ posEnd hp₁ hb₀
    refine ⟨b', τ', h1, h2, h3, ?_, ?_, ?_⟩
    · intro x hx ha hbne
      refine (h4 x hx ha hbne).trans (resetSeg_of_not_le fun hle => hbne (hanti _ _ ha hle))
    · refine h5.trans (qsatWins_before_congr fun x hx ha hbne => ?_)
      have hEq : ρ₀ (posCell x) = ρ (posCell x) :=
        resetSeg_of_not_le fun hle => hbne (hanti _ _ ha hle)
      simp only [TapeTrue, hEq]
    · exact ((reach_descent hwf hok hS (qPosn_posCell hv)).trans hrun₀).trans h6

/-! ### The tape the machine starts on -/

/-- The initial tape is laid out. -/
theorem tapeOk_initTape : TapeOk (initTape : QV A → QV A) :=
  fun _ _ => ⟨false, false, rfl⟩

omit [Language.qsat.Structure A] in
/-- **The initial tape makes every variable false.** -/
theorem not_tapeTrue_initTape (x : A) : ¬TapeTrue (initTape : QV A → QV A) x :=
  fun h => Bool.false_ne_true ((tapeTrue_iff (b := false) (f := false) rfl).mp h)


/-! ### The machine decides QSAT -/

/-- **The machine is well formed** on a well-formed instance. -/
theorem qsatMachine_wellFormed (hwf : QsatWf A) : (qsatMachine A).WellFormed :=
  ⟨isLinOrd_qLe A hwf, exists_qPosn, fun _ _ _ ha hb => qInp_functional ha hb,
    exists_qBlank, fun _ _ ha hb => qBlank_unique ha hb⟩

/-- Nothing is quantified when the head has only just left the left marker. -/
theorem before_afterStart {p₀ : QV A}
    (hs : SuccPos (QLe (A := A)) QPosn posStart p₀) : Before p₀ = fun _ : A => False := by
  funext x
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  rcases hs.2.2.2.2 _ (qPosn_posCell h.1) (qLe_start_cell x) h.2.1 with he | he
  · exact QTag.noConfusion (congrArg Prod.fst he)
  · exact h.2.2 he

/-- **The machine accepts exactly the true formulas.** -/
theorem qsatMachine_acceptsSpace_iff (hwf : QsatWf A) :
    (qsatMachine A).AcceptsSpace ↔ QsatWins (fun _ : A => False) (fun _ : A => False) := by
  obtain ⟨p₀, hp₀⟩ := exists_afterStart hwf
  obtain ⟨b, σ', hok', hS', hE', -, hval, hrun⟩ :=
    reach_game hwf _ p₀ hp₀.2.1 le_rfl initTape tapeOk_initTape rfl rfl posStart hp₀
  have hTT : TapeTrue (initTape : QV A → QV A) = fun _ : A => False := by
    funext x
    exact propext ⟨fun h => absurd h (not_tapeTrue_initTape x), fun h => h.elim⟩
  rw [before_afterStart hp₀, hTT] at hval
  have hstart : Relation.ReflTransGen (qsatMachine A).Step
      ⟨stDesc, posStart, (initTape : QV A → QV A)⟩ ⟨stProc b, posStart, σ'⟩ :=
    (Relation.ReflTransGen.single (step_descStart rfl hp₀)).trans hrun
  constructor
  · intro hacc
    by_contra hno
    have hbf : b = false := by
      rcases Bool.eq_false_or_eq_true b with h | h
      · exact absurd (hval.mp h) hno
      · exact h
    subst hbf
    refine TMData.not_acceptsSpace_of_reaches_dead (qsatMachine_wellFormed hwf)
      qsatMachine_deterministic (isInit_start hwf) hstart (fun _ => not_step_procFalse hS')
      not_acc_stProcFalse (fun e he _ => not_step_of_acc he) hacc
  · intro hw
    have hbt : b = true := hval.mpr hw
    subst hbt
    exact TMData.acceptsSpace_of_reaches_acc (isInit_start hwf)
      (hstart.tail (step_procAcc hS' hp₀)) (acc_stAcc hwf)

/-- **The machine of a QSAT instance decides it.** A malformed instance has no
accepting state, so it is a no-instance on both sides. -/
theorem qsatMachine_correct :
    ((qsatMachine A).WellFormed ∧ (qsatMachine A).Deterministic ∧
      (qsatMachine A).AcceptsSpace) ↔ QsatHolds A := by
  constructor
  · rintro ⟨hwfm, -, hacc⟩
    obtain ⟨-, c, -, -, haccst⟩ := id hacc
    exact ⟨haccst.1, (qsatMachine_acceptsSpace_iff haccst.1).mp hacc⟩
  · rintro ⟨hwf, hw⟩
    exact ⟨qsatMachine_wellFormed hwf, qsatMachine_deterministic,
      (qsatMachine_acceptsSpace_iff hwf).mpr hw⟩


end Run

end QsatTM

end DescriptiveComplexity
