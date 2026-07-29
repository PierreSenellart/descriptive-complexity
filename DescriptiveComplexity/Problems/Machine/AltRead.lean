/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltCheck

/-!
# Reading a block's assignment off an arbitrary run

The direction a universal round needs. `DescriptiveComplexity.steps_sweep`
exhibits *the* run of a sweep against a given assignment; a universal player
must be answered for **every** play of its block, so the converse is needed:
whatever the machine does during sweep `i`, it is the intended run of *some*
assignment of block `i`.

The invariant is `DescriptiveComplexity.InSweepR`: at every moment of the
rightward pass the tape is `tapeAfter (Function.update νs i ν') (i+1)` for the
`ν'` the sweep has written *so far*, which is supported strictly below the
head. Cells at or above the head are therefore untouched – `ν'` is false there,
and `DescriptiveComplexity.valAfter_update_succ` collapses the disjunction back
to the old value – so one statement covers the whole pass rather than needing a
separate “below the head” clause.

The only two transitions that can fire at a cell are `tGKeep`, which changes
nothing, and `tGSet`, which adds the cell's variable to `ν'`. That the machine
has no other choice is `DescriptiveComplexity.altTr_unique`.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Readoff

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Comparing tapes -/

variable {νs : Fin k → A → Prop}

/-- Two tapes agree at a tuple as soon as they give its variable the same
value. -/
theorem tapeAfter_congr_at {ρ σ : Fin k → A → Prop} {m m' : ℕ} {r : AltV k A}
    (h : valAfter ρ m (r.2 0) = valAfter σ m' (r.2 0)) : tapeAfter ρ m r = tapeAfter σ m' r := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := r
  cases t <;> simp only [tapeAfter, h]

/-! ### The invariant of a rightward pass -/

/-- **What is true at every moment of the rightward pass of sweep `i`.** The
witness `ν'` is what the sweep has written so far: a set of variables block `i`
marks, all of them strictly below the head. The head itself lies between the
first cell and the right marker, which is what says that the machine still has
a move: above the right marker the tape is blank, and no transition reads a
blank. -/
def InSweepR (i : Fin k) (νs : Fin k → A → Prop) (c : Config (AltV k A)) : Prop :=
  ∃ ν' : A → Prop,
    (∀ x : A, ν' x → QbfBlk i x ∧ tagTupleLe (posCell x : AltV k A) c.head ∧
      (posCell x : AltV k A) ≠ c.head) ∧
    c.state = stG i.castSucc true ∧ AltPosn c.head ∧
    tagTupleLe (posCell qbotA : AltV k A) c.head ∧ tagTupleLe c.head (posEnd : AltV k A) ∧
    c.tape = tapeAfter (Function.update νs i ν') ((i : ℕ) + 1)

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Writing nothing in block `i` leaves the tape where the sweeps below it left
it. -/
theorem valAfter_update_bot {i : Fin k} {x : A} :
    valAfter (Function.update νs i fun _ => False) ((i : ℕ) + 1) x = valAfter νs (i : ℕ) x := by
  refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
  · rcases valAfter_update_succ.mp h with h' | ⟨-, h'⟩
    · exact h'
    · exact h'.elim
  · exact valAfter_update_succ.mpr (Or.inl h)

/-- **The pass starts with nothing written.** -/
theorem inSweepR_start (i : Fin k) (νs : Fin k → A → Prop) :
    InSweepR i νs (confSweep νs i.castSucc (posCell qbotA)) := by
  classical
  refine ⟨fun _ => False, fun x hx => hx.elim, rfl, altPosn_posCell _,
    altTagTupleLe_refl _, posCell_le_posEnd _, ?_⟩
  refine (tape_confSweep_bot νs i.castSucc).trans (funext fun r => ?_)
  exact (tapeAfter_congr_at valAfter_update_bot.symm)

/-! ### What the tape says about the head -/

/-- The four kinds of symbol a position can hold. -/
theorem tapeAfter_head_cases {m : ℕ} {ρ : Fin k → A → Prop} {r : AltV k A} (hr : AltPosn r) :
    (r.1.1 = AltBase.pStart ∧ tapeAfter ρ m r = symStart) ∨
      (r.1.1 = AltBase.pEnd ∧ tapeAfter ρ m r = symEnd) ∨
      (r.1.1 = AltBase.pCell ∧ tapeAfter ρ m r = symV (valAfter ρ m (r.2 0)) (r.2 0)) ∨
      tapeAfter ρ m r = symBlank := by
  obtain ⟨⟨t, j⟩, w⟩ := r
  cases t <;>
    first
      | exact hr.elim
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, tapeAfter_at_cell hr rfl⟩))
      | exact Or.inr (Or.inr (Or.inr rfl))

/-- Reading the left marker pins the head. -/
theorem head_eq_posStart {m : ℕ} {ρ : Fin k → A → Prop} {r : AltV k A} (hr : AltPosn r)
    (h : tapeAfter ρ m r = symStart) : r = posStart := by
  rcases tapeAfter_head_cases (m := m) (ρ := ρ) hr with ⟨hb, -⟩ | ⟨-, he⟩ | ⟨-, he⟩ | he
  · exact eq_posStart_of_posn hr hb
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI])
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI, aoneI])
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI])

/-- Reading the right marker pins the head. -/
theorem head_eq_posEnd {m : ℕ} {ρ : Fin k → A → Prop} {r : AltV k A} (hr : AltPosn r)
    (h : tapeAfter ρ m r = symEnd) : r = posEnd := by
  rcases tapeAfter_head_cases (m := m) (ρ := ρ) hr with ⟨-, he⟩ | ⟨hb, -⟩ | ⟨-, he⟩ | he
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI])
  · exact eq_posEnd_of_posn hr hb
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI, aoneI])
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI])

/-- Reading a cell's symbol pins the head to that cell. -/
theorem head_eq_posCell {m : ℕ} {ρ : Fin k → A → Prop} {r : AltV k A} {b : Bool} {x : A}
    (hr : AltPosn r) (h : tapeAfter ρ m r = symV b x) :
    r = posCell x ∧ b = valAfter ρ m x := by
  rcases tapeAfter_head_cases (m := m) (ρ := ρ) hr with ⟨-, he⟩ | ⟨-, he⟩ | ⟨hb, he⟩ | he
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI, aoneI])
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI, aoneI])
  · have hx := aoneI_eq_iff.mp (he.symm.trans h)
    refine ⟨?_, ?_⟩
    · rw [eq_posCell_of_posn hr hb, hx.2.2]
    · have hb' : AltBase.sVal (valAfter ρ m (r.2 0)) = AltBase.sVal b := hx.1
      have : valAfter ρ m (r.2 0) = b := by
        simpa only [AltBase.sVal.injEq] using hb'
      rw [← this, hx.2.2]
  · exact absurd (congrArg (fun p => p.1.1) (he.symm.trans h)) (by simp [acstI, aoneI])

/-! ### Writing one cell -/

omit [(Language.qbf k).Structure A] [Finite A] [Nonempty A] in
/-- A tuple with a cell's tag and a cell's shape is a position. -/
theorem altPosn_of_isCellTup {r : AltV k A} (hb : r.1.1 = AltBase.pCell) (h : IsCellTup r) :
    AltPosn r := by
  obtain ⟨⟨t, j⟩, w⟩ := r
  simp only at hb
  subst hb
  exact h

/-- Two tapes agree at a tuple as soon as they agree at it *when it is a real
cell*: a junk cell reads `false` on either. -/
theorem tapeAfter_congr_off {ρ σ : Fin k → A → Prop} {m m' : ℕ} {r : AltV k A}
    (h : r.1.1 = AltBase.pCell → IsCellTup r →
      valAfter ρ m (r.2 0) = valAfter σ m' (r.2 0)) :
    tapeAfter ρ m r = tapeAfter σ m' r := by
  classical
  obtain ⟨⟨t, j⟩, w⟩ := r
  cases t <;> simp only [tapeAfter]
  by_cases hcell : IsCellTup (((AltBase.pCell, j), w) : AltV k A)
  · rw [if_pos hcell, if_pos hcell, h rfl hcell]
  · rw [if_neg hcell, if_neg hcell]

/-- **Setting one cell adds one variable to the block's assignment.** This is
the only computation the read-off of a sweep performs: the cell of `x` turns
from `false` to `true`, and every other tuple is left alone – a real cell
because its variable is not `x`, a junk one because it reads `false`
regardless. -/
theorem tapeAfter_set {i : Fin k} {ν' : A → Prop} {x : A} {T T' : AltV k A → AltV k A}
    (hblk : QbfBlk i x) (hT : T = tapeAfter (Function.update νs i ν') ((i : ℕ) + 1))
    (hx : T' (posCell x) = symV true x)
    (hframe : ∀ r, r ≠ (posCell x : AltV k A) → T' r = T r) :
    T' = tapeAfter (Function.update νs i fun y => ν' y ∨ y = x) ((i : ℕ) + 1) := by
  classical
  funext r
  rcases eq_or_ne r (posCell x : AltV k A) with rfl | hne
  · rw [hx, tapeAfter_posCell]
    congr 1
    exact (valAfter_update_succ.mpr (Or.inr ⟨hblk, Or.inr rfl⟩)).symm
  · rw [hframe r hne, hT]
    refine tapeAfter_congr_off fun hb hcell => ?_
    have hrx : r.2 0 ≠ x := by
      intro hcon
      exact hne (by rw [eq_posCell_of_posn (altPosn_of_isCellTup hb hcell) hb, hcon])
    refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases valAfter_update_succ.mp h with h' | ⟨hb', hν⟩
      · exact valAfter_update_succ.mpr (Or.inl h')
      · exact valAfter_update_succ.mpr (Or.inr ⟨hb', Or.inl hν⟩)
    · rcases valAfter_update_succ.mp h with h' | ⟨hb', hν⟩
      · exact valAfter_update_succ.mpr (Or.inl h')
      · rcases hν with hν | hν
        · exact valAfter_update_succ.mpr (Or.inr ⟨hb', hν⟩)
        · exact absurd hν hrx

/-! ### One step of the pass -/

/-- **What is true at every moment of the leftward pass**: the sweep is over,
the tape holds what it wrote, and the head is on its way back down from the
last cell. -/
def InSweepL (i : Fin k) (νs : Fin k → A → Prop) (c : Config (AltV k A)) : Prop :=
  ∃ ν' : A → Prop, (∀ x : A, ν' x → QbfBlk i x) ∧
    c.state = stG i.castSucc false ∧ AltPosn c.head ∧
    tagTupleLe c.head (posCell (qtopA (A := A)) : AltV k A) ∧
    c.tape = tapeAfter (Function.update νs i ν') ((i : ℕ) + 1)

omit [(Language.qbf k).Structure A] [Finite A] [Nonempty A] in
/-- Moving the head up keeps everything already written below it. -/
theorem supp_step {p q r : AltV k A} (hsucc : SuccPos tagTupleLe AltPosn p q)
    (hle : tagTupleLe r p) : tagTupleLe r q ∧ r ≠ q := by
  refine ⟨isLinOrd_altTagTupleLe.2.1 r p q hle hsucc.2.2.1, ?_⟩
  rintro rfl
  exact hsucc.2.2.2.1 (isLinOrd_altTagTupleLe.2.2.1 p r hsucc.2.2.1 hle)

omit [(Language.qbf k).Structure A] [Nonempty A] in
/-- A step up raises the rank. -/
theorem bitRank_lt_of_succPos {p q : AltV k A} (h : SuccPos tagTupleLe AltPosn p q) :
    bitRank tagTupleLe AltPosn p < bitRank tagTupleLe AltPosn q :=
  bitRank_lt isLinOrd_altTagTupleLe h.1 h.2.2.1 h.2.2.2.1

omit [(Language.qbf k).Structure A] in
/-- A cell is not the right marker. -/
theorem posCell_ne_posEnd (x : A) : (posCell x : AltV k A) ≠ posEnd := fun h =>
  absurd (congrArg (fun p => p.1.1) h) (show ¬(AltBase.pCell = AltBase.pEnd) by decide)

omit [(Language.qbf k).Structure A] in
/-- **The head cannot step over the right marker.** Anything strictly below it
has its successor at or below it, since a successor admits nothing strictly
between. -/
theorem le_posEnd_of_succPos {p q : AltV k A} (hsucc : SuccPos tagTupleLe AltPosn p q)
    (hle : tagTupleLe p (posEnd : AltV k A)) (hne : p ≠ posEnd) :
    tagTupleLe q (posEnd : AltV k A) := by
  by_contra hcon
  have hge : tagTupleLe (posEnd : AltV k A) q :=
    (isLinOrd_altTagTupleLe.2.2.2 q posEnd).resolve_left hcon
  rcases hsucc.2.2.2.2 posEnd altPosn_posEnd hle hge with h | h
  · exact hne h.symm
  · exact absurd (h ▸ altTagTupleLe_refl (posEnd : AltV k A)) hcon

/-- **One step of the rightward pass, whatever the machine chooses.** Only
three transitions can fire once the pass has left the left marker: the turn at
the right one changes nothing, `tGKeep` leaves the cell alone, and `tGSet` adds
its variable to what the block has assigned. The head moves up until the turn,
which is what makes the pass terminate. -/
theorem inSweepR_step {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c c' : Config (AltV k A)} (hinv : InSweepR i νs c)
    (hstep : (altMachine k A cnf).Step c c') :
    (InSweepR i νs c' ∧
        bitRank tagTupleLe AltPosn c.head < bitRank tagTupleLe AltPosn c'.head) ∨
      InSweepL i νs c' := by
  classical
  obtain ⟨ν', hsupp, hst, hpos, hlo, hhi, htape⟩ := hinv
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have hTr : AltTr cnf τ := hτ
  have hSrc : AltSrc cnf τ c.state := hsrc
  have hRead : AltRead τ (c.tape c.head) := hread
  have hDst : AltDst cnf τ c'.state := hdst
  have hWrite : AltWrite τ (c'.tape c.head) := hwrite
  have hMove : (AltRight τ ∧ SuccPos tagTupleLe AltPosn c.head c'.head) ∨
      (¬AltRight τ ∧ SuccPos tagTupleLe AltPosn c'.head c.head) := hmove
  unfold AltTr at hTr
  unfold AltSrc at hSrc
  unfold AltRead at hRead
  unfold AltDst at hDst
  unfold AltWrite at hWrite
  unfold AltRight at hMove
  cases hb : τ.1.1
  all_goals rw [hb] at hTr hSrc hRead hDst hWrite hMove
  all_goals simp only at hTr hSrc hRead hDst hWrite hMove
  case tGStart =>
    -- the pass has already left the left marker, so this transition cannot fire
    exfalso
    have hhead : c.head = posStart := head_eq_posStart hpos (htape ▸ hRead)
    rw [hhead] at hlo
    exact absurd (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlo))
      (show ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart) by decide)
  case tGKeep b =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    obtain ⟨hhead, -⟩ := head_eq_posCell hpos (htape ▸ hRead)
    have hnotEnd : c.head ≠ posEnd := by rw [hhead]; exact posCell_ne_posEnd _
    have hsucc : SuccPos tagTupleLe AltPosn c.head c'.head := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd trivial h
    have htape' : c'.tape = c.tape := by
      funext r
      rcases eq_or_ne r c.head with rfl | hne
      · rw [hWrite, ← hRead]
      · exact hframe r hne
    refine Or.inl ⟨⟨ν', fun x hx => ?_, hDst.trans (by rw [hidx]), hsucc.2.1,
      isLinOrd_altTagTupleLe.2.1 _ _ _ hlo hsucc.2.2.1,
      le_posEnd_of_succPos hsucc hhi hnotEnd, htape' ▸ htape⟩,
      bitRank_lt_of_succPos hsucc⟩
    obtain ⟨hblk, hle, hne⟩ := hsupp x hx
    exact ⟨hblk, (supp_step hsucc hle).1, (supp_step hsucc hle).2⟩
  case tGSet =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    obtain ⟨hhead, -⟩ := head_eq_posCell hpos (htape ▸ hRead)
    have hnotEnd : c.head ≠ posEnd := by rw [hhead]; exact posCell_ne_posEnd _
    have hsucc : SuccPos tagTupleLe AltPosn c.head c'.head := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd trivial h
    have hblkx : QbfBlk i (τ.2 0) := by
      obtain ⟨j, hj, hbj⟩ := hTr.2
      have : j = i := Fin.ext (by rw [hj, hidx]; rfl)
      rwa [this] at hbj
    refine Or.inl ⟨⟨fun y => ν' y ∨ y = τ.2 0, fun x hx => ?_,
      hDst.trans (by rw [hidx]), hsucc.2.1,
      isLinOrd_altTagTupleLe.2.1 _ _ _ hlo hsucc.2.2.1,
      le_posEnd_of_succPos hsucc hhi hnotEnd, ?_⟩,
      bitRank_lt_of_succPos hsucc⟩
    · rcases hx with hx | rfl
      · obtain ⟨hblk, hle, hne⟩ := hsupp x hx
        exact ⟨hblk, (supp_step hsucc hle).1, (supp_step hsucc hle).2⟩
      · refine ⟨hblkx, ?_, ?_⟩
        · rw [← hhead]
          exact hsucc.2.2.1
        · rw [← hhead]
          exact hsucc.2.2.2.1
    · refine tapeAfter_set hblkx htape ?_ ?_
      · rw [← hhead]
        exact hWrite
      · intro r hr
        exact hframe r (by rwa [hhead])
  case tGTurn =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    have hsucc : SuccPos tagTupleLe AltPosn c'.head c.head := by
      rcases hMove with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by simp)
      · exact h
    have htape' : c'.tape = c.tape := by
      funext r
      rcases eq_or_ne r c.head with rfl | hne
      · rw [hWrite, ← hRead]
      · exact hframe r hne
    -- the turn happens at the right marker, so the pass resumes at the last cell
    have hhead : c.head = posEnd := head_eq_posEnd hpos (htape ▸ hRead)
    have hback : c'.head = posCell (qtopA (A := A)) :=
      succPos_left_unique isLinOrd_altTagTupleLe hsucc (by rw [hhead]; exact succPos_posCell_posEnd)
    exact Or.inr ⟨ν', fun x hx => (hsupp x hx).1, hDst.trans (by rw [hidx]), hsucc.1,
      by rw [hback]; exact altTagTupleLe_refl _, htape' ▸ htape⟩
  all_goals
    first
      | exact hTr.elim
      | exact absurd (hst.symm.trans hSrc) (by simp [acstI, aoneI])

/-! ### Where a sweep hands over -/

/-- **What the machine has reached once the sweep of index `i` is over**: the
head is back at the first cell and the tape holds what the block wrote. The
state is the entry of the next sweep, or – after the last one – the entry of
the check phase, or acceptance outright, an instance with no clause at all
being satisfied by a conjunctive matrix. -/
def AfterSweep (cnf : Bool) (i : Fin k) (ρ : Fin k → A → Prop) (c : Config (AltV k A)) : Prop :=
  c.head = posCell qbotA ∧ c.tape = tapeAfter ρ ((i : ℕ) + 1) ∧
    (((i : ℕ) + 1 < k ∧ c.state = stG i.succ true) ∨
      ((i : ℕ) + 1 = k ∧
        ((∃ c₀ : A, QbfMinCl k c₀ ∧ c.state = stChk false true c₀) ∨
          ((∀ e : A, ¬QbfCl k e) ∧ cnf = true ∧ c.state = stAcc))))

/-- **One step of the leftward pass, whatever the machine chooses.** Only four
transitions can fire from a leftward sweeping state, and none of them writes:
`tGBack` walks the cells back, and the three that fire at the left marker hand
the tape over – to the next sweep, to the check phase, or to acceptance. -/
theorem inSweepL_step {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c c' : Config (AltV k A)} (hinv : InSweepL i νs c)
    (hstep : (altMachine k A cnf).Step c c') :
    (InSweepL i νs c' ∧
        bitRank tagTupleLe AltPosn c'.head < bitRank tagTupleLe AltPosn c.head) ∨
      ∃ ν' : A → Prop, (∀ x : A, ν' x → QbfBlk i x) ∧
        AfterSweep cnf i (Function.update νs i ν') c' := by
  classical
  obtain ⟨ν', hsupp, hst, hpos, hhi, htape⟩ := hinv
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  have hTr : AltTr cnf τ := hτ
  have hSrc : AltSrc cnf τ c.state := hsrc
  have hRead : AltRead τ (c.tape c.head) := hread
  have hDst : AltDst cnf τ c'.state := hdst
  have hWrite : AltWrite τ (c'.tape c.head) := hwrite
  have hMove : (AltRight τ ∧ SuccPos tagTupleLe AltPosn c.head c'.head) ∨
      (¬AltRight τ ∧ SuccPos tagTupleLe AltPosn c'.head c.head) := hmove
  -- none of the four writes, so the tape never changes again
  have hkeep : ∀ s : AltV k A, c.tape c.head = s → c'.tape c.head = s → c'.tape = c.tape := by
    intro s h1 h2
    funext r
    rcases eq_or_ne r c.head with rfl | hne
    · rw [h2, ← h1]
    · exact hframe r hne
  unfold AltTr at hTr
  unfold AltSrc at hSrc
  unfold AltRead at hRead
  unfold AltDst at hDst
  unfold AltWrite at hWrite
  unfold AltRight at hMove
  cases hb : τ.1.1
  all_goals rw [hb] at hTr hSrc hRead hDst hWrite hMove
  all_goals simp only at hTr hSrc hRead hDst hWrite hMove
  case tGBack b =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    have hsucc : SuccPos tagTupleLe AltPosn c'.head c.head := by
      rcases hMove with ⟨h, -⟩ | ⟨-, h⟩
      · exact h.elim
      · exact h
    have htape' : c'.tape = c.tape := hkeep _ hRead hWrite
    exact Or.inl ⟨⟨ν', hsupp, hDst.trans (by rw [hidx]), hsucc.1,
      isLinOrd_altTagTupleLe.2.1 _ _ _ hsucc.2.2.1 hhi, htape' ▸ htape⟩,
      bitRank_lt_of_succPos hsucc⟩
  case tGNext =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    have hlt : (i : ℕ) + 1 < k := by
      have := hTr.2
      rwa [hidx, Fin.val_castSucc] at this
    have htape' : c'.tape = c.tape := hkeep _ hRead hWrite
    have hhead : c.head = posStart := head_eq_posStart hpos (htape ▸ hRead)
    have hsucc : SuccPos tagTupleLe AltPosn (posStart : AltV k A) c'.head := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · rwa [hhead] at h
      · exact absurd trivial h
    have hhead' : c'.head = posCell qbotA :=
      TMData.succPos_right_unique (M := (altMachine k A cnf).toTMData)
        isLinOrd_altTagTupleLe hsucc succPos_posStart_posCell
    -- the sweep index steps up: `i.castSucc + 1` is `i.succ`
    have hnext : (i.castSucc + 1 : Fin (k + 1)) = i.succ := by
      refine Fin.ext ?_
      rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc, Fin.val_succ]
    refine Or.inr ⟨ν', hsupp, hhead', htape' ▸ htape, Or.inl ⟨hlt, ?_⟩⟩
    rw [hDst, hidx, hnext]
  case tGEndChk =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    have hlast : (i : ℕ) + 1 = k := by
      have := hTr.2.1
      rwa [hidx, Fin.val_castSucc] at this
    have htape' : c'.tape = c.tape := hkeep _ hRead hWrite
    have hhead : c.head = posStart := head_eq_posStart hpos (htape ▸ hRead)
    have hsucc : SuccPos tagTupleLe AltPosn (posStart : AltV k A) c'.head := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · rwa [hhead] at h
      · exact absurd trivial h
    have hhead' : c'.head = posCell qbotA :=
      TMData.succPos_right_unique (M := (altMachine k A cnf).toTMData)
        isLinOrd_altTagTupleLe hsucc succPos_posStart_posCell
    exact Or.inr ⟨ν', hsupp, hhead', htape' ▸ htape,
      Or.inr ⟨hlast, Or.inl ⟨τ.2 0, hTr.2.2, hDst⟩⟩⟩
  case tGEndAcc =>
    have hidx : τ.1.2 = i.castSucc := (acstI_eq_iff.mp (hSrc.symm.trans hst)).2
    have hlast : (i : ℕ) + 1 = k := by
      have := hTr.2.1
      rwa [hidx, Fin.val_castSucc] at this
    have htape' : c'.tape = c.tape := hkeep _ hRead hWrite
    have hhead : c.head = posStart := head_eq_posStart hpos (htape ▸ hRead)
    have hsucc : SuccPos tagTupleLe AltPosn (posStart : AltV k A) c'.head := by
      rcases hMove with ⟨-, h⟩ | ⟨h, -⟩
      · rwa [hhead] at h
      · exact absurd trivial h
    have hhead' : c'.head = posCell qbotA :=
      TMData.succPos_right_unique (M := (altMachine k A cnf).toTMData)
        isLinOrd_altTagTupleLe hsucc succPos_posStart_posCell
    exact Or.inr ⟨ν', hsupp, hhead', htape' ▸ htape,
      Or.inr ⟨hlast, Or.inr ⟨hTr.2.2.2, hTr.2.2.1, hDst⟩⟩⟩
  all_goals
    first
      | exact hTr.elim
      | exact absurd (hst.symm.trans hSrc) (by simp [acstI, aoneI])

end Readoff

end AltQbf

end DescriptiveComplexity
