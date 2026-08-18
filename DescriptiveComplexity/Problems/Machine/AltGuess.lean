/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltRead

/-!
# A round of the game, played by either player

What a sweep amounts to, whichever player owns its block. Its moves are exactly
the truth assignments of the block: for an existential block the machine picks
one, for a universal block it must survive all of them, and
`DescriptiveComplexity.AltQbf.inSweepR_step` / `DescriptiveComplexity.AltQbf.inSweepL_step`
say that *every* play is the run of some assignment.

The universal half needs two things beyond the read-off. The sweep is never
stuck (`DescriptiveComplexity.AltQbf.exists_step_of_inSweepR`,
`DescriptiveComplexity.AltQbf.exists_step_of_inSweepL`) – at a cell it may keep or set
the value, at the markers it turns or hands over – and it terminates, the head
moving up until the turn and down afterwards. Both are needed because a
universal configuration accepts only when it *has* a successor and all of them
accept, so an induction on the budget alone would never reach its base case.

The one place the handover can genuinely be stuck is the left marker of the
last sweep, where the machine passes to the check phase: a disjunctive matrix
with no term at all has nothing to check and nothing to accept. That is
`DescriptiveComplexity.AltQbf.CanHandOver`, and it is exactly the case where the
formula is false.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

open Language Structure

noncomputable section Guess

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The block of a sweeping state -/

/-- **A sweeping state is universal exactly when its block is.** -/
theorem isUniv_stG {cnf start : Bool} {i : Fin k} {d : Bool} :
    (altMachine k A cnf).IsUniv start (stG i.castSucc d : AltV k A) ↔
      blockPol start (i : ℕ) = false := by
  constructor
  · rintro ⟨j, hj, hpol⟩
    have hj' : j = altBlockOf (stG i.castSucc d : AltV k A) := hj
    rw [altBlockOf_stG (show ((i.castSucc : Fin (k + 1)) : ℕ) < k from i.isLt) d,
      Fin.val_castSucc] at hj'
    rwa [hj'] at hpol
  · intro hpol
    refine ⟨(i : ℕ), show (i : ℕ) = altBlockOf (stG i.castSucc d : AltV k A) from ?_, hpol⟩
    rw [altBlockOf_stG (show ((i.castSucc : Fin (k + 1)) : ℕ) < k from i.isLt) d,
      Fin.val_castSucc]

/-! ### The sweep is never stuck -/

omit [(Language.qbf k).Structure A] in
/-- A position at or below the last cell is the left marker or a cell. -/
theorem posn_le_posCell_cases {p : AltV k A} (hp : AltPosn p)
    (hle : tagTupleLe p (posCell (qtopA (A := A)) : AltV k A)) :
    p = posStart ∨ p = posCell (p.2 0) := by
  rcases base_le_pCell (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hle)) with h | h
  · exact Or.inl (eq_posStart_of_posn hp h)
  · exact Or.inr (eq_posCell_of_posn hp h)

omit [(Language.qbf k).Structure A] in
/-- A position between the first cell and the right marker is a cell or the
right marker. -/
theorem posn_between_cases {p : AltV k A} (hp : AltPosn p)
    (hlo : tagTupleLe (posCell (qbotA (A := A)) : AltV k A) p)
    (hhi : tagTupleLe p (posEnd : AltV k A)) :
    p = posCell (p.2 0) ∨ p = posEnd := by
  rcases base_between (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlo))
    (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hhi)) with h | h
  · exact Or.inl (eq_posCell_of_posn hp h)
  · exact Or.inr (eq_posEnd_of_posn hp h)

omit [(Language.qbf k).Structure A] in
/-- A cell has a position above it: the right marker. -/
theorem not_maxPos_of_ne_posEnd {p : AltV k A} (hhi : tagTupleLe p (posEnd : AltV k A))
    (hne : p ≠ posEnd) : ¬MaxPos tagTupleLe AltPosn p := fun hmax =>
  hne (isLinOrd_altTagTupleLe.2.2.1 p posEnd hhi (hmax.2 posEnd altPosn_posEnd))

omit [(Language.qbf k).Structure A] in
/-- A cell has a position below it: the left marker. -/
theorem not_minPos_posCell (x : A) : ¬MinPos tagTupleLe AltPosn (posCell x : AltV k A) :=
  fun hmin => absurd (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le
    (hmin.2 posStart altPosn_posStart)))
    (show ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart) by decide)

/-- **The rightward pass always has a move**: at a cell it keeps the value it
reads, and at the right marker it turns. -/
theorem exists_step_of_inSweepR {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c : Config (AltV k A)} (hinv : InSweepR i νs c) :
    ∃ c', (altMachine k A cnf).Step c c' := by
  classical
  obtain ⟨ν', -, hst, hpos, hlo, hhi, htape⟩ := hinv
  rcases posn_between_cases hpos hlo hhi with hcell | hend
  · -- at a cell: keep whatever value it holds
    obtain ⟨q, hq⟩ := TMData.exists_succPos' (M := (altMachine k A cnf).toTMData)
      isLinOrd_altTagTupleLe hpos
      (not_maxPos_of_ne_posEnd hhi (by rw [hcell]; exact posCell_ne_posEnd _))
    set v := valAfter (Function.update νs i ν') ((i : ℕ) + 1) (c.head.2 0) with hv
    refine ⟨{ state := stG i.castSucc true, head := q, tape := c.tape },
      aoneI (.tGKeep v) i.castSucc (c.head.2 0), ⟨fun a => qbotA_le a, i.isLt⟩,
      hst, ?_, rfl, ?_, fun r _ => rfl, Or.inl ⟨trivial, hq⟩⟩
    · change c.tape c.head = symV v (c.head.2 0)
      rw [htape]
      conv_lhs => rw [hcell]
      exact tapeAfter_posCell _ _
    · change c.tape c.head = symV v (c.head.2 0)
      rw [htape]
      conv_lhs => rw [hcell]
      exact tapeAfter_posCell _ _
  · -- at the right marker: turn round
    refine ⟨{ state := stG i.castSucc false, head := posCell qtopA, tape := c.tape },
      acstI .tGTurn i.castSucc, ⟨isMinTup2_qbot, i.isLt⟩, hst, ?_, rfl, ?_,
      fun r _ => rfl, Or.inr ⟨id, by rw [hend]; exact succPos_posCell_posEnd⟩⟩
    · change c.tape c.head = symEnd
      rw [htape, hend]
      rfl
    · change c.tape c.head = symEnd
      rw [htape, hend]
      rfl

variable (k A) in
/-- **The last sweep can hand over**: either there is a clause to check, or
there is none and the matrix is conjunctive, so the machine accepts outright.
This fails only for a disjunctive matrix with no term, which is the false
formula. -/
def CanHandOver (cnf : Bool) : Prop :=
  (∃ c₀ : A, QbfMinCl k c₀) ∨ (cnf = true ∧ ∀ e : A, ¬QbfCl k e)

/-- **The leftward pass always has a move**, given that the handover is
available: at a cell it steps back, at the left marker it passes the tape
on. -/
theorem exists_step_of_inSweepL {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c : Config (AltV k A)} (hinv : InSweepL i νs c)
    (hover : (i : ℕ) + 1 = k → CanHandOver k A cnf) :
    ∃ c', (altMachine k A cnf).Step c c' := by
  classical
  obtain ⟨ν', -, hst, hpos, hhi, htape⟩ := hinv
  rcases posn_le_posCell_cases hpos hhi with hstart | hcell
  · -- at the left marker: hand the tape over
    rcases Nat.lt_or_ge ((i : ℕ) + 1) k with hlt | hge
    · refine ⟨{ state := stG (i.castSucc + 1) true, head := posCell qbotA, tape := c.tape },
        acstI .tGNext i.castSucc, ⟨isMinTup2_qbot, hlt⟩, hst, ?_, rfl, ?_,
        fun r _ => rfl, Or.inl ⟨trivial, by rw [hstart]; exact succPos_posStart_posCell⟩⟩
      · change c.tape c.head = symStart
        rw [htape, hstart]
        rfl
      · change c.tape c.head = symStart
        rw [htape, hstart]
        rfl
    · have hlast : ((i.castSucc : Fin (k + 1)) : ℕ) + 1 = k := by
        have := i.isLt
        rw [Fin.val_castSucc]
        omega
      rcases hover (by omega) with ⟨c₀, hc₀⟩ | ⟨hcnf, hno⟩
      · refine ⟨{ state := stChk false true c₀, head := posCell qbotA, tape := c.tape },
          aoneI .tGEndChk i.castSucc c₀, ⟨fun a => qbotA_le a, hlast, hc₀⟩, hst, ?_, rfl, ?_,
          fun r _ => rfl, Or.inl ⟨trivial, by rw [hstart]; exact succPos_posStart_posCell⟩⟩
        · change c.tape c.head = symStart
          rw [htape, hstart]
          rfl
        · change c.tape c.head = symStart
          rw [htape, hstart]
          rfl
      · refine ⟨{ state := stAcc, head := posCell qbotA, tape := c.tape },
          acstI .tGEndAcc i.castSucc, ⟨isMinTup2_qbot, hlast, hcnf, hno⟩, hst, ?_, rfl, ?_,
          fun r _ => rfl, Or.inl ⟨trivial, by rw [hstart]; exact succPos_posStart_posCell⟩⟩
        · change c.tape c.head = symStart
          rw [htape, hstart]
          rfl
        · change c.tape c.head = symStart
          rw [htape, hstart]
          rfl
  · -- at a cell: step back over it
    obtain ⟨q, hq⟩ := exists_predPos isLinOrd_altTagTupleLe hpos
      (by rw [hcell]; exact not_minPos_posCell _)
    set v := valAfter (Function.update νs i ν') ((i : ℕ) + 1) (c.head.2 0) with hv
    refine ⟨{ state := stG i.castSucc false, head := q, tape := c.tape },
      aoneI (.tGBack v) i.castSucc (c.head.2 0), ⟨fun a => qbotA_le a, i.isLt⟩,
      hst, ?_, rfl, ?_, fun r _ => rfl, Or.inr ⟨id, hq⟩⟩
    · change c.tape c.head = symV v (c.head.2 0)
      rw [htape]
      conv_lhs => rw [hcell]
      exact tapeAfter_posCell _ _
    · change c.tape c.head = symV v (c.head.2 0)
      rw [htape]
      conv_lhs => rw [hcell]
      exact tapeAfter_posCell _ _

/-! ### A universal round survives every play

Two inductions, one per pass, on the only quantity that changes monotonically:
the rank of the head, which rises during the rightward pass and falls during
the leftward one. The budget is threaded through as a bound rather than as a
step count, since a universal player is answered by *all* plays at once and
there is no single run to count.
-/

/-- **The leftward pass of a universal round accepts**, given that whatever it
hands over accepts. -/
theorem altAcc_of_inSweepL {cnf start : Bool} {i : Fin k} {νs : Fin k → A → Prop} {n' : ℕ}
    (huniv : blockPol start (i : ℕ) = false) (hover : (i : ℕ) + 1 = k → CanHandOver k A cnf)
    (hexit : ∀ (ν' : A → Prop) (c : Config (AltV k A)), (∀ x : A, ν' x → QbfBlk i x) →
      AfterSweep cnf i (Function.update νs i ν') c → (altMachine k A cnf).AltAcc start n' c) :
    ∀ (r n : ℕ) (c : Config (AltV k A)), InSweepL i νs c →
      bitRank tagTupleLe AltPosn c.head ≤ r → r + 1 + n' ≤ n →
      (altMachine k A cnf).AltAcc start n c := by
  intro r
  induction r with
  | zero =>
    intro n c hinv hrank hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hst : c.state = stG i.castSucc false := by
      obtain ⟨-, -, h, -⟩ := hinv
      exact h
    refine Or.inr (Or.inl ⟨by rw [hst]; exact isUniv_stG.mpr huniv,
      exists_step_of_inSweepL hinv hover, fun c' hstep => ?_⟩)
    rcases inSweepL_step hinv hstep with ⟨-, hlt⟩ | ⟨ν', hsupp, hafter⟩
    · omega
    · exact ATMData.altAcc_mono (by omega) (hexit ν' c' hsupp hafter)
  | succ r ih =>
    intro n c hinv hrank hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hst : c.state = stG i.castSucc false := by
      obtain ⟨-, -, h, -⟩ := hinv
      exact h
    refine Or.inr (Or.inl ⟨by rw [hst]; exact isUniv_stG.mpr huniv,
      exists_step_of_inSweepL hinv hover, fun c' hstep => ?_⟩)
    rcases inSweepL_step hinv hstep with ⟨hinv', hlt⟩ | ⟨ν', hsupp, hafter⟩
    · exact ih m c' hinv' (by omega) (by omega)
    · exact ATMData.altAcc_mono (by omega) (hexit ν' c' hsupp hafter)

/-- **The rightward pass of a universal round accepts.** The measure is what
the head has left to climb; at the turn the leftward pass takes over, with what
it has left to descend. The two together are the length of the sweep, so a
universal round costs no more than the run it must survive. -/
theorem altAcc_of_inSweepR {cnf start : Bool} {i : Fin k} {νs : Fin k → A → Prop} {n' : ℕ}
    (huniv : blockPol start (i : ℕ) = false) (hover : (i : ℕ) + 1 = k → CanHandOver k A cnf)
    (hexit : ∀ (ν' : A → Prop) (c : Config (AltV k A)), (∀ x : A, ν' x → QbfBlk i x) →
      AfterSweep cnf i (Function.update νs i ν') c → (altMachine k A cnf).AltAcc start n' c) :
    ∀ (r n : ℕ) (c : Config (AltV k A)), InSweepR i νs c →
      bitRank tagTupleLe AltPosn (posEnd : AltV k A) - bitRank tagTupleLe AltPosn c.head ≤ r →
      r + 1 + (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) + 1 + n') ≤ n →
      (altMachine k A cnf).AltAcc start n c := by
  have hbound : ∀ e : Config (AltV k A), InSweepR i νs e →
      bitRank tagTupleLe AltPosn e.head ≤
        bitRank tagTupleLe AltPosn (posEnd : AltV k A) := by
    rintro e ⟨-, -, -, hpos, -, hhi, -⟩
    exact TMData.bitRank_le_of_le (M := (altMachine k A cnf).toTMData)
      isLinOrd_altTagTupleLe hpos hhi
  have hboundL : ∀ e : Config (AltV k A), InSweepL i νs e →
      bitRank tagTupleLe AltPosn e.head ≤
        bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) := by
    rintro e ⟨-, -, -, hpos, hhi, -⟩
    exact TMData.bitRank_le_of_le (M := (altMachine k A cnf).toTMData)
      isLinOrd_altTagTupleLe hpos hhi
  intro r
  induction r with
  | zero =>
    intro n c hinv hrank hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hst : c.state = stG i.castSucc true := by
      obtain ⟨-, -, h, -⟩ := hinv
      exact h
    refine Or.inr (Or.inl ⟨by rw [hst]; exact isUniv_stG.mpr huniv,
      exists_step_of_inSweepR hinv, fun c' hstep => ?_⟩)
    rcases inSweepR_step hinv hstep with ⟨hinv', hlt⟩ | hinvL
    · exact absurd (hbound c' hinv') (by omega)
    · exact altAcc_of_inSweepL huniv hover hexit
        (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A)) m c' hinvL
        (hboundL c' hinvL) (by omega)
  | succ r ih =>
    intro n c hinv hrank hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hst : c.state = stG i.castSucc true := by
      obtain ⟨-, -, h, -⟩ := hinv
      exact h
    refine Or.inr (Or.inl ⟨by rw [hst]; exact isUniv_stG.mpr huniv,
      exists_step_of_inSweepR hinv, fun c' hstep => ?_⟩)
    rcases inSweepR_step hinv hstep with ⟨hinv', hlt⟩ | hinvL
    · exact ih m c' hinv' (by have := hbound c' hinv'; omega) (by omega)
    · exact altAcc_of_inSweepL huniv hover hexit
        (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A)) m c' hinvL
        (hboundL c' hinvL) (by omega)

/-! ### Following a run of universal configurations

A universal configuration accepts only if *every* successor does, so acceptance
descends along any run that stays universal – in particular along the intended
run of a given assignment, which is how a universal round is read for one play
at a time. These mirror `DescriptiveComplexity.TMData.stepsIn_of_segment` and
its downward twin, and could be hoisted beside them.
-/

/-- **Acceptance descends across a step** when the step is not a choice: either
the state is universal, and then every successor accepts, or it is the only
step available, and then the successor the machine picks is that one. -/
def StepForced (M : ATMData (AltV k A)) (start : Bool) (c c' : Config (AltV k A)) : Prop :=
  ¬M.Acc c.state ∧ (M.IsUniv start c.state ∨ ∀ c'', M.Step c c'' → c'' = c')

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- **One step down.** -/
theorem altAcc_down_step {M : ATMData (AltV k A)} {start : Bool} {n : ℕ}
    {c c' : Config (AltV k A)} (hf : StepForced M start c c')
    (hstep : M.Step c c') (hacc : M.AltAcc start n c) : 1 ≤ n ∧ M.AltAcc start (n - 1) c' := by
  obtain ⟨hnacc, hforced⟩ := hf
  cases n with
  | zero => exact absurd hacc hnacc
  | succ m =>
    rcases hacc with h | ⟨-, -, hall⟩ | ⟨hnu, c₁, hstep₁, hacc₁⟩
    · exact absurd h hnacc
    · exact ⟨Nat.le_add_left 1 m, hall c' hstep⟩
    · rcases hforced with hu | hdet
      · exact absurd hu hnu
      · exact ⟨Nat.le_add_left 1 m, hdet c₁ hstep₁ ▸ hacc₁⟩

omit [(Language.qbf k).Structure A] [LinearOrder A] [Nonempty A] in
/-- **Down a rising segment.** -/
theorem altAcc_along_segment {M : ATMData (AltV k A)} {start : Bool} (hlin : IsLinOrd M.Le)
    {conf : AltV k A → Config (AltV k A)} {p₀ p₁ : AltV k A} (hp₀ : M.Posn p₀)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ → M.Step (conf p) (conf q))
    (hf : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      StepForced M start (conf p) (conf q)) :
    ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ → M.AltAcc start n (conf p₀) →
      bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀ ≤ n ∧
        M.AltAcc start (n - (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀)) (conf p) := by
  have key : ∀ r : ℕ, ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ →
      bitRank M.Le M.Posn p = r → M.AltAcc start n (conf p₀) →
      bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀ ≤ n ∧
        M.AltAcc start (n - (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀)) (conf p) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro n p hp hlb hub hrank hacc
      rcases eq_or_ne p₀ p with rfl | hne
      · exact ⟨by omega, by rw [Nat.sub_self, Nat.sub_zero]; exact hacc⟩
      · obtain ⟨q, hq⟩ := exists_predPos hlin hp
          (fun hmin => hne (hlin.2.2.1 p₀ p hlb (hmin.2 p₀ hp₀)))
        have hq₀ : M.Le p₀ q := by
          rcases hlin.2.2.2 p₀ q with h | h
          · exact h
          · rcases hq.2.2.2.2 p₀ hp₀ h hlb with h' | h'
            · exact h' ▸ hlin.1 p₀
            · exact absurd h' hne
        have hq₁ : M.Le q p₁ := hlin.2.1 q p p₁ hq.2.2.1 hub
        have hrq : bitRank M.Le M.Posn p = bitRank M.Le M.Posn q + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn p₀ ≤ bitRank M.Le M.Posn q :=
          TMData.bitRank_le_of_le (M := M.toTMData) hlin hp₀ hq₀
        obtain ⟨hle, hrec⟩ := ih (bitRank M.Le M.Posn q) (by omega) n q hq.1 hq₀ hq₁ rfl hacc
        obtain ⟨hone, hstepped⟩ :=
          altAcc_down_step (hf q p hq hq₀ hub) (hstep q p hq hq₀ hub) hrec
        exact ⟨by omega, by
          have : n - (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀) =
              n - (bitRank M.Le M.Posn q - bitRank M.Le M.Posn p₀) - 1 := by omega
          rw [this]
          exact hstepped⟩
  exact fun n p hp hlb hub hacc => key _ n p hp hlb hub rfl hacc

omit [(Language.qbf k).Structure A] [LinearOrder A] [Nonempty A] in
/-- **Down a falling segment.** -/
theorem altAcc_along_segment_down {M : ATMData (AltV k A)} {start : Bool} (hlin : IsLinOrd M.Le)
    {conf : AltV k A → Config (AltV k A)} {p₀ p₁ : AltV k A} (hp₁ : M.Posn p₁)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ → M.Step (conf q) (conf p))
    (hf : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      StepForced M start (conf q) (conf p)) :
    ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ → M.AltAcc start n (conf p₁) →
      bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p ≤ n ∧
        M.AltAcc start (n - (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p)) (conf p) := by
  have key : ∀ r : ℕ, ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ →
      bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p = r → M.AltAcc start n (conf p₁) →
      bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p ≤ n ∧
        M.AltAcc start (n - (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p)) (conf p) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro n p hp hlb hub hrank hacc
      rcases eq_or_ne p p₁ with rfl | hne
      · exact ⟨by omega, by rw [Nat.sub_self, Nat.sub_zero]; exact hacc⟩
      · obtain ⟨q, hq⟩ := TMData.exists_succPos' (M := M.toTMData) hlin hp
          (fun hmax => hne (hlin.2.2.1 p p₁ hub (hmax.2 p₁ hp₁)))
        have hq₁ : M.Le q p₁ := by
          rcases hlin.2.2.2 q p₁ with h | h
          · exact h
          · rcases hq.2.2.2.2 p₁ hp₁ hub h with h' | h'
            · exact absurd h'.symm hne
            · exact h' ▸ hlin.1 q
        have hq₀ : M.Le p₀ q := hlin.2.1 p₀ p q hlb hq.2.2.1
        have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn q ≤ bitRank M.Le M.Posn p₁ :=
          TMData.bitRank_le_of_le (M := M.toTMData) hlin hq.2.1 hq₁
        obtain ⟨hle, hrec⟩ := ih (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q)
          (by omega) n q hq.2.1 hq₀ hq₁ rfl hacc
        obtain ⟨hone, hstepped⟩ :=
          altAcc_down_step (hf p q hq hlb hq₁) (hstep p q hq hlb hq₁) hrec
        exact ⟨by omega, by
          have : n - (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p) =
              n - (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q) - 1 := by omega
          rw [this]
          exact hstepped⟩
  exact fun n p hp hlb hub hacc => key _ n p hp hlb hub rfl hacc

/-! ### A universal round, followed for one assignment at a time -/

/-- A sweeping state is not accepting. -/
theorem not_acc_stG {cnf : Bool} {i : Fin (k + 1)} {d : Bool} :
    ¬(altMachine k A cnf).Acc (stG i d : AltV k A) := fun h =>
  AltBase.noConfusion (show AltBase.qG d = AltBase.qAcc from h)

variable (k A) in
/-- The steps a sweep takes before handing over: up to the right marker, round,
and back to the left one. -/
noncomputable def passLen : ℕ :=
  (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
      bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) + 1 +
    (bitRank tagTupleLe AltPosn (posCell qtopA : AltV k A) -
      bitRank tagTupleLe AltPosn (posStart : AltV k A))

omit [(Language.qbf k).Structure A] in
theorem sweepLen_eq_passLen : sweepLen k A = passLen k A + 1 := rfl

/-- **A universal round, followed along the run of one assignment.** Both
passes are runs of universal configurations, so acceptance descends along them:
whatever the round's assignment, the configuration it leaves at the left marker
accepts too. -/
theorem altAcc_passes_down {cnf start : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    (huniv : blockPol start (i : ℕ) = false) {n : ℕ}
    (hacc : (altMachine k A cnf).AltAcc start n (confSweep νs i.castSucc (posCell qbotA))) :
    passLen k A ≤ n ∧
      (altMachine k A cnf).AltAcc start (n - passLen k A) (confBack νs i.castSucc posStart) := by
  have hu : ∀ (d : Bool) (c c' : Config (AltV k A)), c.state = stG i.castSucc d →
      StepForced (altMachine k A cnf) start c c' :=
    fun d c c' hst => ⟨by rw [hst]; exact not_acc_stG,
      Or.inl (by rw [hst]; exact isUniv_stG.mpr huniv)⟩
  have hik : ((i.castSucc : Fin (k + 1)) : ℕ) < k := i.isLt
  -- up to the right marker
  obtain ⟨hle₁, hacc₁⟩ := altAcc_along_segment (M := altMachine k A cnf)
    isLinOrd_altTagTupleLe (conf := fun p => confSweep νs i.castSucc p)
    (p₀ := posCell qbotA) (p₁ := posEnd) (altPosn_posCell _)
    (fun p q hsucc hlb hb => step_sweep hik hsucc hb fun hst => absurd
      (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlb))
      (by rw [hst]; exact (by decide : ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart))))
    (fun p q _ _ _ => hu true _ _ rfl) n posEnd altPosn_posEnd (posCell_le_posEnd _)
    (altTagTupleLe_refl _) hacc
  -- the turn
  obtain ⟨hle₂, hacc₂⟩ := altAcc_down_step (hu true _ _ rfl)
    (step_turnBack (νs := νs) hik) hacc₁
  -- back to the left marker
  obtain ⟨hle₃, hacc₃⟩ := altAcc_along_segment_down (M := altMachine k A cnf)
    isLinOrd_altTagTupleLe (conf := fun p => confBack νs i.castSucc p)
    (p₀ := posStart) (p₁ := posCell qtopA) (altPosn_posCell _)
    (fun p q hsucc hlb hb => step_back hik hsucc hlb hb)
    (fun p q _ _ _ => hu false _ _ rfl) _ posStart altPosn_posStart
    (altTagTupleLe_refl _) (posStart_le_posCell _) hacc₂
  -- the three bounds, restated against the tape order rather than the machine's
  have h₁ : bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
      bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A) ≤ n := hle₁
  have h₂ : 1 ≤ n - (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
      bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) := hle₂
  have h₃ : bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) -
      bitRank tagTupleLe AltPosn (posStart : AltV k A) ≤
      n - (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
        bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) - 1 := hle₃
  refine ⟨by simp only [passLen]; omega, ?_⟩
  have : n - passLen k A =
      n - (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
        bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) - 1 -
        (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) -
          bitRank tagTupleLe AltPosn (posStart : AltV k A)) := by
    simp only [passLen]
    omega
  rw [this]
  exact hacc₃

/-! ### Following a run of existential configurations

The mirror of the descent: an existential configuration accepts as soon as
*one* successor does, so acceptance climbs back up any run whose
configurations all belong to the machine. This is how an existential round
plays the assignment it has chosen.
-/

omit [(Language.qbf k).Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- **One step up.** -/
theorem altAcc_up_step {M : ATMData (AltV k A)} {start : Bool} {n : ℕ}
    {c c' : Config (AltV k A)} (hnu : ¬M.IsUniv start c.state) (hstep : M.Step c c')
    (hacc : M.AltAcc start n c') : M.AltAcc start (n + 1) c :=
  Or.inr (Or.inr ⟨hnu, c', hstep, hacc⟩)

omit [(Language.qbf k).Structure A] [LinearOrder A] [Nonempty A] in
/-- **Up a rising segment.** -/
theorem altAcc_along_segment_up {M : ATMData (AltV k A)} {start : Bool} (hlin : IsLinOrd M.Le)
    {conf : AltV k A → Config (AltV k A)} {p₀ p₁ : AltV k A} (hp₀ : M.Posn p₀)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ → M.Step (conf p) (conf q))
    (hnu : ∀ p, ¬M.IsUniv start (conf p).state) :
    ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ → M.AltAcc start n (conf p) →
      M.AltAcc start (n + (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀)) (conf p₀) := by
  have key : ∀ r : ℕ, ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ →
      bitRank M.Le M.Posn p = r → M.AltAcc start n (conf p) →
      M.AltAcc start (n + (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀)) (conf p₀) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro n p hp hlb hub hrank hacc
      rcases eq_or_ne p₀ p with rfl | hne
      · rw [Nat.sub_self, Nat.add_zero]
        exact hacc
      · obtain ⟨q, hq⟩ := exists_predPos hlin hp
          (fun hmin => hne (hlin.2.2.1 p₀ p hlb (hmin.2 p₀ hp₀)))
        have hq₀ : M.Le p₀ q := by
          rcases hlin.2.2.2 p₀ q with h | h
          · exact h
          · rcases hq.2.2.2.2 p₀ hp₀ h hlb with h' | h'
            · exact h' ▸ hlin.1 p₀
            · exact absurd h' hne
        have hq₁ : M.Le q p₁ := hlin.2.1 q p p₁ hq.2.2.1 hub
        have hrq : bitRank M.Le M.Posn p = bitRank M.Le M.Posn q + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn p₀ ≤ bitRank M.Le M.Posn q :=
          TMData.bitRank_le_of_le (M := M.toTMData) hlin hp₀ hq₀
        have hup : M.AltAcc start (n + 1) (conf q) :=
          altAcc_up_step (hnu q) (hstep q p hq hq₀ hub) hacc
        have hrec := ih (bitRank M.Le M.Posn q) (by omega) (n + 1) q hq.1 hq₀ hq₁ rfl hup
        have harith : n + (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀) =
            n + 1 + (bitRank M.Le M.Posn q - bitRank M.Le M.Posn p₀) := by omega
        rw [harith]
        exact hrec
  exact fun n p hp hlb hub hacc => key _ n p hp hlb hub rfl hacc

omit [(Language.qbf k).Structure A] [LinearOrder A] [Nonempty A] in
/-- **Up a falling segment.** -/
theorem altAcc_along_segment_up_down {M : ATMData (AltV k A)} {start : Bool}
    (hlin : IsLinOrd M.Le) {conf : AltV k A → Config (AltV k A)} {p₀ p₁ : AltV k A}
    (hp₁ : M.Posn p₁)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ → M.Step (conf q) (conf p))
    (hnu : ∀ p, ¬M.IsUniv start (conf p).state) :
    ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ → M.AltAcc start n (conf p) →
      M.AltAcc start (n + (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p)) (conf p₁) := by
  have key : ∀ r : ℕ, ∀ (n : ℕ) (p : AltV k A), M.Posn p → M.Le p₀ p → M.Le p p₁ →
      bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p = r → M.AltAcc start n (conf p) →
      M.AltAcc start (n + (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p)) (conf p₁) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro n p hp hlb hub hrank hacc
      rcases eq_or_ne p p₁ with rfl | hne
      · rw [Nat.sub_self, Nat.add_zero]
        exact hacc
      · obtain ⟨q, hq⟩ := TMData.exists_succPos' (M := M.toTMData) hlin hp
          (fun hmax => hne (hlin.2.2.1 p p₁ hub (hmax.2 p₁ hp₁)))
        have hq₁ : M.Le q p₁ := by
          rcases hlin.2.2.2 q p₁ with h | h
          · exact h
          · rcases hq.2.2.2.2 p₁ hp₁ hub h with h' | h'
            · exact absurd h'.symm hne
            · exact h' ▸ hlin.1 q
        have hq₀ : M.Le p₀ q := hlin.2.1 p₀ p q hlb hq.2.2.1
        have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn q ≤ bitRank M.Le M.Posn p₁ :=
          TMData.bitRank_le_of_le (M := M.toTMData) hlin hq.2.1 hq₁
        have hup : M.AltAcc start (n + 1) (conf q) :=
          altAcc_up_step (hnu q) (hstep p q hq hlb hq₁) hacc
        have hrec := ih (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q) (by omega)
          (n + 1) q hq.2.1 hq₀ hq₁ rfl hup
        have harith : n + (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p) =
            n + 1 + (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q) := by omega
        rw [harith]
        exact hrec
  exact fun n p hp hlb hub hacc => key _ n p hp hlb hub rfl hacc

/-- **An existential round, played along the run of the assignment it picks.**
The mirror of `DescriptiveComplexity.AltQbf.altAcc_passes_down`: acceptance at the
left marker, where the round hands over, climbs back to its entry. -/
theorem altAcc_passes_up {cnf start : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    (hex : blockPol start (i : ℕ) = true) {n : ℕ}
    (hacc : (altMachine k A cnf).AltAcc start n (confBack νs i.castSucc posStart)) :
    (altMachine k A cnf).AltAcc start (n + passLen k A)
      (confSweep νs i.castSucc (posCell qbotA)) := by
  have hnu : ∀ (d : Bool) (c : Config (AltV k A)), c.state = stG i.castSucc d →
      ¬(altMachine k A cnf).IsUniv start c.state := by
    intro d c hst hu
    rw [hst] at hu
    exact absurd (isUniv_stG.mp hu) (by rw [hex]; exact Bool.noConfusion)
  have hik : ((i.castSucc : Fin (k + 1)) : ℕ) < k := i.isLt
  -- back up the leftward pass to the last cell
  have hup₁ := altAcc_along_segment_up_down (M := altMachine k A cnf) isLinOrd_altTagTupleLe
    (conf := fun p => confBack νs i.castSucc p) (p₀ := posStart) (p₁ := posCell qtopA)
    (altPosn_posCell _) (fun p q hsucc hlb hb => step_back hik hsucc hlb hb)
    (fun p => hnu false _ rfl) n posStart altPosn_posStart (altTagTupleLe_refl _)
    (posStart_le_posCell _) hacc
  -- back over the turn
  have hup₂ := altAcc_up_step (hnu true _ rfl) (step_turnBack (νs := νs) hik) hup₁
  -- back up the rightward pass to the first cell
  have hup₃ := altAcc_along_segment_up (M := altMachine k A cnf) isLinOrd_altTagTupleLe
    (conf := fun p => confSweep νs i.castSucc p) (p₀ := posCell qbotA) (p₁ := posEnd)
    (altPosn_posCell _)
    (fun p q hsucc hlb hb => step_sweep hik hsucc hb fun hst => absurd
      (altBaseIdx_le_of_tag_le (altTagTupleLe_tag_le hlb))
      (by rw [hst]; exact (by decide : ¬(altBaseIdx AltBase.pCell ≤ altBaseIdx AltBase.pStart))))
    (fun p => hnu true _ rfl) _ posEnd altPosn_posEnd (posCell_le_posEnd _)
    (altTagTupleLe_refl _) hup₂
  have harith : n + passLen k A =
      n + (bitRank tagTupleLe AltPosn (posCell (qtopA (A := A)) : AltV k A) -
        bitRank tagTupleLe AltPosn (posStart : AltV k A)) + 1 +
        (bitRank tagTupleLe AltPosn (posEnd : AltV k A) -
          bitRank tagTupleLe AltPosn (posCell qbotA : AltV k A)) := by
    simp only [passLen]
    omega
  rw [harith]
  exact hup₃

/-! ### An existential round, and reading any round off an accepting run -/

/-- Being somewhere in the sweep of round `i`, on either pass. -/
def InSweep (i : Fin k) (νs : Fin k → A → Prop) (c : Config (AltV k A)) : Prop :=
  InSweepR i νs c ∨ InSweepL i νs c

/-- **A sweep either continues or hands over**, whatever the machine does. -/
theorem inSweep_step {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c c' : Config (AltV k A)} (hinv : InSweep i νs c)
    (hstep : (altMachine k A cnf).Step c c') :
    InSweep i νs c' ∨ ∃ ν' : A → Prop, (∀ x : A, ν' x → QbfBlk i x) ∧
      AfterSweep cnf i (Function.update νs i ν') c' := by
  rcases hinv with h | h
  · rcases inSweepR_step h hstep with ⟨h', -⟩ | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
  · rcases inSweepL_step h hstep with ⟨h', -⟩ | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr h'

/-- The state of a sweeping configuration. -/
theorem state_of_inSweep {i : Fin k} {νs : Fin k → A → Prop} {c : Config (AltV k A)}
    (hinv : InSweep i νs c) :
    c.state = stG i.castSucc true ∨ c.state = stG i.castSucc false := by
  rcases hinv with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A sweeping configuration is not accepting. -/
theorem not_acc_of_inSweep {cnf : Bool} {i : Fin k} {νs : Fin k → A → Prop}
    {c : Config (AltV k A)} (hinv : InSweep i νs c) : ¬(altMachine k A cnf).Acc c.state := by
  rcases state_of_inSweep hinv with h | h <;> rw [h] <;> exact not_acc_stG

/-- **Any accepting run of a round hands over an assignment.** Whichever player
owns the block, an accepting configuration has an accepting successor – the one
it picks, or any of the ones it must survive – and following those successors
reaches the handover, since a sweeping state never accepts. -/
theorem exit_of_altAcc {cnf start : Bool} {i : Fin k} {νs : Fin k → A → Prop} :
    ∀ (n : ℕ) (c : Config (AltV k A)), InSweep i νs c →
      (altMachine k A cnf).AltAcc start n c →
      ∃ (ν' : A → Prop) (d : Config (AltV k A)) (m : ℕ), m < n ∧ (∀ x : A, ν' x → QbfBlk i x) ∧
        AfterSweep cnf i (Function.update νs i ν') d ∧ (altMachine k A cnf).AltAcc start m d := by
  intro n
  induction n with
  | zero => intro c hinv hacc; exact absurd hacc (not_acc_of_inSweep hinv)
  | succ n ih =>
    intro c hinv hacc
    have key : ∀ c₁, (altMachine k A cnf).Step c c₁ → (altMachine k A cnf).AltAcc start n c₁ →
        ∃ (ν' : A → Prop) (d : Config (AltV k A)) (m : ℕ), m < n + 1 ∧
          (∀ x : A, ν' x → QbfBlk i x) ∧ AfterSweep cnf i (Function.update νs i ν') d ∧
          (altMachine k A cnf).AltAcc start m d := by
      intro c₁ hstep hacc₁
      rcases inSweep_step hinv hstep with hinv' | ⟨ν', hsupp, hafter⟩
      · obtain ⟨ν', d, m, hm, hsupp, hafter, haccd⟩ := ih c₁ hinv' hacc₁
        exact ⟨ν', d, m, by omega, hsupp, hafter, haccd⟩
      · exact ⟨ν', c₁, n, by omega, hsupp, hafter, hacc₁⟩
    rcases hacc with h | ⟨-, ⟨c₁, hstep⟩, hall⟩ | ⟨-, c₁, hstep, hacc₁⟩
    · exact absurd h (not_acc_of_inSweep hinv)
    · exact key c₁ hstep (hall c₁ hstep)
    · exact key c₁ hstep hacc₁

end Guess

end AltQbf

end DescriptiveComplexity
