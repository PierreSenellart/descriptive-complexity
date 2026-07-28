/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Induction
import DescriptiveComplexity.Problems.SuccinctReach

/-!
# QSAT is PSPACE-hard

The reduction of SUCCINCT-REACH to QSAT is correct
(`DescriptiveComplexity.qsatHolds_iff`), so the interpretation of
`DescriptiveComplexity.Problems.Qsat.Interp` is an ordered first-order reduction
(`DescriptiveComplexity.succinctReach_ordered_fo_reduction_qsat`) and QSAT is
PSPACE-complete (`DescriptiveComplexity.QSAT_PSPACE_complete`).

Peeling the first block – the two endpoints of the walk – opens the position of
the first level, which `DescriptiveComplexity.game_level` says computes
reachability in at most `2 ^ m` moves for `m` the number of state variables; and
that is reachability, by `DescriptiveComplexity.succinctReachable_iff_savPow`.
An instance with no state variable has no level at all: the first block and every
level block are empty, so the initial position *is* the position of the last
block, and `DescriptiveComplexity.game_aux` answers directly.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Correct

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The assignment of the first block made of the two endpoints of the walk. -/
def endVal (S T : A → Prop) : QM A → Prop := fun y =>
  (∃ a : A, y = qVar .sS a (qBot A) ∧ S a) ∨ ∃ a : A, y = qVar .sT a (qBot A) ∧ T a

theorem stS_over_endVal (τ : QM A → Prop) (S T : A → Prop) {a : A} (ha : IsSV a) :
    stS (qOver (QBlk (tEnds A)) τ (endVal S T)) a ↔ S a := by
  refine (readout_in (v := .sS) τ _ ⟨ha, isBot_qBot A⟩ (by simp [tEnds])).trans ?_
  constructor
  · rintro (⟨a', he, hs⟩ | ⟨a', he, -⟩)
    · exact (qVar_inj he).2.1 ▸ hs
    · exact absurd (qVar_inj he).1 (by decide)
  · exact fun hs => Or.inl ⟨a, rfl, hs⟩

theorem stT_over_endVal (τ : QM A → Prop) (S T : A → Prop) {a : A} (ha : IsSV a) :
    stT (qOver (QBlk (tEnds A)) τ (endVal S T)) a ↔ T a := by
  refine (readout_in (v := .sT) τ _ ⟨ha, isBot_qBot A⟩ (by simp [tEnds])).trans ?_
  constructor
  · rintro (⟨a', he, -⟩ | ⟨a', he, ht⟩)
    · exact absurd (qVar_inj he).1 (by decide)
    · exact (qVar_inj he).2.1 ▸ ht
  · exact fun ht => Or.inr ⟨a, rfl, ht⟩

/-- With no state variable, the auxiliary block is the first one: every other
variable would need a state variable for one of its coordinates. -/
theorem qPlayed_tAux_of_isEmpty (h : ∀ x : A, ¬IsSV x) :
    QPlayed (tAux A) = fun _ : QM A => False := by
  funext x
  refine propext ⟨?_, False.elim⟩
  rintro ⟨v, p, q, -, hv, hlt⟩
  cases v <;> simp only [QVarOn] at hv
  · exact h p hv.1
  · exact h p hv.1
  · exact h p hv.1
  · exact h p hv.1
  · exact h p hv.1
  · exact h p hv.1
  · rw [keyTriple_aS, eq_qBot hv, tAux] at hlt
    exact tripleLt_irrefl _ hlt
  · rw [keyTriple_aT, eq_qBot hv, tAux] at hlt
    exact tripleLt_irrefl _ hlt
  · rw [keyTriple_aP, eq_qBot hv, tAux] at hlt
    exact tripleLt_irrefl _ hlt
  · rw [keyTriple_sE, eq_qBot hv.2, tAux] at hlt
    exact tripleLt_irrefl _ hlt

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- With no state variable, all states have the same class. -/
theorem stCls_subsingleton (h : ∀ x : A, ¬IsSV x) (S S' : A → Prop) :
    stCls S = stCls S' :=
  stCls_eq_iff.mpr fun x hx => absurd hx (h x)

/-- **Correctness of the Savitch reduction.** -/
theorem qsatHolds_iff : QsatHolds (QM A) ↔ SuccinctReachable A := by
  classical
  rw [succinctReachable_iff_savPow]
  have hwins : QsatHolds (QM A) ↔ QsatWins (QPlayed (tEnds A)) (fun _ : QM A => False) := by
    rw [QsatHolds, qPlayed_tEnds]
    exact ⟨fun h => h.2, fun h => ⟨qsatWf_qsatInterp, h⟩⟩
  rw [hwins]
  by_cases hsv : ∃ x : A, IsSV x
  · obtain ⟨x0, hx0⟩ := hsv
    obtain ⟨ℓ, hmin⟩ := exists_isMinSV hx0
    rw [qsatWins_block_ex qsatWf_qsatInterp (qDownClosed_qPlayed _) (qBlock_qBlk _)
      blk_ex_tEnds, step_ends hmin]
    have hlev : ∀ σ : QM A → Prop, LevBelow ℓ σ :=
      fun σ b w s ℓ'' x hl hlt _ => absurd hlt (hmin.2 ℓ'' hl)
    have hdepth : svAbove ℓ = stateDepth A := svAbove_of_isMinSV hmin
    simp only [game_level (svAbove ℓ) ℓ hmin.isSV le_rfl, inFst_of_isMinSV hmin,
      inSnd_of_isMinSV hmin, hdepth, iff_true_intro (hlev _), true_and]
    constructor
    · rintro ⟨νE, hs, hg, hsav⟩
      exact ⟨_, _, hs, hg, hsav⟩
    · rintro ⟨S, T, hs, hg, hsav⟩
      refine ⟨endVal S T, ?_, ?_, ?_⟩
      · exact isStart_congr (stCls_eq_iff.mpr fun x hx =>
          (stS_over_endVal _ S T hx).symm) hs
      · exact isGoal_congr (stCls_eq_iff.mpr fun x hx =>
          (stT_over_endVal _ S T hx).symm) hg
      · exact savPow_congr savInv_stepRel _
          (stCls_eq_iff.mpr fun x hx => (stS_over_endVal _ S T hx).symm)
          (stCls_eq_iff.mpr fun x hx => (stT_over_endVal _ S T hx).symm) hsav
  · have hempty : ∀ x : A, ¬IsSV x := fun x hx => hsv ⟨x, hx⟩
    have heq : QPlayed (tEnds A) = QPlayed (tAux A) := by
      rw [qPlayed_tEnds, qPlayed_tAux_of_isEmpty hempty]
    rw [heq, game_aux]
    constructor
    · rintro ⟨hs, hg, -, -⟩
      refine ⟨_, _, hs, hg, (savPow_iff_savLe savInv_stepRel _).mpr
        (savLe_of_le (Nat.zero_le _) (stCls_subsingleton hempty _ _))⟩
    · rintro ⟨S, T, hs, hg, -⟩
      refine ⟨isStart_congr (stCls_subsingleton hempty S _) hs,
        isGoal_congr (stCls_subsingleton hempty T _) hg,
        fun b w s ℓ'' x hl _ => absurd hl (hempty ℓ''), fun m hm => absurd hm.isSV (hempty m)⟩

end Correct

/-- **The Savitch reduction**, as an ordered first-order reduction. -/
noncomputable def succinctReach_ordered_fo_reduction_qsat : SUCCINCTREACH ≤ᶠᵒ[≤] QSAT where
  Tag := QTag
  dim := 2
  toInterpretation := qsatInterp
  correct := fun _ => qsatHolds_iff.symm

/-- **QSAT is PSPACE-hard**, by Savitch's recursive doubling from
SUCCINCT-REACH. -/
theorem qsat_PSPACE_hard : PSPACE.Hard QSAT :=
  PSPACE.hard_of_orderedReduction succinctReach_ordered_fo_reduction_qsat
    succinctReach_PSPACE_hard

/-- **QSAT is PSPACE-complete** ([Stockmeyer–Meyer 1973][stockmeyer1973word]). -/
theorem QSAT_PSPACE_complete : PSPACE.Complete QSAT :=
  ⟨qsat_mem_PSPACE, qsat_PSPACE_hard⟩

end DescriptiveComplexity
