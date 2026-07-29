/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltRank

/-!
# Splicing a play into a walk

The direction `DescriptiveComplexity.Problems.Machine.AltRank` does not cover:
turning a play of block `i` into the walk a round of the game has to produce.
`DescriptiveComplexity.ATMData.splice` follows the previous round's walk up to
the entry time `t`, replays the given play from there, and then stands still.

Standing still is legitimate because
`DescriptiveComplexity.ATMData.LegalBelow` asks a round's walk for nothing once
it has handed over: if the play ends in block `i + 1` there is no obligation at
all, and if it ends *inside* block `i` then it ended by accepting or by getting
stuck, and stuttering there is exactly what a walk is allowed to do. That is
the hypothesis `hend` of
`DescriptiveComplexity.ATMData.roundCond_splice`, and it is the only thing the
construction needs to know about how the play stopped.

The proof is three cases, cut by comparing the rank of a position with the rank
of `t`: strictly below it the walk is the previous one, at it the play starts,
above it the play runs and then repeats. Nothing else about the order is
involved, which is why the file is short.
-/

namespace DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : ATMData A} {k : ℕ}

open Classical in
/-- **The walk following `prev` up to `t` and the play `f` after it**, standing
still once the play is over. -/
noncomputable def splice (M : ATMData A) (prev : A → Config A) (t : A) (ℓ : ℕ)
    (f : ℕ → Config A) : A → Config A := fun x =>
  if M.Posn x ∧ ¬M.Le x t then
    f (min (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t) ℓ)
  else prev x

section Splice

variable (hlin : IsLinOrd M.Le) {prev : A → Config A} {t : A} {ℓ : ℕ} {f : ℕ → Config A}

omit [Finite A] in
/-- Below the entry time the spliced walk is the previous one. -/
theorem splice_of_le {x : A} (h : ¬(M.Posn x ∧ ¬M.Le x t)) :
    M.splice prev t ℓ f x = prev x := by
  classical
  rw [splice, if_neg h]

omit [Finite A] in
include hlin in
/-- Above the entry time the spliced walk replays the play. -/
theorem splice_of_lt {x : A} (hx : M.Posn x) (ht : M.Posn t) (hle : M.Le t x)
    (h0 : prev t = f 0) :
    M.splice prev t ℓ f x =
      f (min (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t) ℓ) := by
  classical
  rcases eq_or_ne x t with rfl | hne
  · rw [splice, if_neg (fun h => h.2 (hlin.1 x)), Nat.sub_self, h0]
    simp
  · have hnle : ¬M.Le x t := fun hcon => hne (hlin.2.2.1 x t hcon hle)
    rw [splice, if_pos ⟨hx, hnle⟩]

include hlin in
/-- The spliced walk at the `j`-th position after `t`. -/
theorem splice_posSeq {p₁ : A} (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁)
    (h0 : prev t = f 0) {j : ℕ}
    (hj : j ≤ bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t) :
    M.splice prev t ℓ f (M.posSeq t j) = f (min j ℓ) := by
  obtain ⟨hp, hr⟩ := posSeq_spec hlin ht hmax j hj
  rw [splice_of_lt hlin hp ht (le_of_bitRank_le hlin ht hp (by omega)) h0, hr]
  simp

end Splice

/-! ### The spliced walk is an admissible move -/

/-- **Splicing a play into the previous round's walk produces an admissible
move for round `i`.** The hypotheses say that `t` is the entry into block `i`
(everything strictly below it is in a lower block, and `prev` is legal there),
that `f` is a play of block `i` from the entry configuration, and that if the
play stopped early inside its own block it stopped by accepting or by getting
stuck. -/
theorem roundCond_splice (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le) {i : ℕ}
    {prev : A → Config A} (hprev : M.LegalBelow i prev) {t p₁ : A}
    (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁) (hti : M.Blk i (prev t).state)
    (hpast : ∀ s, M.Posn s → M.Le s t → s ≠ t → M.BlkLt i (prev s).state)
    {ℓ : ℕ} {f : ℕ → Config A}
    (hℓ : ℓ ≤ bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t)
    (hplay : M.BlockPlay i (prev t) ℓ f)
    (hend : ℓ < bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn t →
      M.BlkLt (i + 1) (f ℓ).state → M.Acc (f ℓ).state ∨ M.Stuck (f ℓ)) :
    M.RoundCond i prev (M.splice prev t ℓ f) := by
  classical
  set w := M.splice prev t ℓ f with hw
  have h0 : prev t = f 0 := hplay.1.symm
  have hbound : ∀ x, M.Posn x → bitRank M.Le M.Posn x ≤ bitRank M.Le M.Posn p₁ := fun x hx =>
    TMData.bitRank_le_of_le (M := M.toTMData) hlin hx (hmax.2 x hx)
  have hreadlow : ∀ x, M.Posn x → M.Le x t → w x = prev x := fun x hx hle =>
    splice_of_le fun hcon => hcon.2 hle
  have hread : ∀ x, M.Posn x → M.Le t x →
      w x = f (min (bitRank M.Le M.Posn x - bitRank M.Le M.Posn t) ℓ) := fun x hx hle =>
    splice_of_lt hlin hx ht hle h0
  -- the low blocks of `prev` are exactly the times strictly below `t`
  have hlow : ∀ x, M.Posn x → M.BlkLt i (prev x).state → M.Le x t ∧ x ≠ t := by
    intro x hx hbx
    have hne : x ≠ t := by
      rintro rfl
      exact ((blkLt_iff hbwf hti).mp hbx).false
    refine ⟨?_, hne⟩
    by_contra hcon
    have hle : M.Le t x := (hlin.2.2.2 t x).resolve_right hcon
    exact ((blkLt_iff hbwf hti).mp (blkLt_of_le hbwf hlin hprev.2.1 ht hx hle hbx)).false
  -- the step obligation, at a pair of consecutive positions
  have hstep : ∀ p q, SuccPos M.Le M.Posn p q →
      (M.Step (w p) (w q) ∧ ¬M.Acc (w p).state) ∨
        (w q = w p ∧ (M.BlkLt (i + 1) (w p).state →
          M.Acc (w p).state ∨ M.Stuck (w p))) := by
    intro p q hpq
    have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    have hqb := hbound q hpq.2.1
    by_cases hpt : p = t
    · -- the entry itself: the play starts here
      subst hpt
      rw [hreadlow p hpq.1 (hlin.1 p), h0,
        hread q hpq.2.1 hpq.2.2.1, hrq, Nat.add_sub_cancel_left]
      rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
      · exact Or.inr ⟨by simp, fun _ =>
          hend (by omega) ⟨i, Nat.lt_succ_self i, by rw [← h0]; exact hti⟩⟩
      · rw [Nat.min_eq_left hpos]
        exact Or.inl ⟨hplay.2.1 0 hpos, (hplay.2.2 0 hpos).2⟩
    · by_cases hple : M.Le p t
      · -- strictly below the entry: the previous walk answers
        have hlt : bitRank M.Le M.Posn p < bitRank M.Le M.Posn t := bitRank_lt hlin hpq.1 hple hpt
        have hqle : M.Le q t := le_of_bitRank_le hlin hpq.2.1 ht (by omega)
        rw [hreadlow p hpq.1 hple, hreadlow q hpq.2.1 hqle]
        exact (hprev.2.2 p q hpq (hpast p hpq.1 hple hpt)).imp id fun h => ⟨h.1, fun _ => h.2⟩
      · -- above the entry: the play answers, then repeats
        have htp : M.Le t p := (hlin.2.2.2 t p).resolve_right hple
        have hlt : bitRank M.Le M.Posn t < bitRank M.Le M.Posn p :=
          bitRank_lt hlin ht htp fun hcon => hpt hcon.symm
        rw [hread p hpq.1 htp, hread q hpq.2.1 (hlin.2.1 t p q htp hpq.2.2.1), hrq,
          show bitRank M.Le M.Posn p + 1 - bitRank M.Le M.Posn t =
            (bitRank M.Le M.Posn p - bitRank M.Le M.Posn t) + 1 by omega]
        rcases Nat.lt_or_ge (bitRank M.Le M.Posn p - bitRank M.Le M.Posn t) ℓ with hin | hout
        · rw [Nat.min_eq_left (Nat.le_of_lt hin), Nat.min_eq_left hin]
          exact Or.inl ⟨hplay.2.1 _ hin, (hplay.2.2 _ hin).2⟩
        · rw [Nat.min_eq_right hout, Nat.min_eq_right (by omega)]
          exact Or.inr ⟨rfl, fun hb => hend (by omega) hb⟩
  refine ⟨⟨fun p hp => ?_, fun p q hpq j j' hj hj' => ?_,
      fun p q hpq hblk => (hstep p q hpq).imp id fun h => ⟨h.1, h.2 hblk⟩⟩,
    fun x hx hbx => ?_, fun x y hxy hbx => ?_⟩
  · rw [hreadlow p hp.1 (hp.2 t ht)]
    exact hprev.1 p hp
  · rcases hstep p q hpq with ⟨hs, -⟩ | ⟨heq, -⟩
    · rcases blk_step hbwf hs hj with h | h
      · exact Nat.le_of_eq (blk_unique hbwf hj' h).symm
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
          (Nat.le_of_eq (blk_unique hbwf h hj')))
    · rw [heq] at hj'
      exact Nat.le_of_eq (blk_unique hbwf hj hj')
  · exact hreadlow x hx (hlow x hx hbx).1
  · obtain ⟨hle, hne⟩ := hlow x hxy.1 hbx
    have hlt : bitRank M.Le M.Posn x < bitRank M.Le M.Posn t := bitRank_lt hlin hxy.1 hle hne
    have hrq : bitRank M.Le M.Posn y = bitRank M.Le M.Posn x + 1 := bitRank_succPos hlin hxy
    exact hreadlow y hxy.2.1 (le_of_bitRank_le hlin hxy.2.1 ht (by omega))

/-! ### Every initial configuration extends to a walk

A round cannot be asked for a move it cannot make, and the universal rounds of
the game are guarded by an existence clause
(`DescriptiveComplexity.guardQ`); so the game needs to know that a legal walk
exists at all. It does: step while a step is available, and stand still
otherwise, which is legal because standing still in a *stuck* configuration is
allowed. -/

open Classical in
/-- The greedy continuation of a configuration: step while a step is available,
and stand still once stuck. -/
noncomputable def greedy (M : ATMData A) (c₀ : Config A) : ℕ → Config A
  | 0 => c₀
  | j + 1 =>
      if M.Acc (M.greedy c₀ j).state then M.greedy c₀ j
      else if h : ∃ d, M.Step (M.greedy c₀ j) d then h.choose else M.greedy c₀ j

omit [Finite A] in
/-- One greedy move is a step, or standing still in a stuck configuration. -/
theorem greedy_step (M : ATMData A) (c₀ : Config A) (j : ℕ) :
    (M.Step (M.greedy c₀ j) (M.greedy c₀ (j + 1)) ∧ ¬M.Acc (M.greedy c₀ j).state) ∨
      (M.greedy c₀ (j + 1) = M.greedy c₀ j ∧
        (M.Acc (M.greedy c₀ j).state ∨ M.Stuck (M.greedy c₀ j))) := by
  classical
  by_cases hacc : M.Acc (M.greedy c₀ j).state
  · exact Or.inr ⟨by rw [greedy, if_pos hacc], Or.inl hacc⟩
  by_cases h : ∃ d, M.Step (M.greedy c₀ j) d
  · refine Or.inl ⟨?_, hacc⟩
    rw [greedy, if_neg hacc, dif_pos h]
    exact h.choose_spec
  · exact Or.inr ⟨by rw [greedy, if_neg hacc, dif_neg h],
      Or.inr fun d hd => h ⟨d, hd⟩⟩

/-- The walk that runs the greedy continuation along the positions. -/
noncomputable def greedyWalk (M : ATMData A) (c₀ : Config A) : A → Config A :=
  fun x => M.greedy c₀ (bitRank M.Le M.Posn x)

/-- **Every initial configuration extends to a walk legal below any block.** -/
theorem legalBelow_greedyWalk (hbwf : M.BlocksWellFormed k) (hlin : IsLinOrd M.Le)
    {c₀ : Config A} (hinit : M.IsInit c₀) (i : ℕ) :
    M.LegalBelow i (M.greedyWalk c₀) ∧
      ∀ p, MinPos M.Le M.Posn p → M.greedyWalk c₀ p = c₀ := by
  have hmin : ∀ p, MinPos M.Le M.Posn p → M.greedyWalk c₀ p = c₀ := by
    intro p hp
    rw [greedyWalk, bitRank_eq_zero_of_minPos hlin hp]
    rfl
  have hstep : ∀ p q, SuccPos M.Le M.Posn p q →
      (M.Step (M.greedyWalk c₀ p) (M.greedyWalk c₀ q) ∧
          ¬M.Acc (M.greedyWalk c₀ p).state) ∨
        (M.greedyWalk c₀ q = M.greedyWalk c₀ p ∧
          (M.Acc (M.greedyWalk c₀ p).state ∨ M.Stuck (M.greedyWalk c₀ p))) := by
    intro p q hpq
    have hr : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    rw [greedyWalk, greedyWalk, hr]
    exact greedy_step M c₀ _
  refine ⟨⟨fun p hp => by rw [hmin p hp]; exact hinit, fun p q hpq j j' hj hj' => ?_,
    fun p q hpq _ => hstep p q hpq⟩, hmin⟩
  rcases hstep p q hpq with ⟨hs, -⟩ | ⟨heq, -⟩
  · rcases blk_step hbwf hs hj with h | h
    · exact Nat.le_of_eq (blk_unique hbwf hj' h).symm
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
        (Nat.le_of_eq (blk_unique hbwf h hj')))
  · rw [heq] at hj'
    exact Nat.le_of_eq (blk_unique hbwf hj hj')

end ATMData

end DescriptiveComplexity
