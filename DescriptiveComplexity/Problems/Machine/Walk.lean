/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Machines

/-!
# A run is a walk along the positions

The one lemma both halves of the machine bridge consume,
`DescriptiveComplexity.TMData.accepts_iff_exists_walk`: acceptance – an `ℕ`-indexed run,
shorter than the number of positions – is equivalent to a family of
configurations *indexed by the position elements themselves*, in order.

This is where the unary time bound is cashed in. A first-order kernel cannot
talk about “the `n`-th step”; it can talk about “the configuration at time `t`”
for `t` ranging over the universe, related to “the configuration at time `t'`”
whenever `t'` is the immediate successor of `t`. `DescriptiveComplexity.TMData.IsWalk`
is exactly that, and it is what the `Σ₁` definition guesses.

The translation is by the rank of a position – `DescriptiveComplexity.bitRank`, the
number of positions strictly below it – which turns the walk into arithmetic:
rank `0` at the lowest position, `+1` along `DescriptiveComplexity.SuccPos`, and
`Nat.card - 1` at the highest. Those three facts are proved here first.

Because a stalled machine has no successor configuration, the walk allows a
*stutter* – but only in an accepting state, so that a walk that has accepted
stays accepted until the last position, where acceptance is read off.
-/

namespace DescriptiveComplexity

/-! ### The rank of a position -/

section Rank

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

omit [Finite A] in
/-- The lowest position has rank `0`. -/
theorem bitRank_eq_zero_of_minPos (hlin : IsLinOrd Le) {p : A} (h : MinPos Le Posn p) :
    bitRank Le Posn p = 0 := by
  have hempty : {r : A | Posn r ∧ Le r p ∧ r ≠ p} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hr hrp
    simp only [ne_eq, not_not]
    exact hlin.2.2.1 r p hrp (h.2 r hr)
  rw [bitRank, hempty, Set.ncard_empty]

/-- Rank increases by one along an immediate successor. -/
theorem bitRank_succPos (hlin : IsLinOrd Le) {p q : A} (h : SuccPos Le Posn p q) :
    bitRank Le Posn q = bitRank Le Posn p + 1 := by
  obtain ⟨hp, hq, hpq, hne, hbetween⟩ := h
  have hset : {r : A | Posn r ∧ Le r q ∧ r ≠ q} =
      insert p {r : A | Posn r ∧ Le r p ∧ r ≠ p} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hr, hrq, hrne⟩
      rcases hlin.2.2.2 r p with hrp | hpr
      · rcases eq_or_ne r p with rfl | hrpne
        · exact Or.inl rfl
        · exact Or.inr ⟨hr, hrp, hrpne⟩
      · rcases hbetween r hr hpr hrq with rfl | rfl
        · exact Or.inl rfl
        · exact absurd rfl hrne
    · rintro (rfl | ⟨hr, hrp, hrne⟩)
      · exact ⟨hp, hpq, hne⟩
      · refine ⟨hr, hlin.2.1 r p q hrp hpq, fun hcon => ?_⟩
        exact hne (hlin.2.2.1 p q hpq (hcon ▸ hrp))
  have hpmem : p ∉ {r : A | Posn r ∧ Le r p ∧ r ≠ p} := fun hmem => hmem.2.2 rfl
  rw [bitRank, hset, Set.ncard_insert_of_notMem hpmem (Set.toFinite _), bitRank]

/-- The rank of a position is below the number of positions. -/
theorem bitRank_lt_card {p : A} (hp : Posn p) :
    bitRank Le Posn p < Nat.card {x : A // Posn x} := by
  have hcard : Nat.card {x : A // Posn x} = ({x : A | Posn x} : Set A).ncard :=
    (Nat.card_coe_set_eq _)
  rw [hcard, bitRank]
  refine Set.ncard_lt_ncard ⟨fun r hr => hr.1, fun hsub => ?_⟩ (Set.toFinite _)
  exact absurd rfl (hsub hp).2.2

/-- The highest position has the greatest rank. -/
theorem bitRank_maxPos {p : A} (h : MaxPos Le Posn p) :
    bitRank Le Posn p + 1 = Nat.card {x : A // Posn x} := by
  have hcard : Nat.card {x : A // Posn x} = ({x : A | Posn x} : Set A).ncard :=
    (Nat.card_coe_set_eq _)
  have hset : ({x : A | Posn x} : Set A) = insert p {r : A | Posn r ∧ Le r p ∧ r ≠ p} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · intro hr
      rcases eq_or_ne r p with rfl | hrne
      · exact Or.inl rfl
      · exact Or.inr ⟨hr, h.2 r hr, hrne⟩
    · rintro (rfl | ⟨hr, -, -⟩)
      · exact h.1
      · exact hr
  have hpmem : p ∉ {r : A | Posn r ∧ Le r p ∧ r ≠ p} := fun hmem => hmem.2.2 rfl
  rw [hcard, hset, Set.ncard_insert_of_notMem hpmem (Set.toFinite _), bitRank]

end Rank

namespace TMData

variable {A : Type} (M : TMData A)

/-- **A run laid out along the positions**: a configuration for each position,
initial at the lowest, related by a step – or by a stutter in an accepting
state, for a machine that has already accepted – at each immediate successor,
and accepting at the highest. -/
def IsWalk (conf : A → Config A) : Prop :=
  (∀ p, MinPos M.Le M.Posn p → M.IsInit (conf p)) ∧
    (∀ p q, SuccPos M.Le M.Posn p q →
      M.Step (conf p) (conf q) ∨ (M.Acc (conf p).state ∧ conf q = conf p)) ∧
    ∀ p, MaxPos M.Le M.Posn p → M.Acc (conf p).state

variable {M}

/-- A run of `n` steps, presented as its sequence of configurations. -/
private theorem exists_run : ∀ (n : ℕ) (c d : Config A), M.StepsIn n c d →
    ∃ f : ℕ → Config A, f 0 = c ∧ f n = d ∧ ∀ i, i < n → M.Step (f i) (f (i + 1)) := by
  intro n
  induction n with
  | zero =>
    intro c d hcd
    exact ⟨fun _ => c, rfl, (show c = d from hcd), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    rintro c d ⟨e, hstep, hrest⟩
    obtain ⟨f, hf0, hfn, hfs⟩ := ih e d hrest
    refine ⟨fun i => Nat.rec c (fun j _ => f j) i, rfl, hfn, fun i hi => ?_⟩
    cases i with
    | zero => simpa [hf0] using hstep
    | succ j => exact hfs j (by omega)

/-- **Acceptance is a walk along the positions.** -/
theorem accepts_iff_exists_walk [Finite A] (hwf : M.WellFormed) :
    M.Accepts ↔ ∃ conf : A → Config A, M.IsWalk conf := by
  obtain ⟨hlin, hne, -⟩ := hwf
  obtain ⟨p₀, hp₀⟩ := exists_minPos hlin hne
  obtain ⟨p₁, hp₁⟩ := exists_maxPos hlin hne
  constructor
  · rintro ⟨c₀, c, n, hinit, hlt, hrun, hacc⟩
    obtain ⟨f, hf0, hfn, hfs⟩ := exists_run n c₀ c hrun
    refine ⟨fun p => f (min (bitRank M.Le M.Posn p) n), fun p hp => ?_, fun p q hpq => ?_,
      fun p hp => ?_⟩
    · dsimp only
      rw [bitRank_eq_zero_of_minPos hlin hp, Nat.zero_min, hf0]
      exact hinit
    · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
      dsimp only
      rcases lt_or_ge (bitRank M.Le M.Posn p) n with hcase | hcase
      · refine Or.inl ?_
        rw [hrq, min_eq_left (by omega), min_eq_left (by omega)]
        exact hfs _ hcase
      · refine Or.inr ⟨?_, ?_⟩ <;>
          rw [min_eq_right hcase] <;> [rw [hfn]; rw [hrq, min_eq_right (by omega), hfn]]
        · exact hacc
    · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
        bitRank_maxPos hp
      dsimp only
      rw [min_eq_right (by omega), hfn]
      exact hacc
  · rintro ⟨conf, hinit, hstep, haccept⟩
    have key : ∀ k : ℕ, ∀ p, M.Posn p → bitRank M.Le M.Posn p = k →
        ∃ n ≤ k, M.StepsIn n (conf p₀) (conf p) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro p hp hrank
        by_cases hmin : MinPos M.Le M.Posn p
        · have hpp : p = p₀ := hlin.2.2.1 p p₀ (hmin.2 p₀ hp₀.1) (hp₀.2 p hp)
          exact ⟨0, Nat.zero_le _, by rw [hpp]; rfl⟩
        · obtain ⟨q, hq⟩ := exists_predPos hlin hp hmin
          have hrq : bitRank M.Le M.Posn q + 1 = k := by
            rw [← hrank, bitRank_succPos hlin hq]
          obtain ⟨n, hn, hsteps⟩ := ih (bitRank M.Le M.Posn q) (by omega) q hq.1 rfl
          rcases hstep q p hq with hs | ⟨-, heq⟩
          · exact ⟨n + 1, by omega, hsteps.trans_step hs⟩
          · exact ⟨n, by omega, heq ▸ hsteps⟩
    obtain ⟨n, hn, hsteps⟩ := key _ p₁ hp₁.1 rfl
    have hmax : bitRank M.Le M.Posn p₁ + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp₁
    exact ⟨conf p₀, conf p₁, n, hinit p₀ hp₀, by omega, hsteps, haccept p₁ hp₁⟩

end TMData

end DescriptiveComplexity
