/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Walk

/-!
# Running a phase of a machine

The reusable half of the hardness reductions. A machine built by a reduction
runs in *phases*, each of which sweeps along a stretch of the positions doing
the same thing at every cell: the guess phase of `SAT ≤ᶠᵒ[≤] NTMAccept` writes a
truth value at each variable cell, the check phase folds a flag over them, the
propagation phase of `HORNSAT ≤ᶠᵒ[≤] DTMAccept` marks variables. Reasoning about
such a phase should not require redoing an induction along the order each time.

`DescriptiveComplexity.TMData.stepsIn_of_segment` is that induction, done once: given a
family of configurations indexed by the positions and a step between each
consecutive pair *of a segment* `[p₀, p₁]`, the machine walks from `p₀` to any
position of the segment, in exactly as many steps as their ranks differ. The
segment is bounded at both ends because a phase stops – at a marker, or where
the next phase begins – and the transitions that carry it need not exist
beyond.
A phase is then described by exhibiting its intended configuration at each
position and checking a single step, which is a statement about the transition
table rather than about runs.

The count is `DescriptiveComplexity.bitRank` – the number of positions strictly below
a given one – so phases compose by arithmetic on ranks: sweeping `[p₀, p₁]` and
then `[p₁, p₂]` takes `(rank p₁ - rank p₀) + (rank p₂ - rank p₁)` steps, and the
budget obligation of the reduction is a comparison of ranks with
`Nat.card {p // Posn p}`.
-/

namespace DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : TMData A}

/-- The rank of a position is monotone along the order. -/
theorem bitRank_le_of_le (hlin : IsLinOrd M.Le) {p q : A} (hp : M.Posn p)
    (hle : M.Le p q) : bitRank M.Le M.Posn p ≤ bitRank M.Le M.Posn q := by
  rcases eq_or_ne p q with rfl | hne
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (bitRank_lt hlin hp hle hne)

omit [Finite A] in
/-- Below a starting position there is no predecessor to fall off: a position
strictly above `p₀` is not the lowest one. -/
private theorem not_minPos_of_lt (hlin : IsLinOrd M.Le) {p₀ p : A} (hp₀ : M.Posn p₀)
    (hle : M.Le p₀ p) (hne : p₀ ≠ p) : ¬ MinPos M.Le M.Posn p :=
  fun hmin => hne (hlin.2.2.1 p₀ p hle (hmin.2 p₀ hp₀))

omit [Finite A] in
/-- **The successor of a position is unique.** `DescriptiveComplexity.succPos_left_unique`
gives the predecessor; a step of a machine needs this direction, since the head
moves to *the* neighbour in the direction the transition names. -/
theorem succPos_right_unique (hlin : IsLinOrd M.Le) {p q q' : A}
    (h : SuccPos M.Le M.Posn p q) (h' : SuccPos M.Le M.Posn p q') : q = q' := by
  rcases hlin.2.2.2 q q' with hle | hle
  · rcases h'.2.2.2.2 q h.2.1 h.2.2.1 hle with hcon | hcon
    · exact absurd hcon.symm h.2.2.2.1
    · exact hcon
  · rcases h.2.2.2.2 q' h'.2.1 h'.2.2.1 hle with hcon | hcon
    · exact absurd hcon.symm h'.2.2.2.1
    · exact hcon.symm

omit [Finite A] in
/-- **A machine takes at most one step wherever its transition is pinned.** The
same proof as `DescriptiveComplexity.TMData.step_functional`, with the clause
that names the transition asked for at *this* configuration only.

That is what a program which guesses in one phase has: everywhere but the guess,
the state and the symbol read name the transition, and the two remaining clauses
– that a transition has one destination and writes one symbol – hold outright.
Feed it to `DescriptiveComplexity.TMData.uniqueFrom_of_invariant`. -/
theorem step_functional_at (hlin : IsLinOrd M.Le)
    (hdstf : ∀ (τ q q' : A), M.Dst τ q → M.Dst τ q' → q = q')
    (hwritef : ∀ (τ a a' : A), M.Write τ a → M.Write τ a' → a = a')
    {c : Config A}
    (huniq : ∀ τ σ : A, M.Tr τ → M.Tr σ → M.Src τ c.state → M.Src σ c.state →
      M.Read τ (c.tape c.head) → M.Read σ (c.tape c.head) → τ = σ)
    {c₁ c₂ : Config A} (h₁ : M.Step c c₁) (h₂ : M.Step c c₂) : c₁ = c₂ := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h₁
  obtain ⟨σ, hσ, hsrc', hread', hdst', hwrite', hframe', hmove'⟩ := h₂
  obtain rfl := huniq τ σ hτ hσ hsrc hsrc' hread hread'
  refine Config.ext (hdstf τ _ _ hdst hdst') ?_ (funext fun p => ?_)
  · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩ <;> rcases hmove' with ⟨hr', hs'⟩ | ⟨hr', hs'⟩
    · exact succPos_right_unique hlin hs hs'
    · exact absurd hr hr'
    · exact absurd hr' hr
    · exact succPos_left_unique hlin hs hs'
  · rcases eq_or_ne p c.head with rfl | hne
    · exact hwritef τ _ _ hwrite hwrite'
    · rw [hframe p hne, hframe' p hne]

omit [Finite A] in
/-- **A deterministic machine takes at most one step** from any configuration:
the transition is pinned by the state and the symbol read, its effect by the
functionality of `Dst` and `Write`, and the new head by uniqueness of the
neighbour in the direction the transition names. -/
theorem step_functional (hlin : IsLinOrd M.Le) (hdet : M.Deterministic)
    {c c₁ c₂ : Config A} (h₁ : M.Step c c₁) (h₂ : M.Step c c₂) : c₁ = c₂ :=
  step_functional_at hlin hdet.2.2.1 hdet.2.2.2
    (fun τ σ hτ hσ hsrc hsrc' hread hread' =>
      hdet.2.1 τ σ _ _ hτ hσ hsrc hsrc' hread hread') h₁ h₂

omit [Finite A] in
/-- **Deterministic runs of equal length agree**: the run is unique, which is
what lets a least fixed point compute it. -/
theorem stepsIn_functional (hlin : IsLinOrd M.Le) (hdet : M.Deterministic) :
    ∀ {n : ℕ} {c d d' : Config A}, M.StepsIn n c d → M.StepsIn n c d' → d = d' := by
  intro n
  induction n with
  | zero =>
    intro c d d' h h'
    exact (show c = d from h).symm.trans h'
  | succ n ih =>
    rintro c d d' ⟨e, he, hrest⟩ ⟨e', he', hrest'⟩
    obtain rfl := step_functional hlin hdet he he'
    exact ih hrest hrest'

/-- Every position that is not the highest has one immediately above it – the
mirror of `DescriptiveComplexity.exists_predPos`, read in the reversed order. -/
theorem exists_succPos' (hlin : IsLinOrd M.Le) {p : A} (hp : M.Posn p)
    (hmax : ¬ MaxPos M.Le M.Posn p) : ∃ q, SuccPos M.Le M.Posn p q := by
  obtain ⟨q, hq⟩ := exists_predPos (Le := fun a b => M.Le b a) hlin.reverse hp hmax
  exact ⟨q, hq.2.1, hq.1, hq.2.2.1, fun h => hq.2.2.2.1 h.symm,
    fun r hr h₁ h₂ => (hq.2.2.2.2 r hr h₂ h₁).symm⟩

/-- **Running a phase leftwards.** The mirror of
`DescriptiveComplexity.TMData.stepsIn_of_segment`: when each consecutive pair of a
segment carries a step *downwards*, the machine walks from the top of the
segment to any position of it. The check sweeps of a reduction alternate
direction, so both readings are needed. -/
theorem stepsIn_of_segment_down (hlin : IsLinOrd M.Le) {conf : A → Config A} {p₀ p₁ : A}
    (hp₁ : M.Posn p₁)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      M.Step (conf q) (conf p)) :
    ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      M.StepsIn (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p) (conf p₁) (conf p) := by
  have key : ∀ k : ℕ, ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p = k →
      M.StepsIn (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p) (conf p₁) (conf p) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p hp hlb hub hrank
      rcases eq_or_ne p p₁ with rfl | hne
      · rw [Nat.sub_self]
        exact rfl
      · have hnmax : ¬ MaxPos M.Le M.Posn p := fun hmax =>
          hne (hlin.2.2.1 p p₁ hub (hmax.2 p₁ hp₁))
        obtain ⟨q, hq⟩ := exists_succPos' hlin hp hnmax
        have hq₁ : M.Le q p₁ := by
          rcases hlin.2.2.2 q p₁ with h | h
          · exact h
          · rcases hq.2.2.2.2 p₁ hp₁ hub h with h' | h'
            · exact absurd h'.symm hne
            · exact h' ▸ hlin.1 q
        have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn q ≤ bitRank M.Le M.Posn p₁ :=
          bitRank_le_of_le hlin hq.2.1 hq₁
        have hrec := ih (bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q) (by omega) q hq.2.1
          (hlin.2.1 p₀ p q hlb hq.2.2.1) hq₁ rfl
        have := hrec.trans_step (hstep p q hq hlb hq₁)
        rwa [show bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn q + 1 =
          bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p by omega] at this
  exact fun p hp hlb hub => key _ p hp hlb hub rfl

/-- **Running a phase.** If from `p₀` onwards every immediate successor of
positions carries a step of the machine, then the machine runs from `p₀` to any
later position, in exactly the number of steps their ranks differ by.

This is the sweep primitive: a reduction describes a phase by giving its
intended configuration at each position and discharging the single-step
obligation, with no induction of its own. -/
theorem stepsIn_of_segment (hlin : IsLinOrd M.Le) {conf : A → Config A} {p₀ p₁ : A}
    (hp₀ : M.Posn p₀)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      M.Step (conf p) (conf q)) :
    ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      M.StepsIn (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀) (conf p₀) (conf p) := by
  have key : ∀ k : ℕ, ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ → bitRank M.Le M.Posn p = k →
      M.StepsIn (bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀) (conf p₀) (conf p) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p hp hle hub hrank
      rcases eq_or_ne p₀ p with rfl | hne
      · rw [Nat.sub_self]
        exact rfl
      · obtain ⟨q, hq⟩ := exists_predPos hlin hp (not_minPos_of_lt hlin hp₀ hle hne)
        -- the predecessor of `p` is still at or above `p₀`, and still below `p₁`
        have hq₀ : M.Le p₀ q := by
          rcases hlin.2.2.2 p₀ q with h | h
          · exact h
          · rcases hq.2.2.2.2 p₀ hp₀ h hle with h' | h'
            · exact h' ▸ hlin.1 p₀
            · exact absurd h' hne
        have hq₁ : M.Le q p₁ := hlin.2.1 q p p₁ hq.2.2.1 hub
        have hrq : bitRank M.Le M.Posn p = bitRank M.Le M.Posn q + 1 := bitRank_succPos hlin hq
        have hmono : bitRank M.Le M.Posn p₀ ≤ bitRank M.Le M.Posn q :=
          bitRank_le_of_le hlin hp₀ hq₀
        have hstep' := hstep q p hq hq₀ hub
        have hrec := ih (bitRank M.Le M.Posn q) (by omega) q hq.1 hq₀ hq₁ rfl
        have := hrec.trans_step hstep'
        rwa [show bitRank M.Le M.Posn q - bitRank M.Le M.Posn p₀ + 1 =
          bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀ by omega] at this
  exact fun p hp hle hub => key _ p hp hle hub rfl

end TMData

end DescriptiveComplexity
