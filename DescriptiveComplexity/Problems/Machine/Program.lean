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

/-- **Running a phase to the end of the tape.** The special case a reduction's
last phase needs: from `p₀` to the highest position, in `Nat.card - 1 - rank p₀`
steps. -/
theorem stepsIn_to_maxPos (hlin : IsLinOrd M.Le) {conf : A → Config A} {p₀ p₁ : A}
    (hp₀ : M.Posn p₀) (hp₁ : MaxPos M.Le M.Posn p₁)
    (hstep : ∀ p q, SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      M.Step (conf p) (conf q)) :
    M.StepsIn (Nat.card {p : A // M.Posn p} - 1 - bitRank M.Le M.Posn p₀)
      (conf p₀) (conf p₁) := by
  have hmax : bitRank M.Le M.Posn p₁ + 1 = Nat.card {p : A // M.Posn p} := bitRank_maxPos hp₁
  have := stepsIn_of_segment hlin hp₀ hstep p₁ hp₁.1 (hp₁.2 p₀ hp₀) (hlin.1 p₁)
  rwa [show Nat.card {p : A // M.Posn p} - 1 - bitRank M.Le M.Posn p₀ =
    bitRank M.Le M.Posn p₁ - bitRank M.Le M.Posn p₀ by omega]

/-- **A phase reaches acceptance.** Packaging the sweep as the acceptance of the
machine: a run from an initial configuration along the positions, ending in an
accepting state, accepts. This is the shape the `⇐` half of a reduction's
correctness proof needs. -/
theorem accepts_of_segment (hlin : IsLinOrd M.Le) {conf : A → Config A} {p₀ p : A}
    (hp₀ : MinPos M.Le M.Posn p₀) (hinit : M.IsInit (conf p₀)) (hp : M.Posn p)
    (hacc : M.Acc (conf p).state)
    (hstep : ∀ r q, SuccPos M.Le M.Posn r q → M.Le p₀ r → M.Le q p →
      M.Step (conf r) (conf q)) :
    M.Accepts := by
  refine ⟨conf p₀, conf p, bitRank M.Le M.Posn p - bitRank M.Le M.Posn p₀, hinit, ?_,
    stepsIn_of_segment hlin hp₀.1 hstep p hp (hp₀.2 p hp) (hlin.1 p), hacc⟩
  have := bitRank_lt_card (Le := M.Le) hp
  omega

end TMData

end DescriptiveComplexity
