/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax799700.Common
end Lax799700.Common

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax822549Proofs.DescriptiveComplexity.TMData
end Lax822549Proofs.DescriptiveComplexity.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (MaxPos)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos TMData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

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

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-- The rank of a position is monotone along the order. -/
theorem bitRank_le_of_le (hlin : Lax904597.Machines.IsLinOrd M.Le) {p q : A} (hp : M.Posn p)
    (hle : M.Le p q) : Lax799700.Common.bitRank M.Le M.Posn p ≤ Lax799700.Common.bitRank M.Le M.Posn q := by
  rcases eq_or_ne p q with rfl | hne
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (bitRank_lt hlin hp hle hne)

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (bitRank_le_of_le)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- Below a starting position there is no predecessor to fall off: a position
strictly above `p₀` is not the lowest one. -/
theorem not_minPos_of_lt (hlin : Lax904597.Machines.IsLinOrd M.Le) {p₀ p : A} (hp₀ : M.Posn p₀)
    (hle : M.Le p₀ p) (hne : p₀ ≠ p) : ¬ Lax904597.Machines.MinPos M.Le M.Posn p :=
  fun hmin => hne (hlin.2.2.1 p₀ p hle (hmin.2 p₀ hp₀))

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (not_minPos_of_lt)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **The successor of a position is unique.** `DescriptiveComplexity.succPos_left_unique`
gives the predecessor; a step of a machine needs this direction, since the head
moves to *the* neighbor in the direction the transition names. -/
theorem succPos_right_unique (hlin : Lax904597.Machines.IsLinOrd M.Le) {p q q' : A}
    (h : Lax904597.Machines.SuccPos M.Le M.Posn p q) (h' : Lax904597.Machines.SuccPos M.Le M.Posn p q') : q = q' := by
  rcases hlin.2.2.2 q q' with hle | hle
  · rcases h'.2.2.2.2 q h.2.1 h.2.2.1 hle with hcon | hcon
    · exact absurd hcon.symm h.2.2.2.1
    · exact hcon
  · rcases h.2.2.2.2 q' h'.2.1 h'.2.2.1 hle with hcon | hcon
    · exact absurd hcon.symm h'.2.2.2.1
    · exact hcon.symm

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (succPos_right_unique)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A machine takes at most one step wherever its transition is pinned.** The
same proof as `DescriptiveComplexity.TMData.step_functional`, with the clause
that names the transition asked for at *this* configuration only.

That is what a program which guesses in one phase has: everywhere but the guess,
the state and the symbol read name the transition, and the two remaining clauses
– that a transition has one destination and writes one symbol – hold outright.
Feed it to `DescriptiveComplexity.TMData.uniqueFrom_of_invariant`. -/
theorem step_functional_at (hlin : Lax904597.Machines.IsLinOrd M.Le)
    (hdstf : ∀ (τ q q' : A), M.Dst τ q → M.Dst τ q' → q = q')
    (hwritef : ∀ (τ a a' : A), M.Write τ a → M.Write τ a' → a = a')
    {c : Lax904597.Machines.Config A}
    (huniq : ∀ τ σ : A, M.Tr τ → M.Tr σ → M.Src τ c.state → M.Src σ c.state →
      M.Read τ (c.tape c.head) → M.Read σ (c.tape c.head) → τ = σ)
    {c₁ c₂ : Lax904597.Machines.Config A} (h₁ : M.Step c c₁) (h₂ : M.Step c c₂) : c₁ = c₂ := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h₁
  obtain ⟨σ, hσ, hsrc', hread', hdst', hwrite', hframe', hmove'⟩ := h₂
  obtain rfl := huniq τ σ hτ hσ hsrc hsrc' hread hread'
  refine Lax904597.Machines.Config.ext (hdstf τ _ _ hdst hdst') ?_ (funext fun p => ?_)
  · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩ <;> rcases hmove' with ⟨hr', hs'⟩ | ⟨hr', hs'⟩
    · exact succPos_right_unique hlin hs hs'
    · exact absurd hr hr'
    · exact absurd hr' hr
    · exact succPos_left_unique hlin hs hs'
  · rcases eq_or_ne p c.head with rfl | hne
    · exact hwritef τ _ _ hwrite hwrite'
    · rw [hframe p hne, hframe' p hne]

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (step_functional_at)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A deterministic machine takes at most one step** from any configuration:
the transition is pinned by the state and the symbol read, its effect by the
functionality of `Dst` and `Write`, and the new head by uniqueness of the
neighbor in the direction the transition names. -/
theorem step_functional (hlin : Lax904597.Machines.IsLinOrd M.Le) (hdet : M.Deterministic)
    {c c₁ c₂ : Lax904597.Machines.Config A} (h₁ : M.Step c c₁) (h₂ : M.Step c c₂) : c₁ = c₂ :=
  step_functional_at hlin hdet.2.2.1 hdet.2.2.2
    (fun τ σ hτ hσ hsrc hsrc' hread hread' =>
      hdet.2.1 τ σ _ _ hτ hσ hsrc hsrc' hread hread') h₁ h₂

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (step_functional)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **Deterministic runs of equal length agree**: the run is unique, which is
what lets a least fixed point compute it. -/
theorem stepsIn_functional (hlin : Lax904597.Machines.IsLinOrd M.Le) (hdet : M.Deterministic) :
    ∀ {n : ℕ} {c d d' : Lax904597.Machines.Config A}, M.StepsIn n c d → M.StepsIn n c d' → d = d' := by
  intro n
  induction n with
  | zero =>
    intro c d d' h h'
    exact (show c = d from h).symm.trans h'
  | succ n ih =>
    rintro c d d' ⟨e, he, hrest⟩ ⟨e', he', hrest'⟩
    obtain rfl := step_functional hlin hdet he he'
    exact ih hrest hrest'

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (stepsIn_functional)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-- Every position that is not the highest has one immediately above it – the
mirror of `DescriptiveComplexity.exists_predPos`, read in the reversed order. -/
theorem exists_succPos' (hlin : Lax904597.Machines.IsLinOrd M.Le) {p : A} (hp : M.Posn p)
    (hmax : ¬ Lax822549.WideTilings.MaxPos M.Le M.Posn p) : ∃ q, Lax904597.Machines.SuccPos M.Le M.Posn p q := by
  obtain ⟨q, hq⟩ := exists_predPos (Le := fun a b => M.Le b a) hlin.reverse hp hmax
  exact ⟨q, hq.2.1, hq.1, hq.2.2.1, fun h => hq.2.2.2.1 h.symm,
    fun r hr h₁ h₂ => (hq.2.2.2.2 r hr h₂ h₁).symm⟩

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (exists_succPos')

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-- **Running a phase leftwards.** The mirror of
`DescriptiveComplexity.TMData.stepsIn_of_segment`: when each consecutive pair of a
segment carries a step *downwards*, the machine walks from the top of the
segment to any position of it. The check sweeps of a reduction alternate
direction, so both readings are needed. -/
theorem stepsIn_of_segment_down (hlin : Lax904597.Machines.IsLinOrd M.Le) {conf : A → Lax904597.Machines.Config A} {p₀ p₁ : A}
    (hp₁ : M.Posn p₁)
    (hstep : ∀ p q, Lax904597.Machines.SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      M.Step (conf q) (conf p)) :
    ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      M.StepsIn (Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn p) (conf p₁) (conf p) := by
  have key : ∀ k : ℕ, ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn p = k →
      M.StepsIn (Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn p) (conf p₁) (conf p) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p hp hlb hub hrank
      rcases eq_or_ne p p₁ with rfl | hne
      · rw [Nat.sub_self]
        exact rfl
      · have hnmax : ¬ Lax822549.WideTilings.MaxPos M.Le M.Posn p := fun hmax =>
          hne (hlin.2.2.1 p p₁ hub (hmax.2 p₁ hp₁))
        obtain ⟨q, hq⟩ := exists_succPos' hlin hp hnmax
        have hq₁ : M.Le q p₁ := by
          rcases hlin.2.2.2 q p₁ with h | h
          · exact h
          · rcases hq.2.2.2.2 p₁ hp₁ hub h with h' | h'
            · exact absurd h'.symm hne
            · exact h' ▸ hlin.1 q
        have hrq : Lax799700.Common.bitRank M.Le M.Posn q = Lax799700.Common.bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hq
        have hmono : Lax799700.Common.bitRank M.Le M.Posn q ≤ Lax799700.Common.bitRank M.Le M.Posn p₁ :=
          bitRank_le_of_le hlin hq.2.1 hq₁
        have hrec := ih (Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn q) (by omega) q hq.2.1
          (hlin.2.1 p₀ p q hlb hq.2.2.1) hq₁ rfl
        have := hrec.trans_step (hstep p q hq hlb hq₁)
        rwa [show Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn q + 1 =
          Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn p by omega] at this
  exact fun p hp hlb hub => key _ p hp hlb hub rfl

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (stepsIn_of_segment_down)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-- **Running a phase.** If from `p₀` onwards every immediate successor of
positions carries a step of the machine, then the machine runs from `p₀` to any
later position, in exactly the number of steps their ranks differ by.

This is the sweep primitive: a reduction describes a phase by giving its
intended configuration at each position and discharging the single-step
obligation, with no induction of its own. -/
theorem stepsIn_of_segment (hlin : Lax904597.Machines.IsLinOrd M.Le) {conf : A → Lax904597.Machines.Config A} {p₀ p₁ : A}
    (hp₀ : M.Posn p₀)
    (hstep : ∀ p q, Lax904597.Machines.SuccPos M.Le M.Posn p q → M.Le p₀ p → M.Le q p₁ →
      M.Step (conf p) (conf q)) :
    ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ →
      M.StepsIn (Lax799700.Common.bitRank M.Le M.Posn p - Lax799700.Common.bitRank M.Le M.Posn p₀) (conf p₀) (conf p) := by
  have key : ∀ k : ℕ, ∀ p, M.Posn p → M.Le p₀ p → M.Le p p₁ → Lax799700.Common.bitRank M.Le M.Posn p = k →
      M.StepsIn (Lax799700.Common.bitRank M.Le M.Posn p - Lax799700.Common.bitRank M.Le M.Posn p₀) (conf p₀) (conf p) := by
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
        have hrq : Lax799700.Common.bitRank M.Le M.Posn p = Lax799700.Common.bitRank M.Le M.Posn q + 1 := bitRank_succPos hlin hq
        have hmono : Lax799700.Common.bitRank M.Le M.Posn p₀ ≤ Lax799700.Common.bitRank M.Le M.Posn q :=
          bitRank_le_of_le hlin hp₀ hq₀
        have hstep' := hstep q p hq hq₀ hub
        have hrec := ih (Lax799700.Common.bitRank M.Le M.Posn q) (by omega) q hq.1 hq₀ hq₁ rfl
        have := hrec.trans_step hstep'
        rwa [show Lax799700.Common.bitRank M.Le M.Posn q - Lax799700.Common.bitRank M.Le M.Posn p₀ + 1 =
          Lax799700.Common.bitRank M.Le M.Posn p - Lax799700.Common.bitRank M.Le M.Posn p₀ by omega] at this
  exact fun p hp hle hub => key _ p hp hle hub rfl

end TMData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax822549Proofs.DescriptiveComplexity.TMData (stepsIn_of_segment)

end Lax904597.Machines.TMData

namespace Lax822549Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

end TMData

end Lax822549Proofs.DescriptiveComplexity


