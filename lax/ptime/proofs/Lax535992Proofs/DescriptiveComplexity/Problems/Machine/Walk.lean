/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.Machines
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992Proofs.DescriptiveComplexity.TMData
end Lax535992Proofs.DescriptiveComplexity.TMData

namespace Lax535992Proofs.DescriptiveComplexity.TMData.RelWalk
end Lax535992Proofs.DescriptiveComplexity.TMData.RelWalk

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos TMData)
end Lax535992Proofs.DescriptiveComplexity

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

namespace Lax535992Proofs.DescriptiveComplexity

/-! ### The rank of a position -/

section Rank

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

omit [Finite A] in
/-- The lowest position has rank `0`. -/
theorem bitRank_eq_zero_of_minPos (hlin : Lax904597.Machines.IsLinOrd Le) {p : A} (h : Lax904597.Machines.MinPos Le Posn p) :
    bitRank Le Posn p = 0 := by
  have hempty : {r : A | Posn r ∧ Le r p ∧ r ≠ p} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hr hrp
    simp only [ne_eq, not_not]
    exact hlin.2.2.1 r p hrp (h.2 r hr)
  rw [bitRank, hempty, Set.ncard_empty]

/-- Rank increases by one along an immediate successor. -/
theorem bitRank_succPos (hlin : Lax904597.Machines.IsLinOrd Le) {p q : A} (h : Lax904597.Machines.SuccPos Le Posn p q) :
    bitRank Le Posn q = bitRank Le Posn p + 1 := by
  obtain ⟨hp, hq, hpq, hne, hbetween⟩ := h
  have hset : {r : A | Posn r ∧ Le r q ∧ r ≠ q} =
      insert p {r : A | Posn r ∧ Le r p ∧ r ≠ p} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
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
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
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

/-! ### The relational form of a walk

A first-order kernel cannot guess a *function* `A → Config A`; it guesses
relations. `DescriptiveComplexity.TMData.RelWalk` is the walk written with the three
relations a `Σ₁` block can supply – `Q t q`, “the state at time `t` is `q`”,
`H t p`, “the head is on `p`”, and `T t p a`, “the cell `p` holds `a`” – each
asserted to be functional, which is where the equivalence with a walk by
configurations is bought.

Every clause below is a literal transcription target for
`DescriptiveComplexity.Problems.Machine.Membership`: nothing here quantifies over
anything but elements of the universe. -/

section Relational

end Relational

end TMData

end Lax535992Proofs.DescriptiveComplexity


