/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltGame
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax564036Proofs.DescriptiveComplexity.ATMData
end Lax564036Proofs.DescriptiveComplexity.ATMData

namespace Lax564036Proofs.DescriptiveComplexity.ATMData.BlockPlay
end Lax564036Proofs.DescriptiveComplexity.ATMData.BlockPlay

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd SuccPos)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax564036Proofs.DescriptiveComplexity

/-!
# Walking the positions, and reading a play off a walk

The bookkeeping between the two shapes a round of the game comes in: a *walk*,
one configuration per position, which is what a second-order block guesses, and
a *play* (`DescriptiveComplexity.ATMData.BlockPlay`), an `ℕ`-indexed sequence of
steps, which is what the collapse lemmas of
`DescriptiveComplexity.MachinesAltPlay` speak about. Translating between them
is arithmetic on `DescriptiveComplexity.bitRank`, exactly as
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` cashes in the unary time
bound of the nondeterministic bridge.

## The order facts

The rank is injective on positions
(`DescriptiveComplexity.ATMData.bitRank_inj`), so a position is the highest one
exactly when its rank is (`DescriptiveComplexity.ATMData.maxPos_iff_rank`), and
comparing ranks compares positions
(`DescriptiveComplexity.ATMData.le_of_bitRank_le`). Iterating
`DescriptiveComplexity.ATMData.nextPos` from a position therefore enumerates
the positions above it in order, its rank going up by one each time
(`DescriptiveComplexity.ATMData.posSeq_spec`), until the highest is reached –
which is where the *budget* of a configuration comes from: from the position
`t` there are exactly `rank p₁ - rank t` steps left.

## Reading a play

`DescriptiveComplexity.ATMData.exists_play_of_legalBelow` is the one theorem
here: from a walk legal below `i + 1` and a position `t` whose configuration is
in block `i`, the configurations at `t`, `nextPos t` … form a play of block
`i`, stopped at the first moment the walk leaves the block, accepts, gets
stuck, or runs out of budget. Those four alternatives are exactly the cases the
two collapse lemmas distinguish, so this is the whole interface the round
induction needs in that direction.
-/

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### Ranks and positions -/

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- **The rank is injective on positions.** -/
theorem bitRank_inj {x y : A} (hx : M.Posn x) (hy : M.Posn y)
    (h : Lax799700.Common.bitRank M.Le M.Posn x = Lax799700.Common.bitRank M.Le M.Posn y) : x = y := by
  rcases hlin.2.2.2 x y with hle | hle
  · rcases eq_or_ne x y with rfl | hne
    · rfl
    · exact absurd h (Nat.ne_of_lt (bitRank_lt hlin hx hle hne))
  · rcases eq_or_ne y x with rfl | hne
    · rfl
    · exact absurd h.symm (Nat.ne_of_lt (bitRank_lt hlin hy hle hne))

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (bitRank_inj)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- **Comparing ranks compares positions.** -/
theorem le_of_bitRank_le {x y : A} (hx : M.Posn x) (hy : M.Posn y)
    (h : Lax799700.Common.bitRank M.Le M.Posn x ≤ Lax799700.Common.bitRank M.Le M.Posn y) : M.Le x y := by
  rcases hlin.2.2.2 x y with hle | hle
  · exact hle
  · rcases eq_or_ne y x with rfl | hne
    · exact hlin.1 _
    · exact absurd (bitRank_lt hlin hy hle hne) (by omega)

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (le_of_bitRank_le)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- **A position is the highest one exactly when its rank is.** -/
theorem maxPos_iff_rank {x p₁ : A} (hx : M.Posn x) (hmax : MaxPos M.Le M.Posn p₁) :
    MaxPos M.Le M.Posn x ↔ Lax799700.Common.bitRank M.Le M.Posn x = Lax799700.Common.bitRank M.Le M.Posn p₁ := by
  constructor
  · intro h
    exact congrArg _ (hlin.2.2.1 x p₁ (hmax.2 x hx) (h.2 p₁ hmax.1))
  · intro h
    exact bitRank_inj hlin hx hmax.1 h ▸ hmax

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (maxPos_iff_rank)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- **Iterating `nextPos` enumerates the positions above `t` in order**: the
`j`-th one is a position of rank `rank t + j`, as long as the budget
`rank p₁ - rank t` has not run out. -/
theorem posSeq_spec {t p₁ : A} (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁) :
    ∀ j, j ≤ Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn t →
      M.Posn (M.posSeq t j) ∧
        Lax799700.Common.bitRank M.Le M.Posn (M.posSeq t j) = Lax799700.Common.bitRank M.Le M.Posn t + j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨ht, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨hp, hr⟩ := ih (by omega)
    have hrp₁ : Lax799700.Common.bitRank M.Le M.Posn t ≤ Lax799700.Common.bitRank M.Le M.Posn p₁ :=
      TMData.bitRank_le_of_le (M := M.toTMData) hlin ht (hmax.2 t ht)
    have hnmax : ¬MaxPos M.Le M.Posn (M.posSeq t j) := by
      rw [maxPos_iff_rank hlin hp hmax, hr]
      omega
    have hsucc := succPos_nextPos_of_not_max hlin hp hnmax
    refine ⟨hsucc.2.1, ?_⟩
    rw [posSeq_succ, bitRank_succPos hlin hsucc, hr]
    omega

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq_spec)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- Consecutive positions of the enumeration are immediate successors. -/
theorem posSeq_succPos {t p₁ : A} (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁) {j : ℕ}
    (hj : j < Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn t) :
    Lax904597.Machines.SuccPos M.Le M.Posn (M.posSeq t j) (M.posSeq t (j + 1)) := by
  obtain ⟨hp, hr⟩ := posSeq_spec hlin ht hmax j (by omega)
  refine succPos_nextPos_of_not_max hlin hp ?_
  rw [maxPos_iff_rank hlin hp hmax, hr]
  omega

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq_succPos)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

/-- The enumeration reaches the highest position exactly at the end of the
budget. -/
theorem posSeq_budget {t p₁ : A} (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁) :
    M.posSeq t (Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn t) = p₁ := by
  have hrp₁ : Lax799700.Common.bitRank M.Le M.Posn t ≤ Lax799700.Common.bitRank M.Le M.Posn p₁ :=
    TMData.bitRank_le_of_le (M := M.toTMData) hlin ht (hmax.2 t ht)
  obtain ⟨hp, hr⟩ := posSeq_spec hlin ht hmax _ (Nat.le_refl _)
  exact bitRank_inj hlin hp hmax.1 (by omega)

end Rank

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq_budget)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Rank

variable (hlin : Lax904597.Machines.IsLinOrd M.Le)

include hlin

end Rank

/-! ### Reading a play off a sequence -/

omit [Finite A] in
/-- **Cutting a sequence of configurations into a play of block `i`.** The
sequence is stopped at the first of four events – the bound `n` is reached, the
sequence leaves the block, it accepts, it gets stuck – and up to there it is a
`DescriptiveComplexity.ATMData.BlockPlay`. The only thing asked of the sequence
is that it takes a genuine step whenever none of the four has happened, which
is what both a legal walk and the greedy continuation of
`DescriptiveComplexity.ATMData.greedy` provide. -/
theorem exists_play_of_seq {i : ℕ} {c : Lax904597.Machines.Config A} {g : ℕ → Lax904597.Machines.Config A} (n : ℕ)
    (hg0 : g 0 = c)
    (hgstep : ∀ j, j < n → M.Blk i (g j).state → ¬M.Acc (g j).state → ¬M.Stuck (g j) →
      M.Step (g j) (g (j + 1))) :
    ∃ ℓ, ℓ ≤ n ∧ M.BlockPlay i c ℓ g ∧
      (ℓ = n ∨ ¬M.Blk i (g ℓ).state ∨ M.Acc (g ℓ).state ∨ M.Stuck (g ℓ)) := by
  classical
  have hex : ∃ j, n ≤ j ∨ ¬M.Blk i (g j).state ∨ M.Acc (g j).state ∨ M.Stuck (g j) :=
    ⟨n, Or.inl (Nat.le_refl n)⟩
  obtain ⟨ℓ, hℓP, hℓmin⟩ :
      ∃ ℓ, (n ≤ ℓ ∨ ¬M.Blk i (g ℓ).state ∨ M.Acc (g ℓ).state ∨ M.Stuck (g ℓ)) ∧
        ∀ j, j < ℓ → ¬(n ≤ j ∨ ¬M.Blk i (g j).state ∨ M.Acc (g j).state ∨ M.Stuck (g j)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hstop : ∀ j, j < ℓ →
      j < n ∧ M.Blk i (g j).state ∧ ¬M.Acc (g j).state ∧ ¬M.Stuck (g j) := by
    intro j hj
    have hnot := hℓmin j hj
    refine ⟨?_, ?_, fun h => hnot (Or.inr (Or.inr (Or.inl h))),
      fun h => hnot (Or.inr (Or.inr (Or.inr h)))⟩
    · by_contra h
      exact hnot (Or.inl (by omega))
    · by_contra h
      exact hnot (Or.inr (Or.inl h))
  have hℓn : ℓ ≤ n := by
    by_contra hcon
    exact (hstop n (by omega)).1.false
  refine ⟨ℓ, hℓn, ⟨hg0, fun j hj => ?_, fun j hj => ?_⟩, ?_⟩
  · obtain ⟨hjn, hblk, hacc, hstuck⟩ := hstop j hj
    exact hgstep j hjn hblk hacc hstuck
  · exact ⟨(hstop j hj).2.1, (hstop j hj).2.2.1⟩
  · rcases hℓP with h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (exists_play_of_seq)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

omit [Finite A] in
/-- **A play depends only on its first `ℓ + 1` configurations.** -/
theorem BlockPlay.congr {i : ℕ} {c : Lax904597.Machines.Config A} {ℓ : ℕ} {f g : ℕ → Lax904597.Machines.Config A}
    (h : ∀ j, j ≤ ℓ → f j = g j) (hf : M.BlockPlay i c ℓ f) : M.BlockPlay i c ℓ g := by
  refine ⟨by rw [← h 0 (Nat.zero_le _)]; exact hf.1, fun j hj => ?_, fun j hj => ?_⟩
  · rw [← h j (Nat.le_of_lt hj), ← h (j + 1) hj]
    exact hf.2.1 j hj
  · rw [← h j (Nat.le_of_lt hj)]
    exact hf.2.2 j hj

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.BlockPlay

export Lax564036Proofs.DescriptiveComplexity.ATMData.BlockPlay (congr)

end Lax564036.AlternatingMachines.ATMData.BlockPlay

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### Reading a play off a walk -/

/-- **A walk legal below `i + 1` carries a play of block `i`.** From the
position `t`, whose configuration is in block `i`, follow the walk along the
order: the configurations form a play of block `i`, and it stops at the first
moment one of the four things happens that end a block – the budget runs out,
the walk leaves the block, it accepts, or it gets stuck. -/
theorem exists_play_of_legalBelow (hlin : Lax904597.Machines.IsLinOrd M.Le)
    {i : ℕ} {w : A → Lax904597.Machines.Config A} (hw : M.LegalBelow (i + 1) w) {t p₁ : A}
    (ht : M.Posn t) (hmax : MaxPos M.Le M.Posn p₁) :
    ∃ ℓ, ℓ ≤ Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn t ∧
      M.BlockPlay i (w t) ℓ (fun j => w (M.posSeq t j)) ∧
      (ℓ = Lax799700.Common.bitRank M.Le M.Posn p₁ - Lax799700.Common.bitRank M.Le M.Posn t ∨
        ¬M.Blk i (w (M.posSeq t ℓ)).state ∨ M.Acc (w (M.posSeq t ℓ)).state ∨
        M.Stuck (w (M.posSeq t ℓ))) := by
  refine exists_play_of_seq _ rfl fun j hj hblk hacc hstuck => ?_
  have hsucc := posSeq_succPos hlin ht hmax (j := j) hj
  rcases hw.2.2 _ _ hsucc ⟨i, Nat.lt_succ_self i, hblk⟩ with ⟨hstep, -⟩ | ⟨-, hor⟩
  · exact hstep
  · exact absurd hor (by rintro (h | h) <;> [exact hacc h; exact hstuck h])

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (exists_play_of_legalBelow)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

end ATMData

end Lax564036Proofs.DescriptiveComplexity


