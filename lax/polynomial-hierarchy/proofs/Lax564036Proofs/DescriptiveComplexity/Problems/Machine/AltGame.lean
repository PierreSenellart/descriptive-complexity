/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.MachinesAltPlay
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.Program
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData blockPol guardQ)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax564036Proofs.DescriptiveComplexity

/-!
# The `k`-round game: what a `Σₖ` definition of alternating acceptance guesses

`DescriptiveComplexity.ATMData.AltAcc` recurses one step at a time; a `Σₖ`
sentence has `k` quantifiers and must therefore commit a whole *round* at a
time. This file defines the round game – the object the second-order blocks of
the membership proof guess – together with the facts about walks it needs. No
vocabulary appears, as in `DescriptiveComplexity.Machines`; the file sits under
`Problems/Machine` only because it reads the rank machinery of
`DescriptiveComplexity.Problems.Machine.Walk`.

## What a round guesses

A *walk* is a configuration per position, positions being times as everywhere
in the bridge. Round `i`'s walk is asked for three things
(`DescriptiveComplexity.ATMData.LegalBelow`):

* it is initial at the lowest position;
* its blocks never decrease along the order
  (`DescriptiveComplexity.ATMData.BlkMono`) – true of any real run, and needed
  of a *guess* so that the times of a block form one stretch rather than
  several;
* at each immediate successor it steps *out of a non-accepting configuration*,
  or stutters in an accepting or stuck one – **but only where its state is in a
  block below `i`**.

Acceptance is therefore absorbing: a walk that has accepted may not move again,
so it still accepts at the highest position, and every later round is obliged
to copy it. Without that, a round could step past an acceptance and let a later
player steer the run into rejection, while
`DescriptiveComplexity.ATMData.AltAcc` grants an accepting configuration
outright.

The last restriction is what keeps the game cheap. Round `i` answers for the
blocks up to `i` and no further, so its walk may be arbitrary from the moment
it hands over; that is why building a witness never needs a legal continuation
to the end of time. Stuttering must be allowed at a *stuck* configuration, not
only at an accepting one as in `DescriptiveComplexity.TMData.IsWalk`: otherwise
a machine that stops has no legal walk at all, the universal rounds become
vacuous, and getting stuck would count as accepting – the opposite of the
convention of `DescriptiveComplexity.MachinesAlt`.

## What a round inherits

`DescriptiveComplexity.ATMData.AgreeBelow` makes round `i` reproduce what the
earlier rounds committed: the configuration at every time whose block – *in the
previous round's walk* – is below `i`, and the configuration at the immediate
successor of such a time. The second clause is not redundant: the move out of
the last configuration of block `i - 1` belongs to the previous player, so the
successor of a committed time is committed too. At `i = 0` both clauses are
vacuous, which is why the first round is free
(`DescriptiveComplexity.ATMData.altGame_eq_gameFrom`).

## The order lemmas

Two facts about the linear order of the positions are proved here and used
throughout: induction upwards from a position
(`DescriptiveComplexity.ATMData.le_induction`), and the successor function
`DescriptiveComplexity.ATMData.nextPos` walking along it, whose rank increases
by one until the highest position is reached.
-/

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### Induction along the positions -/

/-- **Induction upwards from a position**: a property holding at `s` and
inherited along immediate successors holds at every position above `s`. The
same induction as `DescriptiveComplexity.TMData.stepsIn_of_segment`, isolated
because the game needs it for properties that are not about runs. -/
theorem le_induction [Finite A] (hlin : Lax904597.Machines.IsLinOrd M.Le) {P : A → Prop} {s : A}
    (hs : M.Posn s) (hP : P s)
    (hstep : ∀ p q, Lax904597.Machines.SuccPos M.Le M.Posn p q → M.Le s p → P p → P q) :
    ∀ q, M.Posn q → M.Le s q → P q := by
  have key : ∀ n : ℕ, ∀ q, M.Posn q → M.Le s q → Lax799700.Common.bitRank M.Le M.Posn q = n → P q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hq hle hrank
      rcases eq_or_ne s q with rfl | hne
      · exact hP
      · have hnmin : ¬Lax904597.Machines.MinPos M.Le M.Posn q := fun hmin =>
          hne (hlin.2.2.1 s q hle (hmin.2 s hs))
        obtain ⟨p, hp⟩ := exists_predPos hlin hq hnmin
        have hsp : M.Le s p := by
          rcases hlin.2.2.2 s p with h | h
          · exact h
          · rcases hp.2.2.2.2 s hs h hle with h' | h'
            · exact h' ▸ hlin.1 s
            · exact absurd h' hne
        have hrp : Lax799700.Common.bitRank M.Le M.Posn q = Lax799700.Common.bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hp
        exact hstep p q hp hsp (ih (Lax799700.Common.bitRank M.Le M.Posn p) (by omega) p hp.1 hsp rfl)
  exact fun q hq hle => key _ q hq hle rfl

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (le_induction)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

open Classical in
/-- The next position after `t`, or `t` itself at the highest position. -/
noncomputable def nextPos (M : Lax564036.AlternatingMachines.ATMData A) (t : A) : A :=
  if h : ∃ q, Lax904597.Machines.SuccPos M.Le M.Posn t q then h.choose else t

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (nextPos)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

theorem succPos_nextPos {t : A} (h : ∃ q, Lax904597.Machines.SuccPos M.Le M.Posn t q) :
    Lax904597.Machines.SuccPos M.Le M.Posn t (M.nextPos t) := by
  classical
  rw [nextPos, dif_pos h]
  exact h.choose_spec

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (succPos_nextPos)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-- The positions reached from `t` by stepping `j` times along the order. -/
noncomputable def posSeq (M : Lax564036.AlternatingMachines.ATMData A) (t : A) : ℕ → A
  | 0 => t
  | j + 1 => M.nextPos ((posSeq M) t j)

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

@[simp] theorem posSeq_zero (M : Lax564036.AlternatingMachines.ATMData A) (t : A) : M.posSeq t 0 = t := rfl

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq_zero)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

@[simp] theorem posSeq_succ (M : Lax564036.AlternatingMachines.ATMData A) (t : A) (j : ℕ) :
    M.posSeq t (j + 1) = M.nextPos (M.posSeq t j) := rfl

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (posSeq_succ)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-- **The rank increases by one along `nextPos`**, as long as the highest
position has not been reached. -/
theorem succPos_nextPos_of_not_max [Finite A] (hlin : Lax904597.Machines.IsLinOrd M.Le) {t : A}
    (ht : M.Posn t) (hmax : ¬MaxPos M.Le M.Posn t) :
    Lax904597.Machines.SuccPos M.Le M.Posn t (M.nextPos t) :=
  succPos_nextPos (TMData.exists_succPos' (M := M.toTMData) hlin ht hmax)

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (succPos_nextPos_of_not_max)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### Walks -/

variable (M) in
/-- **The blocks of a walk never decrease.** True of any run, and asked of a
guess so that the times of one block form a single stretch. -/
def BlkMono (w : A → Lax904597.Machines.Config A) : Prop :=
  ∀ p q, Lax904597.Machines.SuccPos M.Le M.Posn p q → ∀ j j', M.Blk j (w p).state → M.Blk j' (w q).state → j ≤ j'

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (BlkMono)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

variable (M) in
/-- **A walk legal below block `i`**: initial at the lowest position, with
non-decreasing blocks, and stepping or stuttering at every immediate successor
whose configuration is in a block below `i`. Round `i` of the game guesses a
walk legal below `i + 1`: it answers for its own block and no later one. -/
def LegalBelow (i : ℕ) (w : A → Lax904597.Machines.Config A) : Prop :=
  (∀ p, Lax904597.Machines.MinPos M.Le M.Posn p → M.IsInit (w p)) ∧ M.BlkMono w ∧
    ∀ p q, Lax904597.Machines.SuccPos M.Le M.Posn p q → M.BlkLt i (w p).state →
      (M.Step (w p) (w q) ∧ ¬M.Acc (w p).state) ∨
        (w q = w p ∧ (M.Acc (w p).state ∨ M.Stuck (w p)))

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (LegalBelow)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

variable (M) in
/-- **The walk accepts**: its state at the highest position is accepting. -/
def AccAt (w : A → Lax904597.Machines.Config A) : Prop :=
  ∀ p, MaxPos M.Le M.Posn p → M.Acc (w p).state

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (AccAt)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

variable (M) in
/-- **Round `i` reproduces what the earlier rounds committed**: the
configuration at every time whose block in `prev` is below `i`, and at the
immediate successor of such a time – the move out of the last committed
configuration belonging to the previous player. -/
def AgreeBelow (i : ℕ) (w prev : A → Lax904597.Machines.Config A) : Prop :=
  (∀ t, M.Posn t → M.BlkLt i (prev t).state → w t = prev t) ∧
    ∀ t t', Lax904597.Machines.SuccPos M.Le M.Posn t t' → M.BlkLt i (prev t).state → w t' = prev t'

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (AgreeBelow)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

variable (M) in
/-- The condition round `i` puts on its walk: legal below `i + 1`, and
agreeing with the previous round below `i`. -/
def RoundCond (i : ℕ) (prev w : A → Lax904597.Machines.Config A) : Prop :=
  M.LegalBelow (i + 1) w ∧ M.AgreeBelow i w prev

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (RoundCond)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### Reading the blocks of a walk -/

section Blocks

/-- Membership in a block below `i`, once the block is known. -/
theorem blkLt_iff (hbwf : M.BlocksWellFormed k) {i j : ℕ} {q : A} (hj : M.Blk j q) :
    M.BlkLt i q ↔ j < i := by
  constructor
  · rintro ⟨j', hj', h'⟩
    rwa [blk_unique hbwf h' hj] at hj'
  · exact fun h => ⟨j, h, hj⟩

end Blocks

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (blkLt_iff)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Blocks

/-- **A walk enters the blocks in order**: the first time whose block is not
below `i` is in block `i` exactly, since the step into it is legal. -/
theorem blk_eq_of_entry (hbwf : M.BlocksWellFormed k) {w : A → Lax904597.Machines.Config A} {i : ℕ}
    (hw : M.LegalBelow i w) {p q : A} (hpq : Lax904597.Machines.SuccPos M.Le M.Posn p q)
    (hp : M.BlkLt i (w p).state) (hq : ¬M.BlkLt i (w q).state) :
    M.Blk i (w q).state := by
  obtain ⟨jp, -, hjp, -⟩ := hbwf.1 (w p).state
  have hjplt : jp < i := (blkLt_iff hbwf hjp).mp hp
  rcases hw.2.2 p q hpq hp with ⟨hstep, -⟩ | ⟨heq, -⟩
  · rcases blk_step hbwf hstep hjp with h | h
    · exact absurd ((blkLt_iff hbwf h).mpr hjplt) hq
    · have hnot : ¬jp + 1 < i := fun hlt => hq ((blkLt_iff hbwf h).mpr hlt)
      have hEq : jp + 1 = i := by omega
      exact hEq ▸ h
  · exact absurd (heq ▸ hp) hq

end Blocks

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (blk_eq_of_entry)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Blocks

/-- **The times of the low blocks form a prefix.** -/
theorem blkLt_of_le [Finite A] (hbwf : M.BlocksWellFormed k) (hlin : Lax904597.Machines.IsLinOrd M.Le)
    {w : A → Lax904597.Machines.Config A} (hmono : M.BlkMono w) {i : ℕ} {s q : A}
    (hs : M.Posn s) (hq : M.Posn q) (hle : M.Le s q) (h : M.BlkLt i (w q).state) :
    M.BlkLt i (w s).state := by
  obtain ⟨js, -, hjs, -⟩ := hbwf.1 (w s).state
  obtain ⟨jq, -, hjq, -⟩ := hbwf.1 (w q).state
  have hup : ∀ x, M.Posn x → M.Le s x → ∀ jx, M.Blk jx (w x).state → js ≤ jx := by
    refine le_induction hlin hs (P := fun x => ∀ jx, M.Blk jx (w x).state → js ≤ jx)
      (fun jx hjx => Nat.le_of_eq (blk_unique hbwf hjs hjx)) ?_
    intro p p' hpp' _hsp hp jp' hjp'
    obtain ⟨jp, -, hjp, -⟩ := hbwf.1 (w p).state
    exact Nat.le_trans (hp jp hjp) (hmono p p' hpp' jp jp' hjp hjp')
  exact (blkLt_iff hbwf hjs).mpr
    (Nat.lt_of_le_of_lt (hup q hq hle jq hjq) ((blkLt_iff hbwf hjq).mp h))

end Blocks

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (blkLt_of_le)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

section Blocks

end Blocks

/-! ### The game -/

variable (M) in
/-- **The game from round `i` on**, with `m` rounds still to play and `prev`
the walk the previous round produced: the owner of block `i` chooses a walk
subject to `DescriptiveComplexity.ATMData.RoundCond`, and play passes to the
next block. When no round is left, the walk that remains must accept. -/
def gameFrom (start : Bool) (i : ℕ) : ℕ → (A → Lax904597.Machines.Config A) → Prop
  | 0, prev => M.AccAt prev
  | m + 1, prev =>
      Lax564036.AlternatingMachines.guardQ (Lax564036.AlternatingMachines.blockPol start i) (M.RoundCond i prev) fun w => gameFrom start (i + 1) m w

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (gameFrom)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

variable (M) in
/-- **The whole `k`-round game.** The first round is free – there is nothing
committed yet – so it is peeled off; every later round inherits from the one
before it. -/
def AltGame (start : Bool) : ℕ → Prop
  | 0 => False
  | m + 1 =>
      Lax564036.AlternatingMachines.guardQ (Lax564036.AlternatingMachines.blockPol start 0) (fun w => M.LegalBelow 1 w) fun w => M.gameFrom start 1 m w

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (AltGame)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-! ### A finished run plays itself out -/

/-- **Once every time is in a low block the game is decided**: each remaining
round can only copy what it inherited, so the outcome is whether the walk
accepts. -/
theorem gameFrom_of_blkLt (start : Bool) :
    ∀ (m i : ℕ) (prev : A → Lax904597.Machines.Config A), M.LegalBelow i prev →
      (∀ s, M.Posn s → M.BlkLt i (prev s).state) →
      (M.gameFrom start i m prev ↔ M.AccAt prev) := by
  intro m
  induction m with
  | zero => intro i prev _ _; exact Iff.rfl
  | succ m ih =>
    intro i prev hlegal hall
    have hlegal' : M.LegalBelow (i + 1) prev :=
      ⟨hlegal.1, hlegal.2.1, fun p q hpq _ => hlegal.2.2 p q hpq (hall p hpq.1)⟩
    have hself : M.RoundCond i prev prev :=
      ⟨hlegal', fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    -- any admissible walk copies `prev` at every position, hence plays out the same
    have hcopy : ∀ w, M.RoundCond i prev w → (M.gameFrom start (i + 1) m w ↔ M.AccAt prev) := by
      intro w hw
      have heq : ∀ s, M.Posn s → w s = prev s := fun s hs => hw.2.1 s hs (hall s hs)
      have hallw : ∀ s, M.Posn s → M.BlkLt (i + 1) (w s).state := by
        intro s hs
        obtain ⟨j, hj, h⟩ := hall s hs
        exact ⟨j, by omega, by rw [heq s hs]; exact h⟩
      refine (ih (i + 1) w hw.1 hallw).trans ?_
      exact ⟨fun h p hp => by rw [← heq p hp.1]; exact h p hp,
        fun h p hp => by rw [heq p hp.1]; exact h p hp⟩
    change Lax564036.AlternatingMachines.guardQ (Lax564036.AlternatingMachines.blockPol start i) (M.RoundCond i prev)
        (fun w => M.gameFrom start (i + 1) m w) ↔ M.AccAt prev
    by_cases hpol : Lax564036.AlternatingMachines.blockPol start i = true
    · rw [hpol, guardQ_true]
      exact ⟨fun ⟨w, hw, h⟩ => (hcopy w hw).mp h, fun h => ⟨prev, hself, (hcopy prev hself).mpr h⟩⟩
    · have hfalse : Lax564036.AlternatingMachines.blockPol start i = false := by
        cases h : Lax564036.AlternatingMachines.blockPol start i
        · rfl
        · exact absurd h hpol
      rw [hfalse, guardQ_false]
      exact ⟨fun h => (hcopy prev hself).mp (h.2 prev hself),
        fun h => ⟨⟨prev, hself⟩, fun w hw => (hcopy w hw).mpr h⟩⟩

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (gameFrom_of_blkLt)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

end ATMData

end Lax564036Proofs.DescriptiveComplexity


