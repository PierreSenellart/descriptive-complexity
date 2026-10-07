/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.MachinesAlt
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax480241.AlternatingSpace.ATMData
end Lax480241.AlternatingSpace.ATMData

namespace Lax480241Proofs.DescriptiveComplexity.ATMData
end Lax480241Proofs.DescriptiveComplexity.ATMData

namespace Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree
end Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity.Config
end Lax480241Proofs.DescriptiveComplexity.Config

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData guardQ)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData
export Lax480241.AlternatingSpace.ATMData (AltAcceptsSpace AltWin BlocksSplit)
end Lax564036.AlternatingMachines.ATMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# Alternating machines in bounded space

The fourth acceptance notion of `DescriptiveComplexity.TMData`, and the one
that reaches EXPTIME: an *alternating* machine whose tape is indexed by the
positions, with **no bound on the length of a play and no bound on the number
of alternations**. It stands to `DescriptiveComplexity.ATMData.AltAccepts`
exactly as `DescriptiveComplexity.TMData.AcceptsSpace` stands to
`DescriptiveComplexity.TMData.Accepts`: the step budget is dropped, the space
stays bounded by construction, and what changes is that a play no longer fits
inside the structure.

## Winning, as an inductive predicate

`DescriptiveComplexity.ATMData.AltAcc` recurses on a budget, which is what makes
it a Lean-level recursion rather than a fixed point. With the budget gone the
right presentation is the **least fixed point** of the game operator, and in
Lean that is an inductive predicate
(`DescriptiveComplexity.ATMData.AltWin`): an accepting state wins; an
existential configuration wins when *some* successor does; a universal one when
it has a successor and *every* successor wins. Looping therefore loses, which is
the standard convention and the one that agrees with the budgeted definition
(`DescriptiveComplexity.ATMData.altWin_iff_exists_altAcc`).

Being an inductive rather than a `∃ n` also makes the correspondence with the
AND/OR game of alternating reachability a matter of matching constructors, which
is what the EXPTIME membership proof consumes.

## Unbounded alternation, at no cost

`DescriptiveComplexity.ATMData.BlocksWellFormed` is what bounds the number of
alternations, by forbidding a transition from lowering the block index; it is
*not* imposed here. What is imposed instead is only that the marks partition the
states in two (`DescriptiveComplexity.ATMData.BlocksSplit`), so that block `0`
is the existential player and block `1` the universal one
(`DescriptiveComplexity.ATMData.isUniv_true_iff_blk_one`). No second machine
record is needed and no lemma of `DescriptiveComplexity.MachinesAlt` has to be
restated: the vocabulary is `FirstOrder.Language.turingAlt 2` unchanged.
-/

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

/-! ### Winning the game on the configuration graph -/

/-! ### The budgeted definition, unbounded -/

variable {M}

/-! ### With no universal state the model is the nondeterministic one -/

/-! ### Two blocks are a bipartition of the states -/

variable (M)

variable {M}

/-- **Block `1` is the universal player.** With the marks split in two, the
polarity bookkeeping of `DescriptiveComplexity.blockPol` collapses to a single
mark, so the model reads as an ordinary alternating machine with an
existential and a universal set of states. -/
theorem isUniv_true_iff_blk_one (hsplit : M.BlocksSplit) (q : A) :
    M.IsUniv true q ↔ M.Blk 1 q := by
  constructor
  · rintro ⟨j, hj, hpol⟩
    obtain ⟨i, hi2, hi, huniq⟩ := hsplit q
    have hij : j = i := huniq j hj
    have hi1 : i = 1 := by
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · rw [hij] at hpol
        exact absurd hpol (by decide)
      · rfl
    rw [← hi1]
    exact hi
  · intro h
    exact ⟨1, h, by decide⟩

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax480241Proofs.DescriptiveComplexity.ATMData (isUniv_true_iff_blk_one)

end Lax564036.AlternatingMachines.ATMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

variable {M}

variable (M)

variable {M}

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type} {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

/-- **Winning transports along an equivalence of universes.** Stated as an
implication rather than an equivalence, and proved without any finiteness: the
converse comes from the agreement in the other direction, which the
isomorphism-invariance of a decision problem has anyway. -/
theorem AltAgree.altWin_mp (h : AltAgree u N M) (start : Bool) :
    ∀ {c : Lax904597.Machines.Config B}, N.AltWin start c → M.AltWin start (c.map u) := by
  intro c hw
  induction hw with
  | acc ha => exact .acc ((h.base.acc _).mp ha)
  | @ex d d' hu hstep _ ih =>
    exact .ex (fun hc => hu ((h.isUniv start d.state).mpr hc)) (h.base.step.mp hstep) ih
  | @all d hu hex _ ih =>
    refine .all ((h.isUniv start d.state).mp hu) ?_ ?_
    · obtain ⟨e, he⟩ := hex
      exact ⟨e.map u, h.base.step.mp he⟩
    · intro e he
      obtain ⟨e₀, rfl⟩ := Config.map_surjective u e
      exact ih e₀ (h.base.step.mpr he)

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.AltAgree

export Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree (altWin_mp)

end Lax564036.AlternatingMachines.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

variable {M}

variable (M)

variable {M}

section Transport

variable {B : Type} {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

/-- **Acceptance in bounded space transports along an equivalence.** -/
theorem AltAgree.altAcceptsSpace_mp (h : AltAgree u N M) (start : Bool) :
    N.AltAcceptsSpace start → M.AltAcceptsSpace start := by
  cases start with
  | true =>
    rintro ⟨c₀, hinit, hw⟩
    exact ⟨c₀.map u, h.base.isInit.mp hinit, h.altWin_mp true hw⟩
  | false =>
    rintro ⟨⟨c, hc⟩, hf⟩
    refine ⟨⟨c.map u, h.base.isInit.mp hc⟩, fun d hd => ?_⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u d
    exact h.altWin_mp false (hf d₀ (h.base.isInit.mpr hd))

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.AltAgree

export Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree (altAcceptsSpace_mp)

end Lax564036.AlternatingMachines.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

variable {M}

variable (M)

variable {M}

section Transport

variable {B : Type} {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

/-- **The two-block split transports along an equivalence.** -/
theorem AltAgree.blocksSplit_mp (h : AltAgree u N M) : N.BlocksSplit → M.BlocksSplit := by
  intro hf q
  obtain ⟨j, hjk, hj, huq⟩ := hf (u.symm q)
  refine ⟨j, hjk, ?_, fun j' hj' => huq j' ?_⟩
  · rwa [h.blk j (u.symm q), Equiv.apply_symm_apply] at hj
  · rw [h.blk j' (u.symm q), Equiv.apply_symm_apply]
    exact hj'

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.AltAgree

export Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree (blocksSplit_mp)

end Lax564036.AlternatingMachines.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

variable {M}

variable (M)

variable {M}

section Transport

variable {B : Type} {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity


