/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Machines
import Lax822549Proofs.DescriptiveComplexity.OrderWalk
import Mathlib.Logic.Relation
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config TMData)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Loops in the control: runs indexed by a finite linear order

The element loops of the EXPSPACE program enumerate tuples of source elements
in the machine's control, one lexicographic successor per round. The register
loops have their induction principle already
(`DescriptiveComplexity.reaches_of_wideRounds`, driven by the address rank);
the control loops get theirs here, driven by
`DescriptiveComplexity.order_induction`:

* `DescriptiveComplexity.Draw.reflTransGen_of_ordLoop` – a run per immediate
  successor of a finite linear order carries the machine from the bottom to
  anywhere;
* `DescriptiveComplexity.Draw.reflTransGen_of_tupLoop` – the same over tuples in
  the lexicographic order, the rounds indexed by
  `DescriptiveComplexity.TupSucc`, which is the shape of the guards the
  advancing rules read (`DescriptiveComplexity.succTupF`).

Both are stated for an arbitrary relation on an arbitrary configuration type:
nothing here is about wide machines, and the reachability they produce is fed
to `Relation.ReflTransGen.trans` like any other phase.

Both also have a **budgeted** form – `reachesIn_of_ordLoop` and
`reachesIn_of_tupLoop`, with `reachesIn_of_ordLoop_card` for the crude bound –
which keeps the count a clocked program has to compare with its clock: one
round's budget, once per element of the enumeration. A space-bounded program
throws the count away and uses the two above.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

section Loop

variable {C : Type} {Step : C → C → Prop}

/-- **A loop over a finite linear order, on a clock**: one *budgeted* run per
immediate successor, and the machine reaches the configuration of any element
paying that budget once per element it crossed. The count is `orank`, the
number of elements strictly below the target, so a whole loop costs
`w · (card − 1)` and a clocked program can compare it with its clock.

This is `DescriptiveComplexity.Draw.reflTransGen_of_ordLoop` with the budget
kept, and it is what turns every element and tag loop of the evaluation into a
cost. -/
theorem reachesIn_of_ordLoop {A : Type} [LinearOrder A] [Finite A]
    {S : Type} {M : Lax904597.Machines.TMData S} {conf : A → Lax904597.Machines.Config S} {w : ℕ}
    (hstep : ∀ x z : A, x < z → (∀ a : A, ¬(x < a ∧ a < z)) →
      M.ReachesIn w (conf x) (conf z))
    {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (a : A) :
    M.ReachesIn (w * orank a) (conf a₀) (conf a) := by
  induction a using order_induction with
  | hmin z hz =>
    rw [le_antisymm (hbot z) (hz a₀), orank_eq_zero hz, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | hstep x z hxz hnb ih =>
    have hcov : x ⋖ z := ⟨hxz, fun c h₁ h₂ => hnb c ⟨h₁, h₂⟩⟩
    rw [orank_covBy hcov, Nat.mul_succ]
    exact ih.trans (hstep x z hxz hnb)

/-- **A loop over a finite linear order, at the crude bound**: the whole loop
costs at most the budget of one round times the number of elements. What a
clock is compared with. -/
theorem reachesIn_of_ordLoop_card {A : Type} [LinearOrder A] [Finite A]
    {S : Type} {M : Lax904597.Machines.TMData S} {conf : A → Lax904597.Machines.Config S} {w : ℕ}
    (hstep : ∀ x z : A, x < z → (∀ a : A, ¬(x < a ∧ a < z)) →
      M.ReachesIn w (conf x) (conf z))
    {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (a : A) :
    M.ReachesIn (w * Nat.card A) (conf a₀) (conf a) :=
  (reachesIn_of_ordLoop hstep hbot a).mono
    (Nat.mul_le_mul_left w (Nat.le_of_lt (orank_lt_card a)))

end Loop

end Draw

end Lax822549Proofs.DescriptiveComplexity


