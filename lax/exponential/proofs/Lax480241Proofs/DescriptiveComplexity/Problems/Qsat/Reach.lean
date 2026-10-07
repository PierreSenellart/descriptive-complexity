/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Savitch
import Lax480241Proofs.DescriptiveComplexity.Problems.SuccinctReach.Defs
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

namespace Lax134656.SuccinctReach
end Lax134656.SuccinctReach

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SuccinctReach (IsGoal IsStart ReadsCur StepRel SuccinctReachable WritesNext)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax134656.SuccinctReach (transSys tsStateVar)
end FirstOrder.Language

/-!
# SUCCINCT-REACH as a Savitch recursion

The first half of the reduction of SUCCINCT-REACH to QSAT: rewriting the
yes-instances of `DescriptiveComplexity.SUCCINCTREACH` – a reachability statement
with an unbounded number of steps – as the bounded, *recursively doubled*
statement `DescriptiveComplexity.SavPow` of `DescriptiveComplexity.Savitch`, whose
unfolding has depth equal to the number of state variables. That is the form a
quantifier prefix can express.

The vertices of the walk are not the states themselves – a state is a predicate
on the whole universe – but their restrictions to the state variables
(`DescriptiveComplexity.stCls`), since that is all the clause groups can read.
There are `2 ^ m` such restrictions for `m` state variables
(`DescriptiveComplexity.card_stateClass`), so `m` levels of doubling suffice:
`DescriptiveComplexity.succinctReachable_iff_savPow`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section States

variable {A : Type} [Lax134656.SuccinctReach.transSys.Structure A]

variable (A) in
/-- The state variables of an instance, as a type: the coordinates of a
state that the clause groups can read. -/
abbrev StateVar : Type := {x : A // RelMap Lax134656.SuccinctReach.tsStateVar ![x]}

/-- The **class** of a state: its restriction to the state variables. Two states
with the same class are interchangeable everywhere in the semantics. -/
def stCls (S : A → Prop) : StateVar A → Prop := fun x => S x.1

theorem stCls_eq_iff {S S' : A → Prop} :
    stCls S = stCls S' ↔ ∀ x : A, RelMap Lax134656.SuccinctReach.tsStateVar ![x] → (S x ↔ S' x) := by
  refine ⟨fun h x hx => iff_of_eq (congrFun h ⟨x, hx⟩), fun h => ?_⟩
  funext x
  exact propext (h x.1 x.2)

variable (A) in
/-- The number of state variables: the depth of the Savitch recursion the
reduction writes as a quantifier prefix. -/
noncomputable def stateDepth : ℕ := Nat.card (StateVar A)

/-! ### The semantics only sees a state through its class -/

theorem readsCur_congr {ν S S' : A → Prop} (h : stCls S = stCls S') (hr : Lax134656.SuccinctReach.ReadsCur A ν S) :
    Lax134656.SuccinctReach.ReadsCur A ν S' :=
  fun x hx => (hr x hx).trans (stCls_eq_iff.mp h x hx)

theorem writesNext_congr {ν S S' : A → Prop} (h : stCls S = stCls S') (hw : Lax134656.SuccinctReach.WritesNext A ν S) :
    Lax134656.SuccinctReach.WritesNext A ν S' :=
  fun x y hx hxy => (hw x y hx hxy).trans (stCls_eq_iff.mp h x hx)

theorem isStart_congr {S S' : A → Prop} (h : stCls S = stCls S') (hs : Lax134656.SuccinctReach.IsStart A S) :
    Lax134656.SuccinctReach.IsStart A S' :=
  let ⟨ν, hcl, hr⟩ := hs
  ⟨ν, hcl, readsCur_congr h hr⟩

theorem isGoal_congr {S S' : A → Prop} (h : stCls S = stCls S') (hs : Lax134656.SuccinctReach.IsGoal A S) :
    Lax134656.SuccinctReach.IsGoal A S' :=
  let ⟨ν, hcl, hr⟩ := hs
  ⟨ν, hcl, readsCur_congr h hr⟩

/-- **The transition relation lives on the classes**: it only depends on its two
endpoints through their restrictions to the state variables. -/
theorem savInv_stepRel : SavInv (stCls (A := A)) (Lax134656.SuccinctReach.StepRel A) := by
  rintro X X' Y Y' hX hY ⟨ν, hcl, hr, hw⟩
  exact ⟨ν, hcl, readsCur_congr hX hr, writesNext_congr hY hw⟩

end States

section Depth

variable {A : Type} [Lax134656.SuccinctReach.transSys.Structure A] [Finite A]

/-- **There are `2 ^ m` classes of states** for `m` state variables. -/
theorem card_stateClass :
    Nat.card (StateVar A → Prop) = 2 ^ stateDepth A := by
  rw [Nat.card_fun, stateDepth]
  congr 1
  rw [Nat.card_congr Equiv.propEquivBool, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- **SUCCINCT-REACH as a bounded, recursively doubled reachability statement.**
The walk saturates after `2 ^ m` moves, `m` the number of state variables, and
`DescriptiveComplexity.SavPow` at depth `m` is exactly that bound. -/
theorem succinctReachable_iff_savPow :
    Lax134656.SuccinctReach.SuccinctReachable A ↔
      ∃ S T : A → Prop, Lax134656.SuccinctReach.IsStart A S ∧ Lax134656.SuccinctReach.IsGoal A T ∧
        SavPow (stCls (A := A)) (Lax134656.SuccinctReach.StepRel A) (stateDepth A) S T := by
  constructor
  · rintro ⟨S, T, hS, hT, hreach⟩
    exact ⟨S, T, hS, hT,
      savPow_of_reflTransGen savInv_stepRel (le_of_eq card_stateClass) hreach⟩
  · rintro ⟨S, T, hS, hT, hsav⟩
    obtain ⟨T', hT', hreach⟩ := reflTransGen_of_savLe savInv_stepRel _
      ((savPow_iff_savLe savInv_stepRel _).mp hsav)
    exact ⟨S, T', hS, isGoal_congr hT'.symm hT, hreach⟩

end Depth

end Lax480241Proofs.DescriptiveComplexity


