/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Exponential.Pull
import Lax822549Proofs.DescriptiveComplexity.Hierarchy
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Classes (CofinalHard)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The exponential of a complexity class

`DescriptiveComplexity.ComplexityClass.exp` reads a class over the *expanded*
universe: `P ∈ C.exp` when there is an exponential expansion `X` and a problem
`Q ∈ C` such that `P` holds of `A` exactly when `Q` holds of `X.Map A`. Since
the expanded universe of a size-`n` structure has `2^(n^a)` points, a resource
bound read there is one exponential higher than the same bound read on `A`.
This is the succinctness upgrade – trivial properties of circuit-described
graphs become NP-complete ([Galperin–Wigderson 1983][galperin1983succinct]),
NP-complete properties become NEXPTIME-complete ([Papadimitriou–Yannakakis
1986][papadimitriou1986note]), and the general statement is [Veith
1998][veith1998succinct] – stated as an *operator* rather than as a theorem
about one problem at a time.

The operator is applied to an **abstract** `DescriptiveComplexity.ComplexityClass`,
and that is the whole point of the design: the complement equalities, the
inclusions and the completeness transfers of the exponential classes are then
inherited from their polynomial-level counterparts instead of being reproved.

That `ExpDefinable C` is closed under (ordered) first-order reductions – so
that `C.exp` is a class at all – is
`DescriptiveComplexity.ExpExpansion.pullOrdered`: an interpretation followed by
an expansion is an expansion. Nothing about `C` is used, which is why the
closure holds at an arbitrary class.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-! ### Cofinal hardness only sees the membership predicate -/

/-- Cofinal hardness depends on the membership predicate only up to pointwise
equivalence. Needed to compare the hardness halves of two classes built by
`DescriptiveComplexity.ComplexityClass.ofMem` from equivalent membership
predicates, as `DescriptiveComplexity.ComplexityClass.exp_compl` does. -/
theorem cofinalHard_congr_mem
    {Mem Mem' : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    (h : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : Lax904597.Problems.DecisionProblem L₀), Mem Q ↔ Mem' Q)
    {L : Language.{0, 0}} [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    Lax904597.Classes.CofinalHard Mem P ↔ Lax904597.Classes.CofinalHard Mem' P := by
  constructor
  · intro hP L' _ S hS L'' _ Q hQ
    exact hP S hS Q ((h Q).mpr hQ)
  · intro hP L' _ S hS L'' _ Q hQ
    exact hP S hS Q ((h Q).mp hQ)

/-! ### Definability over an expanded universe -/

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- **Definability over an expanded universe**: the problem `P` is `C`-definable
one exponential up when some exponential expansion `X` turns it into a problem
of `C` – `P` holds of `A` exactly when a fixed `Q ∈ C` holds of `X.Map A`. -/
def ExpDefinable (C : ComplexityClass) (P : Lax904597.Problems.DecisionProblem L) : Prop :=
  ∃ (X : Lax480241.Expansions.ExpExpansion L) (Q : Lax904597.Problems.DecisionProblem X.E), C.Mem Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

variable {C : ComplexityClass} {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

/-- Definability over an expanded universe only depends on the finite instances
of a problem. -/
theorem expDefinable_congr {P P' : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) :
    ExpDefinable C P ↔ ExpDefinable C P' := by
  constructor <;> rintro ⟨X, R, hR, hX⟩ <;> refine ⟨X, R, hR, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hX A)
  · exact (h A).trans (hX A)

/-- **Closure under ordered first-order reductions**: the interpretation of the
reduction, followed by the expansion witnessing `Q`, is again an expansion. -/
theorem ExpDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : ExpDefinable C Q) :
    ExpDefinable C P := by
  obtain ⟨X, R, hR, hX⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  -- The pulled expansion has the same expanded vocabulary as `X`, but
  -- `pullOrdered` is not reducible, so the expanded structure has to be offered
  -- to instance search by hand.
  let hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      X.E.Structure ((X.pullOrdered f.toInterpretation).Map A) :=
    fun A => X.pullOrderedStructure f.toInterpretation A
  refine ⟨X.pullOrdered f.toInterpretation, R, hR, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hX (f.toInterpretation.Map A)).trans
    (R.iso_invariant (X.pullOrderedLEquiv f.toInterpretation A)))

/-- Closure under first-order reductions. -/
theorem ExpDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : ExpDefinable C Q) :
    ExpDefinable C P :=
  h.of_orderedReduction f.toOrdered

/-! ### The exponential of a class -/

/-- **The exponential of a complexity class**: the problems that become members
of `C` when read over an exponentially larger, definable universe. Hardness is
cofinal hardness for that membership predicate, as for every class of this
library. -/
noncomputable def ComplexityClass.exp (C : ComplexityClass) : ComplexityClass :=
  .ofMem (fun P => ExpDefinable C P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => expDefinable_congr h)

@[simp]
theorem ComplexityClass.mem_exp (C : ComplexityClass) (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ C.exp ↔ ExpDefinable C P :=
  Iff.rfl

end Lax822549Proofs.DescriptiveComplexity


