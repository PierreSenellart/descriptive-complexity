/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Exponential.SecondOrderFixedPoint
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

namespace Lax480241.SecondOrderFixedPoints
end Lax480241.SecondOrderFixedPoints

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.SecondOrderFixedPoints (SOLFPDefinable SOPFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The exponential classes: EXPTIME, NEXPTIME, EXPSPACE

The three classes, and the bridge theorems that let everything else about them
be inherited rather than reproved.

| | definition | equal, by theorem |
|---|---|---|
| `DescriptiveComplexity.EXPTIME` | SO(≤, LFP) | `PTIME.exp` |
| `DescriptiveComplexity.NEXPTIME` | `NP.exp` – ∃SO over the expanded universe | – |
| `DescriptiveComplexity.EXPSPACE` | SO(≤, PFP) | `PSPACE.exp` |

The library elsewhere splits definition from theorem the other way round –
`PTIME` is *defined* by SO-Horn and equals FO(LFP) by theorem, `PSPACE` is
*defined* by SO(TC) and equals FO(PFP) by theorem. At the exponential level the
fixpoint logic takes the definition slot, because there is no comparably
canonical restricted syntax to define these classes by, and because naming a
class after its fixpoint is what makes its statements readable: `EXPTIME ⊆
EXPSPACE` is SO(LFP) ⊆ SO(PFP).

## Why NEXPTIME is presented differently

Its literature spelling is existential *third*-order logic ([Leivant
1989][leivant1989descriptive]; [Hella–Turull-Torres
2006][hella2006higher]), and this development deliberately builds no
third-order syntax layer: the two fixpoint logics need none, since an expansion
has already lowered the type of the objects a second-order fixpoint ranges
over. A “Σ¹₁ over the expansion” definition would be no more informative than
`NP.exp`, since that is what `NP.exp` unfolds to. So NEXPTIME is *defined* as
the succinct-instance form of NP, and this is an honest and narrow gap: the
library does not prove `NEXPTIME = Σ²₁`, because it does not have the syntax to
state it. NEXPTIME still gets its logical reading – guess a relation over the
expanded universe, check a first-order condition there – its machine problem
and its complete problems, exactly like the other two.

## What is *not* claimed

SO(LFP) = EXPTIME and SO(PFP) = EXPSPACE are **definitions** here, so nothing
is asserted and no capture theorem is being claimed.
[Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint] is the reason these are the
right logics to name the classes after, cited as motivation and not as a
theorem proved here; it is stated in the relational (order-free, generic)
setting, which is a second reason not to cite it flatly.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The three classes -/

/-- **The class EXPSPACE**, defined as SO(≤, PFP) – equivalently, and with no
order in the statement at all, as SO(PFP)
(`DescriptiveComplexity.mem_EXPSPACE_iff_sopfpDefinableFree`): a partial fixed point over a
second-order universe. Equivalently, and by theorem, polynomial space read over
an exponential expansion (`DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`). -/
noncomputable def EXPSPACE : ComplexityClass :=
  .ofMem (fun P => Lax480241.SecondOrderFixedPoints.SOPFPDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sopfpDefinable_congr h)

/-- **The class NEXPTIME**: NP read over an exponential expansion – guess a
relation over the expanded universe, check a first-order condition there. See
the module docstring for why this one is presented as `NP.exp` rather than as a
fixpoint logic. -/
noncomputable def NEXPTIME : ComplexityClass := NP.exp

/-! ### Membership, unfolded -/

/-! ### The bridge theorems

Every later result about the exponential classes is stated about
`EXPTIME`/`EXPSPACE`/`NEXPTIME` and proved by rewriting along these, so that
the work happens once, at `DescriptiveComplexity.ComplexityClass.exp` and an
arbitrary class. -/

/-- **EXPSPACE is polynomial space on succinct instances.** -/
theorem EXPSPACE_eq_PSPACE_exp : EXPSPACE = PSPACE.exp :=
  ComplexityClass.ext (fun P => sopfpDefinable_iff_expDefinable P)
    fun P => cofinalHard_congr_mem (fun Q => sopfpDefinable_iff_expDefinable Q) P

/-! ### Hardness over relational vocabularies

The shape every hardness proof of the exponential catalog discharges, one per
class; each is `DescriptiveComplexity.cofinalHard_iff` read through the bridge
theorem. -/

theorem hard_EXPSPACE_iff (P : Lax904597.Problems.DecisionProblem L) :
    EXPSPACE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
        Lax480241.SecondOrderFixedPoints.SOPFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

theorem hard_NEXPTIME_iff (P : Lax904597.Problems.DecisionProblem L) :
    NEXPTIME.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
        ExpDefinable NP Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- A problem is EXPSPACE-hard as soon as every SO(≤, PFP) definable problem
reduces to it. -/
theorem EXPSPACE_hard_of_sopfpDefinable (P : Lax904597.Problems.DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
      Lax480241.SecondOrderFixedPoints.SOPFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : EXPSPACE.Hard P :=
  (hard_EXPSPACE_iff P).mpr h

/-- A problem is NEXPTIME-hard as soon as every problem NP-definable over an
expanded universe reduces to it. -/
theorem NEXPTIME_hard_of_expDefinable (P : Lax904597.Problems.DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
      ExpDefinable NP Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : NEXPTIME.Hard P :=
  (hard_NEXPTIME_iff P).mpr h

end Lax822549Proofs.DescriptiveComplexity


