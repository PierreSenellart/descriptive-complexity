/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Iterate
import Lax822549Proofs.DescriptiveComplexity.FixedPoint
import Lax822549Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax822549Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull
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

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.StepDef
end Lax822549Proofs.DescriptiveComplexity.StepDef

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (instFiniteAssignment)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# Simultaneous first-order inductions: one skeleton for IFP and PFP

The inflationary (FO(IFP)) and partial (FO(PFP)) fixed-point logics differ in
exactly one place – what one application of the step formulas does with the
previous stage. Everything else is shared: the data (a block of relation
variables, one first-order step formula per variable, an output sentence), the
notion of a stage, stabilization on finite structures, transport along
isomorphisms, and the pullback along a first-order interpretation. This file
provides that shared skeleton; the logics themselves are built on it in
`DescriptiveComplexity.FixedPointInflationary` and
`DescriptiveComplexity.FixedPointPartial`.

## The data

A `DescriptiveComplexity.StepDef` over `L` bundles a block `B` of relation
variables, one step *formula* per variable – a first-order formula over
`L.sum B.lang` whose free variables are the arguments of the variable – and an
output sentence over the same expanded vocabulary. This is one *simultaneous*
induction with a first-order output; nesting is treated by stratification, in
`DescriptiveComplexity.FixedPointInflationary`.

Unlike `DescriptiveComplexity.LFPDef`, whose rules are clausal *data* (the
library's Horn-program normal form), the step formulas here are unrestricted:
positivity is exactly what the inflationary and partial iterations dispense
with. `LFPDef` keeps its clausal form – the two are bridged in
`DescriptiveComplexity.FixedPointInflationary` (rules give a `StepDef`) and
`DescriptiveComplexity.FixedPointInflationaryLFP` (the converse translation).

## The two iterations

* `DescriptiveComplexity.StepDef.inflStage`: iterate
  `DescriptiveComplexity.StepDef.inflStep`, which *accumulates* the step
  formulas into the previous stage. The stages grow, so on a finite structure
  they reach a fixed point within the atom count
  (`DescriptiveComplexity.StepDef.isFixedPt_inflStep_card` – the height of the
  subset lattice, via
  `DescriptiveComplexity.exists_succ_eq_of_monotone_subset`), and their union
  `DescriptiveComplexity.StepDef.inflLimit` equals the stage at the atom count
  (`DescriptiveComplexity.StepDef.inflLimit_eq_stage_card`).
* `DescriptiveComplexity.StepDef.partStage`: iterate
  `DescriptiveComplexity.StepDef.next` itself, *replacing* the previous stage.
  Nothing grows, and the iteration may cycle forever; if some stage is a fixed
  point, all fixed stages are equal
  (`DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt`) and one is
  reached within `Nat.card` of the *assignment* type – the pigeonhole
  `DescriptiveComplexity.isFixedPt_iterate_card_iff`, exposed here as
  `DescriptiveComplexity.StepDef.exists_isFixedPt_partStage_iff`.

## Transport

Both iterations commute with transporting an assignment along an isomorphism
(`DescriptiveComplexity.StepDef.inflStage_map`,
`DescriptiveComplexity.StepDef.partStage_map`) and with the pullback of the
block through a first-order interpretation
(`DescriptiveComplexity.StepDef.inflStage_pull`,
`DescriptiveComplexity.StepDef.partStage_pull`, for the pulled definition
`DescriptiveComplexity.StepDef.pull`). Each is one commuting lemma about
`DescriptiveComplexity.StepDef.next` (`next_map`, `next_pull`) propagated along
the orbit; these are the lemmas isomorphism-invariance and closure under
reductions rest on, for every logic built on this skeleton.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### Assignments form a finite type -/

/-- Transport along an equivalence maps the empty assignment to the empty
assignment. -/
theorem SOBlock.mapAssign_botAssign (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A') :
    B.mapAssign e (B.botAssign A) = B.botAssign A' :=
  rfl

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (mapAssign_botAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### Realization transport with explicit structures

The structures a stage is read against are block expansions, which are not
instances; this is `FirstOrder.Language.StrongHomClass.realize_formula` with
the two structures passed explicitly, exactly as
`DescriptiveComplexity.realize_sentence_of_equiv` does at the sentence level. -/

theorem realize_formula_of_equiv {L' : Language.{0, 0}} {M N : Type} {α : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (φ : L'.Formula α) (v : α → M) :
    @Formula.Realize L' N instN α φ (fun a => e (v a)) ↔
      @Formula.Realize L' M instM α φ v :=
  letI := instM
  letI := instN
  StrongHomClass.realize_formula φ (g := e)

/-! ### The data of a simultaneous induction -/

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

theorem partStage_succ (n : ℕ) :
    d.partStage A (n + 1) = d.next (d.partStage A n) :=
  Function.iterate_succ_apply' d.next n (d.B.botAssign A)

end Semantics

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (partStage_succ)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

/-- Two partial stages that are both fixed points of the step are equal: the
value of a converging partial iteration does not depend on which stable stage
witnesses the convergence. -/
theorem partStage_eq_of_isFixedPt {m n : ℕ} (hm : IsFixedPt d.next (d.partStage A m))
    (hn : IsFixedPt d.next (d.partStage A n)) : d.partStage A m = d.partStage A n := by
  rcases le_total m n with h | h
  · exact (iterate_eq_of_isFixedPt hm h).symm
  · exact iterate_eq_of_isFixedPt hn h

end Semantics

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (partStage_eq_of_isFixedPt)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

/-! ### Stabilization on finite structures -/

section Stab

end Stab

/-! ### Transport along isomorphisms -/

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- One application of the step formulas commutes with transporting the
assignment along an isomorphism: the step formulas cannot tell isomorphic
expanded structures apart. -/
theorem next_map (ρ : d.B.Assignment M) :
    d.next (d.B.mapAssign e.toEquiv ρ) = d.B.mapAssign e.toEquiv (d.next ρ) := by
  funext i x
  refine propext ?_
  have h := realize_formula_of_equiv (d.B.extendEquiv' (L' := L) e ρ) (d.step i)
    (fun j => e.toEquiv.symm (x j))
  refine Iff.trans (iff_of_eq (congrArg _ ?_)) h
  exact funext fun j => (e.toEquiv.apply_symm_apply (x j)).symm

end Map

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (next_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- The partial stages transport along an isomorphism. -/
theorem partStage_map (n : ℕ) :
    d.partStage N n = d.B.mapAssign e.toEquiv (d.partStage M n) := by
  induction n with
  | zero => exact (d.B.mapAssign_botAssign e.toEquiv).symm
  | succ n ih => rw [d.partStage_succ, d.partStage_succ, ih, d.next_map]

end Map

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (partStage_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- Being a fixed point of the step is insensitive to transporting the
assignment along an isomorphism. -/
theorem isFixedPt_next_map_iff (ρ : d.B.Assignment M) :
    IsFixedPt d.next (d.B.mapAssign e.toEquiv ρ) ↔ IsFixedPt d.next ρ := by
  have hinj : Function.Injective (d.B.mapAssign (A := M) (A' := N) e.toEquiv) :=
    (d.B.assignEquiv e.toEquiv).injective
  exact ⟨fun h => hinj ((d.next_map e ρ).symm.trans h),
    fun h => (d.next_map e ρ).trans (congrArg _ h)⟩

end Map

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (isFixedPt_next_map_iff)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

end Map

end StepDef

/-! ### Pullback through an interpretation -/

namespace StepDef

section Pull

end Pull

end StepDef

end Lax822549Proofs.DescriptiveComplexity


