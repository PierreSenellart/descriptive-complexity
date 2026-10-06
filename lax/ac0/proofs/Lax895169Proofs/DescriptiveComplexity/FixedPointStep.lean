/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.Iterate
import Lax895169Proofs.DescriptiveComplexity.FixedPoint
import Lax895169Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax895169Proofs.DescriptiveComplexity.OrderedComposition
import Lax895169Proofs.DescriptiveComplexity.SecondOrderPull
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity.SOBlock
end Lax895169Proofs.DescriptiveComplexity.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity.StepDef
end Lax895169Proofs.DescriptiveComplexity.StepDef

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

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

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### Assignments form a finite type -/

instance {B : Lax904597.SecondOrder.SOBlock} {A : Type} [Finite A] : Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))

/-! ### Realization transport with explicit structures

The structures a stage is read against are block expansions, which are not
instances; this is `FirstOrder.Language.StrongHomClass.realize_formula` with
the two structures passed explicitly, exactly as
`DescriptiveComplexity.realize_sentence_of_equiv` does at the sentence level. -/

/-! ### The data of a simultaneous induction -/

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

theorem inflStage_succ (n : ℕ) :
    d.inflStage A (n + 1) = d.inflStep (d.inflStage A n) :=
  Function.iterate_succ_apply' d.inflStep n (d.B.botAssign A)

end Semantics

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (inflStage_succ)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

/-- The inflationary stages increase. -/
theorem inflStage_le_succ (n : ℕ) (i : d.B.ι) (x : Fin (d.B.arity i) → A)
    (h : d.inflStage A n i x) : d.inflStage A (n + 1) i x := by
  rw [d.inflStage_succ]
  exact Or.inl h

end Semantics

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (inflStage_le_succ)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

/-- The inflationary stages increase, monotonically. -/
theorem inflStage_le_of_le {m n : ℕ} (hmn : m ≤ n) (i : d.B.ι)
    (x : Fin (d.B.arity i) → A) (h : d.inflStage A m i x) : d.inflStage A n i x := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact d.inflStage_le_succ n i x (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

end Semantics

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (inflStage_le_of_le)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

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

variable {A : Type} [L.Structure A] [Finite A]

variable (A) in
/-- The inflationary stages plateau within the atom count. -/
theorem exists_inflStage_succ_eq :
    ∃ N ≤ Nat.card (BAtom d.B A), d.inflStage A (N + 1) = d.inflStage A N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => {q : BAtom d.B A | d.inflStage A n q.1 q.2})
    (fun n q hq => d.inflStage_le_succ n q.1 q.2 hq)
  refine ⟨N, hN, ?_⟩
  funext i x
  exact propext ⟨fun h => (Set.ext_iff.mp heq ⟨i, x⟩).mp h,
    fun h => (Set.ext_iff.mp heq ⟨i, x⟩).mpr h⟩

end Stab

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (exists_inflStage_succ_eq)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Stab

variable {A : Type} [L.Structure A] [Finite A]

variable (A) in
/-- **The inflationary iteration reaches a fixed point within the atom
count** – the height of the subset lattice of the block's atoms, not the
number of assignments. -/
theorem isFixedPt_inflStep_card :
    IsFixedPt d.inflStep (d.inflStage A (Nat.card (BAtom d.B A))) := by
  obtain ⟨N, hN, heq⟩ := d.exists_inflStage_succ_eq A
  have hfix : IsFixedPt d.inflStep (d.inflStage A N) :=
    (Function.iterate_succ_apply' d.inflStep N (d.B.botAssign A)).symm.trans heq
  have hc : d.inflStage A (Nat.card (BAtom d.B A)) = d.inflStage A N :=
    iterate_eq_of_isFixedPt hfix hN
  rw [hc]
  exact hfix

end Stab

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (isFixedPt_inflStep_card)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Stab

variable {A : Type} [L.Structure A] [Finite A]

/-- The inflationary stages are constant from the atom count on. -/
theorem inflStage_eq_of_card_le {n : ℕ} (hn : Nat.card (BAtom d.B A) ≤ n) :
    d.inflStage A n = d.inflStage A (Nat.card (BAtom d.B A)) :=
  iterate_eq_of_isFixedPt (d.isFixedPt_inflStep_card A) hn

end Stab

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (inflStage_eq_of_card_le)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Stab

variable {A : Type} [L.Structure A] [Finite A]

variable (A) in
/-- On a finite structure, the value of the inflationary iteration is the
stage at the atom count. -/
theorem inflLimit_eq_stage_card :
    d.inflLimit A = d.inflStage A (Nat.card (BAtom d.B A)) := by
  funext i x
  refine propext ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨n, hn⟩
  rcases le_or_gt n (Nat.card (BAtom d.B A)) with hle | hlt
  · exact d.inflStage_le_of_le hle i x hn
  · rw [← d.inflStage_eq_of_card_le hlt.le]
    exact hn

end Stab

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (inflLimit_eq_stage_card)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Stab

variable {A : Type} [L.Structure A] [Finite A]

variable (A) in
/-- The value of the inflationary iteration is a fixed point of the
inflationary step. -/
theorem isFixedPt_inflStep_inflLimit : IsFixedPt d.inflStep (d.inflLimit A) := by
  rw [d.inflLimit_eq_stage_card A]
  exact d.isFixedPt_inflStep_card A

end Stab

end StepDef

end Lax895169Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax895169Proofs.DescriptiveComplexity.StepDef (isFixedPt_inflStep_inflLimit)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Stab

variable {A : Type} [L.Structure A] [Finite A]

end Stab

/-! ### Transport along isomorphisms -/

section Map

end Map

end StepDef

/-! ### Pullback through an interpretation -/

namespace StepDef

section Pull

end Pull

end StepDef

end Lax895169Proofs.DescriptiveComplexity


