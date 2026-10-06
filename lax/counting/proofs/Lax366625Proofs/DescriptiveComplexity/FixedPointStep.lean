/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Iterate
import Lax366625Proofs.DescriptiveComplexity.FixedPoint
import Lax366625Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax366625Proofs.DescriptiveComplexity.OrderedComposition
import Lax366625Proofs.DescriptiveComplexity.SecondOrderPull
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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

namespace Lax366625Proofs.DescriptiveComplexity.SOBlock
end Lax366625Proofs.DescriptiveComplexity.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity.StepDef
end Lax366625Proofs.DescriptiveComplexity.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax366625Proofs.DescriptiveComplexity

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

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax366625Proofs.DescriptiveComplexity.SOBlock (mapAssign_botAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

instance {B : Lax904597.SecondOrder.SOBlock} {A : Type} [Finite A] : Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))

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

theorem inflStage_succ (n : ℕ) :
    d.inflStage A (n + 1) = d.inflStep (d.inflStage A n) :=
  Function.iterate_succ_apply' d.inflStep n (d.B.botAssign A)

end Semantics

end StepDef

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStage_succ)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStage_le_succ)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStage_le_of_le)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (exists_inflStage_succ_eq)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (isFixedPt_inflStep_card)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStage_eq_of_card_le)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflLimit_eq_stage_card)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (next_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- The inflationary step commutes with transport along an isomorphism. -/
theorem inflStep_map (ρ : d.B.Assignment M) :
    d.inflStep (d.B.mapAssign e.toEquiv ρ) = d.B.mapAssign e.toEquiv (d.inflStep ρ) := by
  funext i x
  have h := congrFun (congrFun (d.next_map e ρ) i) x
  exact congrArg (fun p => d.B.mapAssign e.toEquiv ρ i x ∨ p) h

end Map

end StepDef

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStep_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- The inflationary stages transport along an isomorphism. -/
theorem inflStage_map (n : ℕ) :
    d.inflStage N n = d.B.mapAssign e.toEquiv (d.inflStage M n) := by
  induction n with
  | zero => exact (d.B.mapAssign_botAssign e.toEquiv).symm
  | succ n ih => rw [d.inflStage_succ, d.inflStage_succ, ih, d.inflStep_map]

end Map

end StepDef

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflStage_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef L)

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

/-- The value of the inflationary iteration transports along an
isomorphism. -/
theorem inflLimit_map : d.inflLimit N = d.B.mapAssign e.toEquiv (d.inflLimit M) := by
  funext i x
  refine propext ?_
  change (∃ n, d.inflStage N n i x) ↔ ∃ n, d.inflStage M n i fun j => e.toEquiv.symm (x j)
  refine exists_congr fun n => iff_of_eq ?_
  exact congrFun (congrFun (d.inflStage_map e n) i) x

end Map

end StepDef

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflLimit_map)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity


