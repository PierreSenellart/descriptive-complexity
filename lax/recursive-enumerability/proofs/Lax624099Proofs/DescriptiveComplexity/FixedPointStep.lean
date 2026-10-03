/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Lattice.Nat
import Lax624099Proofs.DescriptiveComplexity.Ordered
import Lax624099Proofs.DescriptiveComplexity.OrderedComposition
import Lax624099Proofs.DescriptiveComplexity.Padding
import Lax624099Proofs.DescriptiveComplexity.SecondOrder
import Lax624099Proofs.DescriptiveComplexity.SecondOrderPull
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.DescriptiveComplexity.SOBlock
end Lax624099Proofs.DescriptiveComplexity.SOBlock

/-!
# Simultaneous first-order inductions: one skeleton for IFP and PFP

The inflationary (FO(IFP)) and partial (FO(PFP)) fixed-point logics differ in
exactly one place – what one application of the step formulas does with the
previous stage. Everything else is shared: the data (a block of relation
variables, one first-order step formula per variable, an output sentence), the
notion of a stage, stabilization on finite structures, transport along
isomorphisms, and the pullback along a first-order interpretation. This file
provides that shared skeleton; the logics themselves are built on it in
`Lax624099Proofs.DescriptiveComplexity.FixedPointInflationary` and
`Lax624099Proofs.DescriptiveComplexity.FixedPointPartial`.

## The data

A `Lax624099Proofs.DescriptiveComplexity.StepDef` over `L` bundles a block `B` of relation
variables, one step *formula* per variable – a first-order formula over
`L.sum B.lang` whose free variables are the arguments of the variable – and an
output sentence over the same expanded vocabulary. This is one *simultaneous*
induction with a first-order output; nesting is treated by stratification, in
`Lax624099Proofs.DescriptiveComplexity.FixedPointInflationary`.

Unlike `Lax624099Proofs.DescriptiveComplexity.LFPDef`, whose rules are clausal *data* (the
library's Horn-program normal form), the step formulas here are unrestricted:
positivity is exactly what the inflationary and partial iterations dispense
with. `LFPDef` keeps its clausal form – the two are bridged in
`Lax624099Proofs.DescriptiveComplexity.FixedPointInflationary` (rules give a `StepDef`) and
`Lax624099Proofs.DescriptiveComplexity.FixedPointInflationaryLFP` (the converse translation).

## The two iterations

* `Lax624099Proofs.DescriptiveComplexity.StepDef.inflStage`: iterate
  `Lax624099Proofs.DescriptiveComplexity.StepDef.inflStep`, which *accumulates* the step
  formulas into the previous stage. The stages grow, so on a finite structure
  they reach a fixed point within the atom count
  (`Lax624099Proofs.DescriptiveComplexity.StepDef.isFixedPt_inflStep_card` – the height of the
  subset lattice, via
  `Lax624099Proofs.DescriptiveComplexity.exists_succ_eq_of_monotone_subset`), and their union
  `Lax624099Proofs.DescriptiveComplexity.StepDef.inflLimit` equals the stage at the atom count
  (`Lax624099Proofs.DescriptiveComplexity.StepDef.inflLimit_eq_stage_card`).
* `Lax624099Proofs.DescriptiveComplexity.StepDef.partStage`: iterate
  `Lax624099Proofs.DescriptiveComplexity.StepDef.next` itself, *replacing* the previous stage.
  Nothing grows, and the iteration may cycle forever; if some stage is a fixed
  point, all fixed stages are equal
  (`Lax624099Proofs.DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt`) and one is
  reached within `Nat.card` of the *assignment* type – the pigeonhole
  `Lax624099Proofs.DescriptiveComplexity.isFixedPt_iterate_card_iff`, exposed here as
  `Lax624099Proofs.DescriptiveComplexity.StepDef.exists_isFixedPt_partStage_iff`.

## Transport

Both iterations commute with transporting an assignment along an isomorphism
(`Lax624099Proofs.DescriptiveComplexity.StepDef.inflStage_map`,
`Lax624099Proofs.DescriptiveComplexity.StepDef.partStage_map`) and with the pullback of the
block through a first-order interpretation
(`Lax624099Proofs.DescriptiveComplexity.StepDef.inflStage_pull`,
`Lax624099Proofs.DescriptiveComplexity.StepDef.partStage_pull`, for the pulled definition
`Lax624099Proofs.DescriptiveComplexity.StepDef.pull`). Each is one commuting lemma about
`Lax624099Proofs.DescriptiveComplexity.StepDef.next` (`next_map`, `next_pull`) propagated along
the orbit; these are the lemmas isomorphism-invariance and closure under
reductions rest on, for every logic built on this skeleton.
-/

namespace Lax624099Proofs.DescriptiveComplexity

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
`Lax624099Proofs.DescriptiveComplexity.realize_sentence_of_equiv` does at the sentence level. -/

/-! ### The data of a simultaneous induction -/

namespace StepDef

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

/-! ### Stabilization on finite structures -/

section Stab

variable {A : Type} [L.Structure A] [Finite A]

end Stab

/-! ### Transport along isomorphisms -/

section Map

variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)

end Map

end StepDef

/-! ### Pullback through an interpretation -/

namespace StepDef

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

variable {A : Type} [L₁.Structure A]

end Pull

end StepDef

end Lax624099Proofs.DescriptiveComplexity


