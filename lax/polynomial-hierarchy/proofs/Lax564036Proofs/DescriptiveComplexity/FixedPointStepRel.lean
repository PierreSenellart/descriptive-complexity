/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.FixedPointStep
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax564036Proofs.DescriptiveComplexity.OrderedComposition
import Lax564036Proofs.DescriptiveComplexity.SecondOrderPull
import Lax564036Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax564036Proofs.DescriptiveComplexity.SecondOrderNewPull
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

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax564036Proofs.DescriptiveComplexity.IFPDefinable
end Lax564036Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax564036Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax564036Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax564036Proofs.DescriptiveComplexity.SOBlock
end Lax564036Proofs.DescriptiveComplexity.SOBlock

namespace Lax564036Proofs.DescriptiveComplexity.StepDef
end Lax564036Proofs.DescriptiveComplexity.StepDef

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Pulling a simultaneous induction through a relativized interpretation

The transport lemmas of `DescriptiveComplexity.FixedPointStep`, redone for
interpretations with a *definable domain*
(`DescriptiveComplexity.RelFOInterpretation`) – and with them, **closure of
membership under relativized ordered reductions** `≤ʳᶠᵒ[≤]`
(`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`,
`DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`).

Why the fixed-point logics need it when the second-order ones did not: all the
library's hardness travels along relativized reductions (they are what a
*spanning* target problem requires), so bringing a problem of a class *back*
from a complete problem – `PSPACE ⊆ FO(≤, PFP)` via the machine problem in
`DescriptiveComplexity.FixedPointPartialMachine` – crosses a relativized
reduction in the membership direction. For the second-order classes membership
was always a direct sentence, and the crossing never happened.

## The construction

Everything mirrors the plain pullback (`DescriptiveComplexity.StepDef.pull`),
with the domain threaded through:

* the interpretation extends along a block with its domain unchanged
  (`DescriptiveComplexity.RelFOInterpretation.extendSORel`);
* an assignment of the block on the definable universe transfers to an
  assignment of the pulled block that holds *only in-domain* tuples
  (`DescriptiveComplexity.SOBlock.pullAssignRel`) – the transfer is injective
  (`DescriptiveComplexity.SOBlock.pullAssignRel_injective`), which is what
  carries fixed-point-ness back and forth for a *deterministic* iteration,
  where the existential-only transfer of
  `DescriptiveComplexity.SecondOrderNewPull` would not suffice;
* the step formula of a pulled variable is the guarded pullback of the
  original step (`DescriptiveComplexity.guardPullRel`, from
  `DescriptiveComplexity.RelFOInterpretation.pullRel`) *gated by the domain
  formulas of its arguments* (`DescriptiveComplexity.domGateF`), so that
  off-domain tuples are never derived and the stages stay in the image of the
  transfer;
* one application of the pulled step is the transfer of one application of
  the original (`DescriptiveComplexity.StepDef.next_pullRel`), whence the
  stages, limits, and values correspond
  (`DescriptiveComplexity.StepDef.ifpHolds_pullRel`,
  `DescriptiveComplexity.StepDef.pfpHolds_pullRel`).
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

/-! ### Extending a relativized interpretation along a block -/

/-- Extension of a relativized interpretation along a second-order quantifier
block: the underlying interpretation extends as
`DescriptiveComplexity.FOInterpretation.extendSO`, and the domain formula is
unchanged (lifted to the expanded source vocabulary, which it does not
use). -/
def RelFOInterpretation.extendSORel (I : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    (B : Lax904597.SecondOrder.SOBlock) :
    Lax904597.Relativized.RelFOInterpretation (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) Tag dm where
  toFOInterpretation := I.toFOInterpretation.extendSO B
  domFormula := fun t => LHom.sumInl.onFormula (I.domFormula t)

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax564036Proofs.DescriptiveComplexity.RelFOInterpretation (extendSORel)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

/-! ### Transferring assignments -/

/-- Transfer of an assignment on the definable universe to an assignment of
the pulled block: a pulled tuple is in the transferred relation when all its
argument points lie in the domain *and* the packed tuple is in the original
relation. Off-domain tuples are never held – which keeps the transfer
injective. -/
def SOBlock.pullAssignRel (B : Lax904597.SecondOrder.SOBlock) (I : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    {A : Type} [L₁.Structure A] (ρ : B.Assignment (I.MapRel A)) :
    (B.pull Tag dm).Assignment A :=
  fun p x =>
    ∃ h : ∀ k, (I.domFormula (p.2 k)).Realize fun j => x (finProdFinEquiv (k, j)),
      ρ p.1 fun k => ⟨(p.2 k, fun j => x (finProdFinEquiv (k, j))), h k⟩

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax564036Proofs.DescriptiveComplexity.SOBlock (pullAssignRel)

end Lax904597.SecondOrder.SOBlock

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

omit [L₂.IsRelational] in
/-- The workhorse characterization of the transfer: reading it at a tuple of
points whose components are known is reading the original assignment at those
points. -/
theorem SOBlock.pullAssignRel_iff (B : Lax904597.SecondOrder.SOBlock) (I : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    {A : Type} [L₁.Structure A] (ρ : B.Assignment (I.MapRel A)) {i : B.ι}
    {τ : Fin (B.arity i) → Tag} {x : Fin (B.arity i * dm) → A}
    (y : Fin (B.arity i) → I.MapRel A)
    (hy : ∀ k, (y k).1 = (τ k, fun j => x (finProdFinEquiv (k, j)))) :
    B.pullAssignRel I ρ ⟨i, τ⟩ x ↔ ρ i y := by
  constructor
  · rintro ⟨h, hρ⟩
    have hfun : (fun k => (⟨(τ k, fun j => x (finProdFinEquiv (k, j))), h k⟩ :
        I.MapRel A)) = y :=
      funext fun k => Subtype.ext (hy k).symm
    rwa [hfun] at hρ
  · intro hρ
    have h : ∀ k, (I.domFormula (τ k)).Realize fun j => x (finProdFinEquiv (k, j)) := by
      intro k
      have h2 := (y k).2
      rw [hy k] at h2
      exact h2
    refine ⟨h, ?_⟩
    have hfun : (fun k => (⟨(τ k, fun j => x (finProdFinEquiv (k, j))), h k⟩ :
        I.MapRel A)) = y :=
      funext fun k => Subtype.ext (hy k).symm
    rwa [hfun]

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax564036Proofs.DescriptiveComplexity.SOBlock (pullAssignRel_iff)

end Lax904597.SecondOrder.SOBlock

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

/-! ### The gated pullback of the step formulas -/

/-! ### The extended structure equivalence -/

omit [L₂.IsRelational] in
/-- The domain formula of the extended relativized interpretation means the
original domain formula. -/
theorem realize_extendSORel_domFormula (I : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    (B : Lax904597.SecondOrder.SOBlock) {A : Type} [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A)
    (t : Tag) (w : Fin dm → A) :
    (@Formula.Realize _ A ((B.pull Tag dm).structure₁ (L := L₁) σ) _
      ((I.extendSORel B).domFormula t) w) ↔ (I.domFormula t).Realize w := by
  let := (B.pull Tag dm).structure σ
  exact LHom.realize_onFormula LHom.sumInl (I.domFormula t)

/-- Points of the extended relativized universe are points of the original
one: the two subtypes are cut out by equivalent conditions. -/
noncomputable def extendSORelPointEquiv (I : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    (B : Lax904597.SecondOrder.SOBlock) (A : Type) [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A) :
    (letI := (B.pull Tag dm).structure σ
     (I.extendSORel B).MapRel A) ≃ I.MapRel A :=
  letI := (B.pull Tag dm).structure σ
  Equiv.subtypeEquiv (Equiv.refl _) fun a =>
    realize_extendSORel_domFormula I B σ a.1 a.2

/-! ### The pulled induction and its stages -/

namespace StepDef

end StepDef

/-! ### Closure under relativized ordered reductions -/

section Closure

end Closure

end Lax564036Proofs.DescriptiveComplexity


