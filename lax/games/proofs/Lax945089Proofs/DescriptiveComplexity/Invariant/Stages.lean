/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Invariant.EquivK
import Lax945089Proofs.DescriptiveComplexity.FixedPointStep
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089.EhrenfeuchtGames
end Lax945089.EhrenfeuchtGames

namespace Lax945089.PebbleGames
end Lax945089.PebbleGames

namespace Lax945089.PebbleGames.StepDef
end Lax945089.PebbleGames.StepDef

namespace Lax945089Proofs.DescriptiveComplexity.StepDef
end Lax945089Proofs.DescriptiveComplexity.StepDef

namespace Lax945089Proofs.DescriptiveComplexity.StepDef.UsesRels
end Lax945089Proofs.DescriptiveComplexity.StepDef.UsesRels

namespace Lax945089Proofs.DescriptiveComplexity.StepDef.VarBound
end Lax945089Proofs.DescriptiveComplexity.StepDef.VarBound

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.EhrenfeuchtGames (qdepth)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.PebbleGames (RelsIn blockRelsExtend)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax945089.PebbleGames.StepDef (UsesRels VarBound)
end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (partStage)
end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# `≡ᵏ`-invariance of the fixed-point stages

The stages of a simultaneous first-order induction cannot separate
`≡ᵏ`-equivalent tuples, when `k` covers the induction's *variable budget*
(`DescriptiveComplexity.StepDef.VarBound`: each variable's arity plus the
quantifier depth of its step formula) and the equivalence is taken relative
to a family of relation symbols covering those of the induction
(`DescriptiveComplexity.StepDef.UsesRels`; every induction has a finite such
family, `DescriptiveComplexity.StepDef.exists_usesRels`). This is the reason
the unordered Abiteboul–Vianu theorem is about `P = PSPACE` rather than a
triviality: an inflationary or partial induction over a bare structure only
ever computes `≡ᵏ`-invariant relations, so everything it derives factors
through the `≡ᵏ`-classes.

The induction is one step of bookkeeping on top of the `k`-variable
invariance lemma (`DescriptiveComplexity.realize_formula_equivK`): the
previous stage is invariant by induction hypothesis, so expanding the
structure by it does not change `≡ᵏ`
(`DescriptiveComplexity.equivK_structure₁_eq`, the expansion lemma
`DescriptiveComplexity.equivK_inf_eq` read at a block expansion – the block's
own symbols joining the agreement family through
`DescriptiveComplexity.blockRelsExtend`), so the step formulas – within
budget – cannot separate equivalent tuples, so the next stage is invariant
(`DescriptiveComplexity.StepDef.next_invariant`). Neither iteration is
special: inflationary and partial stages inherit invariance from `next`
alone (`DescriptiveComplexity.StepDef.inflStage_invariant`,
`DescriptiveComplexity.StepDef.partStage_invariant`).

Every induction has a budget (`DescriptiveComplexity.StepDef.exists_varBound`):
`k` and the family are chosen *per definition*, which is exactly how the
invariant layer is consumed – each phase-G statement carries the `k` and the
symbols of the definition it starts from.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

/-! ### Invariant assignments -/

/-- An assignment of a block is *`≡ᵏ`-invariant* (relative to the agreement
family `S`) when each of its relations cannot separate `≡ᵏ`-equivalent
tuples, however its arguments are selected from the `k` coordinates. -/
def AssignInvariant (S : Set (Σ n, L.Relations n)) (A : Type) [L.Structure A]
    (k : ℕ) {B : Lax904597.SecondOrder.SOBlock} (ρ : B.Assignment A) : Prop :=
  ∀ (i : B.ι) (g : Fin (B.arity i) → Fin k) {v w : Fin k → A},
    EquivK (atomicAgreeOn S A k) v w →
      ((ρ i fun p => v (g p)) ↔ ρ i fun p => w (g p))

section Structure

variable [L.Structure A]

/-- The empty assignment is invariant. -/
theorem botAssign_invariant (B : Lax904597.SecondOrder.SOBlock) :
    AssignInvariant S A k (B.botAssign A) :=
  fun _ _ _ _ _ => Iff.rfl

/-! ### Expanding by an invariant assignment does not change `≡ᵏ` -/

/-- **Expanding the structure by an invariant assignment does not change
`≡ᵏ`**: the expansion lemma `DescriptiveComplexity.equivK_inf_eq`, read at the
block expansion `DescriptiveComplexity.SOBlock.structure₁`, the block symbols
joining the agreement family. -/
theorem equivK_structure₁_eq [Finite A] {B : Lax904597.SecondOrder.SOBlock} {ρ : B.Assignment A}
    (hρ : AssignInvariant S A k ρ) :
    EquivK (@atomicAgreeOn (L.sum B.lang) (Lax945089.PebbleGames.blockRelsExtend S B) A
        (B.structure₁ (L := L) ρ) k) =
      EquivK (atomicAgreeOn S A k) := by
  refine equivK_inf_eq (fun v w hvw => ?_) (fun v w hvw => ?_)
  · exact ⟨hvw.1, fun {l} r hr g => hvw.2 (Sum.inl r) hr g⟩
  · refine ⟨hvw.initial.1, ?_⟩
    intro l R hR g
    cases R with
    | inl r => exact hvw.initial.2 r hR g
    | inr r => exact hρ r.1 (fun p => g (Fin.cast r.2 p)) hvw

/-! ### The variable budget and the symbols of an induction -/

/-- Every induction has a variable budget: the block is finite. -/
theorem StepDef.exists_varBound (d : Lax535992.InflationaryFixedPoint.StepDef L) : ∃ k, d.VarBound k := by
  let := Fintype.ofFinite d.B.ι
  exact ⟨Finset.univ.sup fun i => d.B.arity i + Lax945089.EhrenfeuchtGames.qdepth (d.step i),
    fun i => Finset.le_sup (f := fun i => d.B.arity i + Lax945089.EhrenfeuchtGames.qdepth (d.step i))
      (Finset.mem_univ i)⟩

end Structure

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (exists_varBound)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

/-- A variable budget survives being raised. -/
theorem StepDef.VarBound.mono {d : Lax535992.InflationaryFixedPoint.StepDef L} {k k' : ℕ} (h : d.VarBound k)
    (hkk' : k ≤ k') : d.VarBound k' :=
  fun i => (h i).trans hkk'

end Structure

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.PebbleGames.StepDef.VarBound

export Lax945089Proofs.DescriptiveComplexity.StepDef.VarBound (mono)

end Lax945089.PebbleGames.StepDef.VarBound

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

/-! ### Invariance of the stages -/

variable [L.IsRelational] [Finite A]

/-- **One application of the step formulas preserves invariance**: the
`k`-variable invariance lemma, over the structure expanded by the (invariant)
current stage. -/
theorem StepDef.next_invariant (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) {ρ : d.B.Assignment A} (hρ : AssignInvariant S A k ρ) :
    AssignInvariant S A k (d.next ρ) := by
  intro i g v w hvw
  let := d.B.structure₁ (L := L) ρ
  have hroom : (Finset.image g Finset.univ).card + Lax945089.EhrenfeuchtGames.qdepth (d.step i) ≤ k := by
    have h1 : (Finset.image g Finset.univ).card ≤ d.B.arity i := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h2 := hd i
    omega
  exact realize_formula_equivK (d.step i) g hroom (hrels.1 i)
    ((equivK_structure₁_eq hρ).symm ▸ hvw)

end Structure

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (next_invariant)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

variable [L.IsRelational] [Finite A]

/-- Every stage of the inflationary iteration is `≡ᵏ`-invariant. -/
theorem StepDef.inflStage_invariant (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant S A k (d.inflStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.inflStage_succ]
    exact or_congr (ih i g hvw) (d.next_invariant hd hrels ih i g hvw)

end Structure

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (inflStage_invariant)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

variable [L.IsRelational] [Finite A]

/-- **The value of the inflationary iteration is `≡ᵏ`-invariant**: an
inflationary induction over a bare structure only computes `≡ᵏ`-invariant
relations. -/
theorem StepDef.inflLimit_invariant (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) :
    AssignInvariant S A k (d.inflLimit A) :=
  fun i g _ _ hvw => exists_congr fun n => d.inflStage_invariant hd hrels n i g hvw

end Structure

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (inflLimit_invariant)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

variable [L.IsRelational] [Finite A]

end Structure

end Lax945089Proofs.DescriptiveComplexity


