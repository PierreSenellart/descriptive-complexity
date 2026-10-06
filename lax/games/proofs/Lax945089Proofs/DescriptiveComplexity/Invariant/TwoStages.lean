/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Invariant.TwoInvariance
import Lax945089Proofs.DescriptiveComplexity.FixedPointInflationary
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

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.EhrenfeuchtGames (qdepth)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.PebbleGames (EquivK₂ atomicAgreeOn₂ blockRelsExtend)
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

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# An induction cannot separate two `k`-pebble equivalent structures

`DescriptiveComplexity.Invariant.Stages` carries `≡ᵏ`-invariance through the
stages of an inflationary induction *inside* one structure. The same argument,
run against the two-structure game of
`DescriptiveComplexity.Invariant.TwoPebble`, carries it *between* two
structures: stage by stage, the assignments computed on either side agree on
`k`-pebble equivalent tuples
(`DescriptiveComplexity.StepDef.inflStage_invariant₂`), and therefore so do
the limits, and therefore the output sentence is true on one structure exactly
when it is on the other (`DescriptiveComplexity.StepDef.ifpHolds_equivK₂`).

That last statement is what separates a Boolean query: a query distinguishing
two structures the duplicator can play forever on is not order-free
FO(IFP)-definable. Over bare sets, where `k` pebbles cannot count past `k`
(`DescriptiveComplexity.equivK₂_bare`), this is the inexpressibility of
`DescriptiveComplexity.EVEN` for order-free inflationary induction – the
failure of capture, since parity is decidable in polynomial time.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

/-! ### Jointly invariant assignments -/

/-- A pair of assignments of a block, one on each structure, is *jointly
`≡ᵏ`-invariant* when corresponding relations agree on `k`-pebble equivalent
tuples, however their arguments are selected from the `k` coordinates. -/
def AssignInvariant₂ (S : Set (Σ n, L.Relations n)) (M N : Type) [L.Structure M]
    [L.Structure N] (k : ℕ) {B : Lax904597.SecondOrder.SOBlock} (ρ : B.Assignment M) (σ : B.Assignment N) : Prop :=
  ∀ (i : B.ι) (g : Fin (B.arity i) → Fin k) {v : Fin k → M} {w : Fin k → N},
    Lax945089.PebbleGames.EquivK₂ (Lax945089.PebbleGames.atomicAgreeOn₂ S M N k) v w →
      ((ρ i fun p => v (g p)) ↔ σ i fun p => w (g p))

variable [L.Structure M] [L.Structure N]

/-- The pair of empty assignments is jointly invariant. -/
theorem botAssign_invariant₂ (B : Lax904597.SecondOrder.SOBlock) :
    AssignInvariant₂ S M N k (B.botAssign M) (B.botAssign N) := by
  intro _ _ _ _ _
  exact Iff.rfl

/-- **Expanding both structures by a jointly invariant pair of assignments
does not change the equivalence** – the two-structure expansion lemma, the one
that carries invariance from a stage to the next. -/
theorem equivK₂_structure₁_eq [Finite M] [Finite N] {B : Lax904597.SecondOrder.SOBlock} {ρ : B.Assignment M}
    {σ : B.Assignment N} (hρσ : AssignInvariant₂ S M N k ρ σ) :
    Lax945089.PebbleGames.EquivK₂ (@Lax945089.PebbleGames.atomicAgreeOn₂ (L.sum B.lang) (Lax945089.PebbleGames.blockRelsExtend S B) M N
        (B.structure₁ (L := L) ρ) (B.structure₁ (L := L) σ) k) =
      Lax945089.PebbleGames.EquivK₂ (Lax945089.PebbleGames.atomicAgreeOn₂ S M N k) := by
  refine equivK₂_inf_eq (fun v w hvw => ?_) (fun v w hvw => ?_)
  · exact ⟨hvw.1, fun {l} r hr g => hvw.2 (Sum.inl r) hr g⟩
  · refine ⟨hvw.initial.1, ?_⟩
    intro l R hR g
    cases R with
    | inl r => exact hvw.initial.2 r hR g
    | inr r => exact hρσ r.1 (fun p => g (Fin.cast r.2 p)) hvw

/-! ### The stages -/

variable [L.IsRelational] [Finite M] [Finite N]

/-- **One application of the step formulas preserves joint invariance**: the
two-structure `k`-variable invariance lemma, over the structures expanded by
the (jointly invariant) current stages. -/
theorem StepDef.next_invariant₂ (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k) (hrels : d.UsesRels S)
    {ρ : d.B.Assignment M} {σ : d.B.Assignment N} (hρσ : AssignInvariant₂ S M N k ρ σ) :
    AssignInvariant₂ S M N k (d.next ρ) (d.next σ) := by
  intro i g v w hvw
  let := d.B.structure₁ (L := L) ρ
  let := d.B.structure₁ (L := L) σ
  have hroom : (Finset.image g Finset.univ).card + Lax945089.EhrenfeuchtGames.qdepth (d.step i) ≤ k := by
    have h1 : (Finset.image g Finset.univ).card ≤ d.B.arity i := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h2 := hd i
    omega
  exact realize_formula_equivK₂ (d.step i) g hroom (hrels.1 i)
    ((equivK₂_structure₁_eq hρσ).symm ▸ hvw)

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (next_invariant₂)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

variable [L.Structure M] [L.Structure N]

variable [L.IsRelational] [Finite M] [Finite N]

/-- Corresponding stages of the inflationary iteration are jointly
invariant. -/
theorem StepDef.inflStage_invariant₂ (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant₂ S M N k (d.inflStage M n) (d.inflStage N n) := by
  induction n with
  | zero => exact botAssign_invariant₂ d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.inflStage_succ, d.inflStage_succ]
    exact or_congr (ih i g hvw) (d.next_invariant₂ hd hrels ih i g hvw)

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (inflStage_invariant₂)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

variable [L.Structure M] [L.Structure N]

variable [L.IsRelational] [Finite M] [Finite N]

/-- The two limits are jointly invariant. -/
theorem StepDef.inflLimit_invariant₂ (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) :
    AssignInvariant₂ S M N k (d.inflLimit M) (d.inflLimit N) :=
  fun i g _ _ hvw => exists_congr fun n => d.inflStage_invariant₂ hd hrels n i g hvw

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (inflLimit_invariant₂)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

variable [L.Structure M] [L.Structure N]

variable [L.IsRelational] [Finite M] [Finite N]

/-- **An order-free inflationary induction cannot separate two structures
carrying a `k`-pebble equivalent pair of tuples**, `k` covering both its
variable budget and the quantifier depth of its output sentence. This is the
Boolean-query form of `≡ᵏ`-invariance, and the one a capture statement needs:
the value of the induction is the same on both sides. -/
theorem StepDef.ifpHolds_equivK₂ (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k) (hrels : d.UsesRels S)
    (hout : Lax945089.EhrenfeuchtGames.qdepth d.out ≤ k) {v : Fin k → M} {w : Fin k → N}
    (hvw : Lax945089.PebbleGames.EquivK₂ (Lax945089.PebbleGames.atomicAgreeOn₂ S M N k) v w) : d.IFPHolds M ↔ d.IFPHolds N := by
  let instM := d.B.structure₁ (L := L) (d.inflLimit M)
  let instN := d.B.structure₁ (L := L) (d.inflLimit N)
  have hvw' : Lax945089.PebbleGames.EquivK₂ (@Lax945089.PebbleGames.atomicAgreeOn₂ (L.sum d.B.lang) (Lax945089.PebbleGames.blockRelsExtend S d.B) M N
      instM instN k) v w := by
    rw [equivK₂_structure₁_eq (d.inflLimit_invariant₂ hd hrels)]
    exact hvw
  exact realize_sentence_equivK₂ (M := M) (N := N) d.out hout hrels.2 hvw'

end Lax945089Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax945089Proofs.DescriptiveComplexity.StepDef (ifpHolds_equivK₂)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

variable [L.Structure M] [L.Structure N]

variable [L.IsRelational] [Finite M] [Finite N]

end Lax945089Proofs.DescriptiveComplexity


