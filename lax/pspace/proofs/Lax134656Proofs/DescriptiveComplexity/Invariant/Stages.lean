/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Invariant.EquivK
import Lax134656Proofs.DescriptiveComplexity.FixedPointStep
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity.StepDef
end Lax134656Proofs.DescriptiveComplexity.StepDef

namespace Lax134656Proofs.DescriptiveComplexity.StepDef.UsesRels
end Lax134656Proofs.DescriptiveComplexity.StepDef.UsesRels

namespace Lax134656Proofs.DescriptiveComplexity.StepDef.VarBound
end Lax134656Proofs.DescriptiveComplexity.StepDef.VarBound

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (partStage)
end Lax535992.InflationaryFixedPoint.StepDef

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

namespace Lax134656Proofs.DescriptiveComplexity

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

/-- The agreement family of the block expansion of a structure: the given
family on the base symbols, everything on the block symbols. -/
def blockRelsExtend (S : Set (Σ n, L.Relations n)) (B : Lax904597.SecondOrder.SOBlock) :
    Set (Σ n, (L.sum B.lang).Relations n) :=
  fun x =>
    match x with
    | ⟨n, Sum.inl r⟩ => ⟨n, r⟩ ∈ S
    | ⟨_, Sum.inr _⟩ => True

/-- **Expanding the structure by an invariant assignment does not change
`≡ᵏ`**: the expansion lemma `DescriptiveComplexity.equivK_inf_eq`, read at the
block expansion `DescriptiveComplexity.SOBlock.structure₁`, the block symbols
joining the agreement family. -/
theorem equivK_structure₁_eq [Finite A] {B : Lax904597.SecondOrder.SOBlock} {ρ : B.Assignment A}
    (hρ : AssignInvariant S A k ρ) :
    EquivK (@atomicAgreeOn (L.sum B.lang) (blockRelsExtend S B) A
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

/-- The variable budget of a simultaneous induction: `k` covers each
variable's arity together with the quantifier depth of its step formula –
enough pebbles to hold the arguments and play out the quantifiers. -/
def StepDef.VarBound (d : Lax535992.InflationaryFixedPoint.StepDef L) (k : ℕ) : Prop :=
  ∀ i, d.B.arity i + qdepth (d.step i) ≤ k

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (VarBound)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

/-- Every induction has a variable budget: the block is finite. -/
theorem StepDef.exists_varBound (d : Lax535992.InflationaryFixedPoint.StepDef L) : ∃ k, d.VarBound k := by
  let := Fintype.ofFinite d.B.ι
  exact ⟨Finset.univ.sup fun i => d.B.arity i + qdepth (d.step i),
    fun i => Finset.le_sup (f := fun i => d.B.arity i + qdepth (d.step i))
      (Finset.mem_univ i)⟩

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (exists_varBound)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

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

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.VarBound

export Lax134656Proofs.DescriptiveComplexity.StepDef.VarBound (mono)

end Lax535992.InflationaryFixedPoint.StepDef.VarBound

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

/-- The base relation symbols of a simultaneous induction – of its step
formulas and its output sentence – lie in the family `S`. -/
def StepDef.UsesRels (d : Lax535992.InflationaryFixedPoint.StepDef L) (S : Set (Σ n, L.Relations n)) : Prop :=
  (∀ i, RelsIn (blockRelsExtend S d.B) (d.step i)) ∧
    RelsIn (blockRelsExtend S d.B) d.out

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (UsesRels)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

/-- **Every induction mentions finitely many base relation symbols**: the
finite agreement family relative to which its stages are invariant and its
refinement is definable. -/
theorem StepDef.exists_usesRels (d : Lax535992.InflationaryFixedPoint.StepDef L) :
    ∃ S : Set (Σ n, L.Relations n), S.Finite ∧ d.UsesRels S := by
  classical
  let := Fintype.ofFinite d.B.ι
  -- the base-symbol part of the symbols of a formula over the expansion
  let base : Set (Σ n, (L.sum d.B.lang).Relations n) → Set (Σ n, L.Relations n) :=
    fun T => {x | (⟨x.1, Sum.inl x.2⟩ : Σ n, (L.sum d.B.lang).Relations n) ∈ T}
  have hbase : ∀ {T}, T.Finite → (base T).Finite := by
    intro T hT
    have hinj : Function.Injective
        (fun x : Σ n, L.Relations n =>
          (⟨x.1, Sum.inl x.2⟩ : Σ n, (L.sum d.B.lang).Relations n)) := by
      rintro ⟨n, r⟩ ⟨n', r'⟩ h
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl : r = r' := Sum.inl_injective (eq_of_heq h2)
      rfl
    exact Set.Finite.preimage hinj.injOn hT
  refine ⟨(⋃ i, base (relsOf (d.step i))) ∪ base (relsOf d.out),
    ((Set.finite_iUnion fun i => hbase (relsOf_finite _)).union
      (hbase (relsOf_finite _))), ?_, ?_⟩
  · intro i
    refine (relsIn_relsOf (d.step i)).mono ?_
    rintro ⟨n, r | r⟩ hr
    · exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hr⟩)
    · trivial
  · refine (relsIn_relsOf d.out).mono ?_
    rintro ⟨n, r | r⟩ hr
    · exact Set.mem_union_right _ hr
    · trivial

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (exists_usesRels)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

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
  have hroom : (Finset.image g Finset.univ).card + qdepth (d.step i) ≤ k := by
    have h1 : (Finset.image g Finset.univ).card ≤ d.B.arity i := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h2 := hd i
    omega
  exact realize_formula_equivK (d.step i) g hroom (hrels.1 i)
    ((equivK_structure₁_eq hρ).symm ▸ hvw)

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (next_invariant)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

variable [L.IsRelational] [Finite A]

/-- Every stage of the partial iteration is `≡ᵏ`-invariant. -/
theorem StepDef.partStage_invariant (d : Lax535992.InflationaryFixedPoint.StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant S A k (d.partStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.partStage_succ]
    exact d.next_invariant hd hrels ih i g hvw

end Structure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (partStage_invariant)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

section Structure

variable [L.Structure A]

variable [L.IsRelational] [Finite A]

end Structure

end Lax134656Proofs.DescriptiveComplexity


