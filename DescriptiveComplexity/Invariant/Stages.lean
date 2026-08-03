/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.EquivK
import DescriptiveComplexity.FixedPointStep

/-!
# `≡ᵏ`-invariance of the fixed-point stages

The stages of a simultaneous first-order induction cannot separate
`≡ᵏ`-equivalent tuples, when `k` covers the induction's *variable budget*
(`DescriptiveComplexity.StepDef.VarBound`: each variable's arity plus the
quantifier depth of its step formula). This is the reason the unordered
Abiteboul–Vianu theorem is about `P = PSPACE` rather than a triviality: an
inflationary or partial induction over a bare structure only ever computes
`≡ᵏ`-invariant relations, so everything it derives factors through the
`≡ᵏ`-classes.

The induction is one step of bookkeeping on top of the `k`-variable
invariance lemma (`DescriptiveComplexity.realize_formula_equivK`): the
previous stage is invariant by induction hypothesis, so expanding the
structure by it does not change `≡ᵏ`
(`DescriptiveComplexity.equivK_structure₁_eq`, the expansion lemma
`DescriptiveComplexity.equivK_inf_eq` read at a block expansion), so the step
formulas – within budget – cannot separate equivalent tuples, so the next
stage is invariant (`DescriptiveComplexity.StepDef.next_invariant`). Neither
iteration is special: inflationary and partial stages inherit invariance from
`next` alone (`DescriptiveComplexity.StepDef.inflStage_invariant`,
`DescriptiveComplexity.StepDef.partStage_invariant`).

Every induction has a budget (`DescriptiveComplexity.StepDef.exists_varBound`):
`k` is chosen *per definition*, which is exactly how the invariant layer is
consumed – each phase-G statement carries the `k` of the definition it starts
from.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ}

/-! ### Invariant assignments -/

/-- An assignment of a block is *`≡ᵏ`-invariant* when each of its relations
cannot separate `≡ᵏ`-equivalent tuples, however its arguments are selected
from the `k` coordinates. -/
def AssignInvariant (L : Language.{0, 0}) (A : Type) [L.Structure A] (k : ℕ)
    {B : SOBlock} (ρ : B.Assignment A) : Prop :=
  ∀ (i : B.ι) (g : Fin (B.arity i) → Fin k) {v w : Fin k → A},
    EquivK (atomicAgree L A k) v w →
      ((ρ i fun p => v (g p)) ↔ ρ i fun p => w (g p))

section Structure

variable [L.Structure A]

/-- The empty assignment is invariant. -/
theorem botAssign_invariant (B : SOBlock) :
    AssignInvariant L A k (B.botAssign A) :=
  fun _ _ _ _ _ => Iff.rfl

/-! ### Expanding by an invariant assignment does not change `≡ᵏ` -/

/-- **Expanding the structure by an invariant assignment does not change
`≡ᵏ`**: the expansion lemma `DescriptiveComplexity.equivK_inf_eq`, read at the
block expansion `DescriptiveComplexity.SOBlock.structure₁`. -/
theorem equivK_structure₁_eq [Finite A] {B : SOBlock} {ρ : B.Assignment A}
    (hρ : AssignInvariant L A k ρ) :
    EquivK (@atomicAgree (L.sum B.lang) A (B.structure₁ (L := L) ρ) k) =
      EquivK (atomicAgree L A k) := by
  refine equivK_inf_eq (fun v w hvw => ?_) (fun v w hvw => ?_)
  · exact ⟨hvw.1, fun {l} r g => hvw.2 (Sum.inl r) g⟩
  · refine ⟨hvw.initial.1, ?_⟩
    intro l R g
    cases R with
    | inl r => exact hvw.initial.2 r g
    | inr r => exact hρ r.1 (fun p => g (Fin.cast r.2 p)) hvw

/-! ### The variable budget of an induction -/

/-- The variable budget of a simultaneous induction: `k` covers each
variable's arity together with the quantifier depth of its step formula –
enough pebbles to hold the arguments and play out the quantifiers. -/
def StepDef.VarBound (d : StepDef L) (k : ℕ) : Prop :=
  ∀ i, d.B.arity i + qdepth (d.step i) ≤ k

/-- Every induction has a variable budget: the block is finite. -/
theorem StepDef.exists_varBound (d : StepDef L) : ∃ k, d.VarBound k := by
  letI := Fintype.ofFinite d.B.ι
  exact ⟨Finset.univ.sup fun i => d.B.arity i + qdepth (d.step i),
    fun i => Finset.le_sup (f := fun i => d.B.arity i + qdepth (d.step i))
      (Finset.mem_univ i)⟩

/-- A variable budget survives being raised. -/
theorem StepDef.VarBound.mono {d : StepDef L} {k k' : ℕ} (h : d.VarBound k)
    (hkk' : k ≤ k') : d.VarBound k' :=
  fun i => (h i).trans hkk'

/-! ### Invariance of the stages -/

variable [L.IsRelational] [Finite A]

/-- **One application of the step formulas preserves invariance**: the
`k`-variable invariance lemma, over the structure expanded by the (invariant)
current stage. -/
theorem StepDef.next_invariant (d : StepDef L) (hd : d.VarBound k)
    {ρ : d.B.Assignment A} (hρ : AssignInvariant L A k ρ) :
    AssignInvariant L A k (d.next ρ) := by
  intro i g v w hvw
  letI := d.B.structure₁ (L := L) ρ
  have hroom : (Finset.image g Finset.univ).card + qdepth (d.step i) ≤ k := by
    have h1 : (Finset.image g Finset.univ).card ≤ d.B.arity i := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h2 := hd i
    omega
  exact realize_formula_equivK (d.step i) g hroom
    ((equivK_structure₁_eq hρ).symm ▸ hvw)

/-- Every stage of the inflationary iteration is `≡ᵏ`-invariant. -/
theorem StepDef.inflStage_invariant (d : StepDef L) (hd : d.VarBound k) (n : ℕ) :
    AssignInvariant L A k (d.inflStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.inflStage_succ]
    exact or_congr (ih i g hvw) (d.next_invariant hd ih i g hvw)

/-- **The value of the inflationary iteration is `≡ᵏ`-invariant**: an
inflationary induction over a bare structure only computes `≡ᵏ`-invariant
relations. -/
theorem StepDef.inflLimit_invariant (d : StepDef L) (hd : d.VarBound k) :
    AssignInvariant L A k (d.inflLimit A) :=
  fun i g _ _ hvw => exists_congr fun n => d.inflStage_invariant hd n i g hvw

/-- Every stage of the partial iteration is `≡ᵏ`-invariant. -/
theorem StepDef.partStage_invariant (d : StepDef L) (hd : d.VarBound k) (n : ℕ) :
    AssignInvariant L A k (d.partStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.partStage_succ]
    exact d.next_invariant hd ih i g hvw

end Structure

end DescriptiveComplexity
