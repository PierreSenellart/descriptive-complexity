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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {A : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

/-! ### Invariant assignments -/

/-- An assignment of a block is *`≡ᵏ`-invariant* (relative to the agreement
family `S`) when each of its relations cannot separate `≡ᵏ`-equivalent
tuples, however its arguments are selected from the `k` coordinates. -/
def AssignInvariant (S : Set (Σ n, L.Relations n)) (A : Type) [L.Structure A]
    (k : ℕ) {B : SOBlock} (ρ : B.Assignment A) : Prop :=
  ∀ (i : B.ι) (g : Fin (B.arity i) → Fin k) {v w : Fin k → A},
    EquivK (atomicAgreeOn S A k) v w →
      ((ρ i fun p => v (g p)) ↔ ρ i fun p => w (g p))

section Structure

variable [L.Structure A]

/-- The empty assignment is invariant. -/
theorem botAssign_invariant (B : SOBlock) :
    AssignInvariant S A k (B.botAssign A) :=
  fun _ _ _ _ _ => Iff.rfl

/-! ### Expanding by an invariant assignment does not change `≡ᵏ` -/

/-- The agreement family of the block expansion of a structure: the given
family on the base symbols, everything on the block symbols. -/
def blockRelsExtend (S : Set (Σ n, L.Relations n)) (B : SOBlock) :
    Set (Σ n, (L.sum B.lang).Relations n) :=
  fun x =>
    match x with
    | ⟨n, Sum.inl r⟩ => ⟨n, r⟩ ∈ S
    | ⟨_, Sum.inr _⟩ => True

/-- **Expanding the structure by an invariant assignment does not change
`≡ᵏ`**: the expansion lemma `DescriptiveComplexity.equivK_inf_eq`, read at the
block expansion `DescriptiveComplexity.SOBlock.structure₁`, the block symbols
joining the agreement family. -/
theorem equivK_structure₁_eq [Finite A] {B : SOBlock} {ρ : B.Assignment A}
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
def StepDef.VarBound (d : StepDef L) (k : ℕ) : Prop :=
  ∀ i, d.B.arity i + qdepth (d.step i) ≤ k

/-- Every induction has a variable budget: the block is finite. -/
theorem StepDef.exists_varBound (d : StepDef L) : ∃ k, d.VarBound k := by
  let := Fintype.ofFinite d.B.ι
  exact ⟨Finset.univ.sup fun i => d.B.arity i + qdepth (d.step i),
    fun i => Finset.le_sup (f := fun i => d.B.arity i + qdepth (d.step i))
      (Finset.mem_univ i)⟩

/-- A variable budget survives being raised. -/
theorem StepDef.VarBound.mono {d : StepDef L} {k k' : ℕ} (h : d.VarBound k)
    (hkk' : k ≤ k') : d.VarBound k' :=
  fun i => (h i).trans hkk'

/-- The base relation symbols of a simultaneous induction – of its step
formulas and its output sentence – lie in the family `S`. -/
def StepDef.UsesRels (d : StepDef L) (S : Set (Σ n, L.Relations n)) : Prop :=
  (∀ i, RelsIn (blockRelsExtend S d.B) (d.step i)) ∧
    RelsIn (blockRelsExtend S d.B) d.out

/-- A family of used symbols survives being enlarged. -/
theorem StepDef.UsesRels.mono {d : StepDef L} {S S' : Set (Σ n, L.Relations n)}
    (h : d.UsesRels S) (hSS' : S ⊆ S') : d.UsesRels S' := by
  have hext : blockRelsExtend S d.B ⊆ blockRelsExtend S' d.B := by
    rintro ⟨n, r | r⟩ hr
    · exact hSS' hr
    · trivial
  exact ⟨fun i => (h.1 i).mono hext, h.2.mono hext⟩

/-- **Every induction mentions finitely many base relation symbols**: the
finite agreement family relative to which its stages are invariant and its
refinement is definable. -/
theorem StepDef.exists_usesRels (d : StepDef L) :
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

/-! ### Invariance of the stages -/

variable [L.IsRelational] [Finite A]

/-- **One application of the step formulas preserves invariance**: the
`k`-variable invariance lemma, over the structure expanded by the (invariant)
current stage. -/
theorem StepDef.next_invariant (d : StepDef L) (hd : d.VarBound k)
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

/-- Every stage of the inflationary iteration is `≡ᵏ`-invariant. -/
theorem StepDef.inflStage_invariant (d : StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant S A k (d.inflStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.inflStage_succ]
    exact or_congr (ih i g hvw) (d.next_invariant hd hrels ih i g hvw)

/-- **The value of the inflationary iteration is `≡ᵏ`-invariant**: an
inflationary induction over a bare structure only computes `≡ᵏ`-invariant
relations. -/
theorem StepDef.inflLimit_invariant (d : StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) :
    AssignInvariant S A k (d.inflLimit A) :=
  fun i g _ _ hvw => exists_congr fun n => d.inflStage_invariant hd hrels n i g hvw

/-- Every stage of the partial iteration is `≡ᵏ`-invariant. -/
theorem StepDef.partStage_invariant (d : StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant S A k (d.partStage A n) := by
  induction n with
  | zero => exact botAssign_invariant d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.partStage_succ]
    exact d.next_invariant hd hrels ih i g hvw

end Structure

end DescriptiveComplexity
