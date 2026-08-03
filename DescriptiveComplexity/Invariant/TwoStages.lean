/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.TwoInvariance
import DescriptiveComplexity.FixedPointInflationary

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} {k : ℕ} {S : Set (Σ n, L.Relations n)}

/-! ### Jointly invariant assignments -/

/-- A pair of assignments of a block, one on each structure, is *jointly
`≡ᵏ`-invariant* when corresponding relations agree on `k`-pebble equivalent
tuples, however their arguments are selected from the `k` coordinates. -/
def AssignInvariant₂ (S : Set (Σ n, L.Relations n)) (M N : Type) [L.Structure M]
    [L.Structure N] (k : ℕ) {B : SOBlock} (ρ : B.Assignment M) (σ : B.Assignment N) : Prop :=
  ∀ (i : B.ι) (g : Fin (B.arity i) → Fin k) {v : Fin k → M} {w : Fin k → N},
    EquivK₂ (atomicAgreeOn₂ S M N k) v w →
      ((ρ i fun p => v (g p)) ↔ σ i fun p => w (g p))

variable [L.Structure M] [L.Structure N]

/-- The pair of empty assignments is jointly invariant. -/
theorem botAssign_invariant₂ (B : SOBlock) :
    AssignInvariant₂ S M N k (B.botAssign M) (B.botAssign N) := by
  intro _ _ _ _ _
  exact Iff.rfl

/-- **Expanding both structures by a jointly invariant pair of assignments
does not change the equivalence** – the two-structure expansion lemma, the one
that carries invariance from a stage to the next. -/
theorem equivK₂_structure₁_eq [Finite M] [Finite N] {B : SOBlock} {ρ : B.Assignment M}
    {σ : B.Assignment N} (hρσ : AssignInvariant₂ S M N k ρ σ) :
    EquivK₂ (@atomicAgreeOn₂ (L.sum B.lang) (blockRelsExtend S B) M N
        (B.structure₁ (L := L) ρ) (B.structure₁ (L := L) σ) k) =
      EquivK₂ (atomicAgreeOn₂ S M N k) := by
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
theorem StepDef.next_invariant₂ (d : StepDef L) (hd : d.VarBound k) (hrels : d.UsesRels S)
    {ρ : d.B.Assignment M} {σ : d.B.Assignment N} (hρσ : AssignInvariant₂ S M N k ρ σ) :
    AssignInvariant₂ S M N k (d.next ρ) (d.next σ) := by
  intro i g v w hvw
  letI := d.B.structure₁ (L := L) ρ
  letI := d.B.structure₁ (L := L) σ
  have hroom : (Finset.image g Finset.univ).card + qdepth (d.step i) ≤ k := by
    have h1 : (Finset.image g Finset.univ).card ≤ d.B.arity i := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h2 := hd i
    omega
  exact realize_formula_equivK₂ (d.step i) g hroom (hrels.1 i)
    ((equivK₂_structure₁_eq hρσ).symm ▸ hvw)

/-- Corresponding stages of the inflationary iteration are jointly
invariant. -/
theorem StepDef.inflStage_invariant₂ (d : StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    AssignInvariant₂ S M N k (d.inflStage M n) (d.inflStage N n) := by
  induction n with
  | zero => exact botAssign_invariant₂ d.B
  | succ n ih =>
    intro i g v w hvw
    rw [d.inflStage_succ, d.inflStage_succ]
    exact or_congr (ih i g hvw) (d.next_invariant₂ hd hrels ih i g hvw)

/-- The two limits are jointly invariant. -/
theorem StepDef.inflLimit_invariant₂ (d : StepDef L) (hd : d.VarBound k)
    (hrels : d.UsesRels S) :
    AssignInvariant₂ S M N k (d.inflLimit M) (d.inflLimit N) :=
  fun i g _ _ hvw => exists_congr fun n => d.inflStage_invariant₂ hd hrels n i g hvw

/-- **An order-free inflationary induction cannot separate two structures
carrying a `k`-pebble equivalent pair of tuples**, `k` covering both its
variable budget and the quantifier depth of its output sentence. This is the
Boolean-query form of `≡ᵏ`-invariance, and the one a capture statement needs:
the value of the induction is the same on both sides. -/
theorem StepDef.ifpHolds_equivK₂ (d : StepDef L) (hd : d.VarBound k) (hrels : d.UsesRels S)
    (hout : qdepth d.out ≤ k) {v : Fin k → M} {w : Fin k → N}
    (hvw : EquivK₂ (atomicAgreeOn₂ S M N k) v w) : d.IFPHolds M ↔ d.IFPHolds N := by
  letI instM := d.B.structure₁ (L := L) (d.inflLimit M)
  letI instN := d.B.structure₁ (L := L) (d.inflLimit N)
  have hvw' : EquivK₂ (@atomicAgreeOn₂ (L.sum d.B.lang) (blockRelsExtend S d.B) M N
      instM instN k) v w := by
    rw [equivK₂_structure₁_eq (d.inflLimit_invariant₂ hd hrels)]
    exact hvw
  exact realize_sentence_equivK₂ (M := M) (N := N) d.out hout hrels.2 hvw'

end DescriptiveComplexity
