/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointStratifyPartial
import DescriptiveComplexity.FixedPointPartialMachine
import DescriptiveComplexity.FixedPointReductionHierarchy

/-!
# PSPACE is closed under FO(LFP) reductions

`DescriptiveComplexity.mem_PSPACE_of_lfpReduction`: a problem reducing to a
polynomial-space problem by a polynomial-time reduction is in polynomial space.
With it, every class of this library from PTIME to PSPACE – and every level of
the polynomial hierarchy in between – is closed under `≤ˡᶠᵖ`, hence under
`≤ᵗᶜ` and `≤ᵈᵗᶜ`.

## The route, and why it is the fixed-point one

`DescriptiveComplexity.PSPACE` is defined by SO(TC), so the natural attempt is
to absorb the reduction's induction into the walk: give the walk's state a
copy of the induction's variables, iterate the induction in it, freeze, then
run the original walk. That works, and it is *the same construction* as the one
carried out here – but on the fixed-point side of the capture theorem it costs
one construction instead of two, because the pullback half is already built:
`DescriptiveComplexity.StepDef.pullRel` pulls a simultaneous iteration through
a relativized interpretation, where SO(TC) would need that written afresh.

So the proof goes: FO(≤, PFP) is PSPACE (`DescriptiveComplexity.PSPACE` through
`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`); the membership witness of
`Q` is pulled back through the reduction's interpretation
(`DescriptiveComplexity.StepDef.pfpHolds_pullRel`); and the reduction's own
induction is absorbed by
`DescriptiveComplexity.StepDef.pfpHolds_stratifyPFP` – an inflationary stratum
gating a partial one, which is the walk-with-a-preliminary-phase written as an
iteration.

That last step is where the earlier pessimism about FO(PFP) was wrong: what a
partial iteration cannot do is *gate itself*, and it does not have to – the
gate is an arity-`0` variable of the state, set by the inflationary stratum,
and the partial stratum is merely conjoined with it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **FO(≤, PFP) definability is closed under FO(LFP) reductions**: the
membership iteration is pulled back through the (order-extended)
interpretation, and the reduction's induction is absorbed as an inflationary
stratum gating it. -/
theorem PFPDefinable.of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : PFPDefinable Q) :
    PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  set I := f.toInterpretation with hI
  refine ⟨I.ind.stratifyPFP (d.pullRel I.ordExtend.toRel), ?_⟩
  intro A _ _ _ _
  let := I.mapLinearOrder A
  have : Finite (I.Map A) := I.map_finite A
  have : Nonempty (I.Map A) := f.map_nonempty A
  refine (f.correct A).trans ((hd (I.Map A)).trans ?_)
  -- the composite computes the pulled iteration over the induction's limit
  have hstrat := I.ind.pfpHolds_stratifyPFP (A := A) (d.pullRel I.ordExtend.toRel)
  refine Iff.trans ?_ hstrat.symm
  -- and the pulled iteration is the original, read on the order-extended universe
  let : ((L₁.sum Language.order).sum I.ordExtend.ind.B.lang).Structure A :=
    I.ordExtend.expStructure A
  have hpull := StepDef.pfpHolds_pullRel (A := A) d I.ordExtend.toRel
  refine Iff.trans ?_ hpull.symm
  exact (@StepDef.pfpHolds_equiv (L₂.sum Language.order) d (I.ordExtend.Map A) (I.Map A)
    (LFPInterpretation.mapStructure I.ordExtend A)
    (letI := I.mapLinearOrder A; sumOrderStructure L₂ (I.Map A))
    (I.ordExtendLEquiv A)).symm

/-- **PSPACE is closed under FO(LFP) reductions.** -/
theorem mem_PSPACE_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ PSPACE) : P ∈ PSPACE :=
  mem_PSPACE_of_pfpDefinable
    (PFPDefinable.of_lfpReduction f ((pfpDefinable_iff_mem_PSPACE Q).mpr h))

/-- **PSPACE is closed under FO(TC) reductions.** -/
theorem mem_PSPACE_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ PSPACE) : P ∈ PSPACE :=
  mem_PSPACE_of_lfpReduction f.toLFP h

/-- **PSPACE is closed under FO(DTC) reductions.** -/
theorem mem_PSPACE_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ PSPACE) : P ∈ PSPACE :=
  mem_PSPACE_of_tcReduction f.toTC h

/-- **SO(TC) definability is closed under FO(LFP) reductions** – the same
statement as `DescriptiveComplexity.mem_PSPACE_of_lfpReduction`, at the logic
PSPACE is defined by. -/
theorem SOTCDefinable.of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : SOTCDefinable Q) :
    SOTCDefinable P :=
  (mem_PSPACE_iff P).mp (mem_PSPACE_of_lfpReduction f ((mem_PSPACE_iff Q).mpr h))

end DescriptiveComplexity
