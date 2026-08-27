/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointExpandLevels
import DescriptiveComplexity.TransitiveClosureReductionDet

/-!
# The whole polynomial hierarchy is closed under FO(LFP) reductions

`DescriptiveComplexity.FixedPointReductionClosure` closes PTIME, NP and coNP
under `≤ˡᶠᵖ`. This file does the same at every level
(`DescriptiveComplexity.mem_sigmaP_of_lfpReduction`,
`DescriptiveComplexity.mem_piP_of_lfpReduction`) and for `PH` itself
(`DescriptiveComplexity.mem_PH_of_lfpReduction`), and – a reduction of one
notion being a reduction of the wider ones – for `≤ᵗᶜ` and `≤ᵈᵗᶜ` too.

Only one ingredient is new, and it is the one that was missing at level 1:
`DescriptiveComplexity.exists_expand_sorealize` removes the reduction's
induction from a definition with a prefix of *any* length. Everything else is
the argument of the first level verbatim – pull the definition back through the
interpretation (`DescriptiveComplexity.sorealize_pullRelSO`), guard it with the
domain's inhabitedness, and re-quantify the order inside the first block
(`DescriptiveComplexity.sigmaSODefinable_of_orderPull`).

The universal levels come by complementation, as coNP did: a reduction
complements (`DescriptiveComplexity.LFPReduction.compl`), and `Πₖ` definability
is `Σₖ` definability of the complement
(`DescriptiveComplexity.piSODefinable_iff_compl`). Nothing here needs the
`Π`-polarity of the expansion theorem – though it has it, which is what would
be needed to close the levels without complementing.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂} {k : ℕ}

/-! ### The levels -/

/-- **`Σₖ₊₁`-definability is closed under FO(LFP) reductions**, at every level:
the membership sentence is pulled back through the interpretation, the
induction is eliminated from under the whole quantifier prefix
(`DescriptiveComplexity.exists_expand_sorealize`), and the order the reduction
uses is re-quantified inside the first block. -/
theorem SigmaSODefinable.of_lfpReduction_succ (f : P ≤ˡᶠᵖ Q)
    (h : SigmaSODefinable (k + 1) Q) : SigmaSODefinable (k + 1) P := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  let := f.tagFinite
  set I := f.toInterpretation with hI
  -- the target problem, pulled back through the interpretation alone
  let S : DecisionProblem ((L₁.sum Language.order).sum I.ind.B.lang) :=
    { Holds := fun A' inst =>
        Nonempty (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A' inst) ∧
          Q (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A' inst)
      iso_invariant := fun {M N} instM instN e =>
        and_congr ⟨fun hne => hne.map (I.toRel.mapRelLEquiv e),
            fun hne => hne.map (I.toRel.mapRelLEquiv e.symm)⟩
          (Q.iso_invariant (I.toRel.mapRelLEquiv e)) }
  have hSlen : (pullBlocks f.Tag f.dim Bs).length = k + 1 := by
    simpa [pullBlocks] using hlen
  have hS : ∀ (A' : Type) (inst : ((L₁.sum Language.order).sum I.ind.B.lang).Structure A'),
      Finite A' → Nonempty A' →
      (@DecisionProblem.Holds _ _ S A' inst ↔
        @SORealize _ A' inst (pullBlocks f.Tag f.dim Bs)
          ((soLangEmbed (pullBlocks f.Tag f.dim Bs) _).onSentence I.toRel.domNonemptyS ⊓
            pullRelSO Bs _ L₂ I.toRel φ) true) := by
    intro A' inst _ _
    rw [sorealize_inf_embed (pullBlocks f.Tag f.dim Bs) _ A' inst _ _ true,
      I.toRel.realize_domNonemptyS A']
    refine and_congr_right fun hne => ?_
    have : Finite (I.toRel.MapRel A') := I.toRel.mapRel_finite A'
    exact (hφ (I.toRel.MapRel A')).trans (sorealize_pullRelSO I.toRel A' Bs φ true)
  -- the induction is eliminated from under the prefix
  obtain ⟨Bs', χ, hlen', hχ⟩ :=
    exists_expand_sorealize I.ind (pullBlocks f.Tag f.dim Bs)
      (by intro hnil; rw [hnil] at hSlen; exact absurd hSlen (by simp)) _ true
  -- and the order is re-quantified inside the first block
  refine sigmaSODefinable_of_orderPull Bs' (hlen'.trans hSlen) χ ?_
  intro A _ _ _
  have key : ∀ lo : LinearOrder A,
      (letI := lo
       P A ↔ SORealize (L₁.sum Language.order) A Bs' χ true) := by
    intro lo
    let := lo
    have hfinI : Finite (I.Map A) := I.map_finite A
    have hne : Nonempty (I.Map A) := f.map_nonempty A
    have hpair : Q (I.Map A) ↔ (Nonempty (I.Map A) ∧ Q (I.Map A)) :=
      ⟨fun hQ => ⟨hne, hQ⟩, fun hh => hh.2⟩
    refine (f.correct A).trans (Iff.trans hpair (Iff.trans ?_
      (hχ A _ ‹Finite A› ‹Nonempty A›)))
    exact hS A (I.expStructure A) ‹Finite A› ‹Nonempty A›
  exact ⟨fun hP => ⟨finiteLinearOrder A, (key _).mp hP⟩, fun ⟨lo, h⟩ => (key lo).mpr h⟩

/-- **`Πₖ₊₁`-definability is closed under FO(LFP) reductions**, by
complementation. -/
theorem PiSODefinable.of_lfpReduction_succ (f : P ≤ˡᶠᵖ Q)
    (h : PiSODefinable (k + 1) Q) : PiSODefinable (k + 1) P :=
  (piSODefinable_iff_compl (k + 1) P).mpr
    (SigmaSODefinable.of_lfpReduction_succ f.compl
      ((piSODefinable_iff_compl (k + 1) Q).mp h))

/-! ### The classes -/

/-- **Every level `Σₖᵖ` is closed under FO(LFP) reductions.** -/
theorem mem_sigmaP_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ SigmaP k) : P ∈ SigmaP k := by
  cases k with
  | zero => exact mem_PTIME_of_lfpReduction f h
  | succ k => exact SigmaSODefinable.of_lfpReduction_succ f h

/-- **Every level `Πₖᵖ` is closed under FO(LFP) reductions.** -/
theorem mem_piP_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ PiP k) : P ∈ PiP k := by
  cases k with
  | zero =>
    exact mem_PTIME_of_lfpReduction f.compl h
  | succ k => exact PiSODefinable.of_lfpReduction_succ f h

/-- **The polynomial hierarchy is closed under FO(LFP) reductions.** -/
theorem mem_PH_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ PH) : P ∈ PH :=
  h.imp fun _ hk => mem_sigmaP_of_lfpReduction f hk

/-! ### The same, at the reduction notions below -/

/-- **Every level `Σₖᵖ` is closed under FO(TC) reductions.** -/
theorem mem_sigmaP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ SigmaP k) : P ∈ SigmaP k :=
  mem_sigmaP_of_lfpReduction f.toLFP h

/-- **Every level `Πₖᵖ` is closed under FO(TC) reductions.** -/
theorem mem_piP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ PiP k) : P ∈ PiP k :=
  mem_piP_of_lfpReduction f.toLFP h

/-- **The polynomial hierarchy is closed under FO(TC) reductions.** -/
theorem mem_PH_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ PH) : P ∈ PH :=
  mem_PH_of_lfpReduction f.toLFP h

/-- **Every level `Σₖᵖ` is closed under FO(DTC) reductions.** -/
theorem mem_sigmaP_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ SigmaP k) : P ∈ SigmaP k :=
  mem_sigmaP_of_tcReduction f.toTC h

/-- **Every level `Πₖᵖ` is closed under FO(DTC) reductions.** -/
theorem mem_piP_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ PiP k) : P ∈ PiP k :=
  mem_piP_of_tcReduction f.toTC h

/-- **The polynomial hierarchy is closed under FO(DTC) reductions.** -/
theorem mem_PH_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ PH) : P ∈ PH :=
  mem_PH_of_tcReduction f.toTC h

end DescriptiveComplexity
