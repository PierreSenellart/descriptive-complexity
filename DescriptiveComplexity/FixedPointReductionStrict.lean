/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointReductionClosure
import DescriptiveComplexity.Problems.Even
import DescriptiveComplexity.Problems.Parity

/-!
# FO(LFP) reductions are strictly stronger than first-order ones

`DescriptiveComplexity.FOReduction.toLFP` embeds every first-order reduction
into the FO(LFP) ones. This file shows the embedding is **strict**, and
unconditionally: there is a problem to which EVEN reduces in FO(LFP) and to
which it reduces by no first-order reduction at all
(`DescriptiveComplexity.exists_lfpReduction_not_orderedReduction`).

The witness is as small as it can be. Let `NONEMPTYMARK` be “the marked subset
is nonempty”, over the vocabulary of a marked set
(`DescriptiveComplexity.Problems.Parity`). It is first-order definable – one
existential quantifier – so nothing that first-order reduces to it is harder
than a first-order sentence, and EVEN is not
(`DescriptiveComplexity.even_not_foDefinable`,
`DescriptiveComplexity.even_not_le_of_foDefinable`). Yet EVEN *does* FO(LFP)
reduce to it: mark every element if the universe is even, none if it is odd.
Deciding which is a polynomial-time question, so an induction settles it – the
one already at hand, since EVEN is in PTIME – and the reduction's marking
formula is that induction's output sentence, read with a free variable it
ignores.

Two things to read off this.

* The gap is not about *hardness*: EVEN is in LOGSPACE, `NONEMPTYMARK` is
  first-order, and neither is hard for anything. It is about what a reduction
  may *compute* on its way, which is exactly the difference between AC⁰ and
  polynomial time.
* A reduction notion that can decide its source problem outright trivializes
  every problem it can decide: `NONEMPTYMARK` is a target only because the
  interpretation may answer the question itself. That is why the classical
  theory measures classes *above* the reductions' own power, and why the
  library's own hardness results stay stated with `≤ᶠᵒ[≤]`, where no such
  collapse happens.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### A first-order target: the marked subset is nonempty -/

/-- **NONEMPTYMARK**: some element of the universe is marked. As simple a
problem as the vocabulary of a marked set supports, and first-order definable
(`DescriptiveComplexity.nonemptyMark_foDefinable`). -/
def NONEMPTYMARK : DecisionProblem Language.markedSet where
  Holds := fun A _ => ∃ x : A, RelMap Language.markedSetMark ![x]
  iso_invariant := fun e =>
    ⟨fun ⟨x, hx⟩ => ⟨e x, (relMap_equiv₁ e _ x).mp hx⟩,
      fun ⟨y, hy⟩ => ⟨e.symm y, (relMap_equiv₁ e _ (e.symm y)).mpr
        (by rwa [e.apply_symm_apply])⟩⟩

/-- The defining sentence of `DescriptiveComplexity.NONEMPTYMARK`. -/
noncomputable def nonemptyMarkS : (Language.markedSet.sum Language.order).Sentence :=
  Formula.iExs (Fin 1)
    (Relations.formula₁ Language.markedSetMarkO (Term.var (Sum.inr 0)) :
      (Language.markedSet.sum Language.order).Formula (Empty ⊕ Fin 1))

/-- **NONEMPTYMARK is first-order definable**: one existential quantifier. -/
theorem nonemptyMark_foDefinable : FODefinable NONEMPTYMARK := by
  refine ⟨nonemptyMarkS, fun A _ _ _ _ => ?_⟩
  rw [Sentence.Realize, nonemptyMarkS, Formula.realize_iExs]
  simp only [Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨v, hv⟩ => ⟨v 0, hv⟩⟩

/-! ### EVEN reduces to it, in FO(LFP) -/

/-- The interpretation of the reduction: the universe unchanged, every element
marked exactly when the induction `d` – which will be one defining EVEN –
answers yes. Its marking formula is the output sentence of `d`, read with a
free variable it does not use. -/
noncomputable def evenMarkInterp (d : StepDef (Language.empty.sum Language.order)) :
    LFPInterpretation (Language.empty.sum Language.order) Language.markedSet Unit 1 where
  ind := d
  toRel :=
    { relFormula := fun {_n} _R _t => d.out.relabel fun z => z.elim
      domFormula := fun _ => ⊤ }

variable {d : StepDef (Language.empty.sum Language.order)}

/-- Every point of the interpreted universe is marked exactly when the
induction answers yes. -/
theorem relMap_evenMarkInterp (A : Type) [Language.empty.Structure A] [LinearOrder A]
    (xs : Fin 1 → (evenMarkInterp d).Map A) :
    RelMap (M := (evenMarkInterp d).Map A) Language.markedSetMark xs ↔ d.IFPHolds A := by
  let := (evenMarkInterp d).expStructure A
  rw [StepDef.IFPHolds]
  refine Iff.trans (Formula.realize_relabel (g := fun z : Empty => z.elim)) ?_
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Every element of the base universe is a point of the interpreted one: the
domain formula is `⊤`. -/
theorem evenMarkInterp_nonempty (A : Type) [Language.empty.Structure A] [LinearOrder A]
    [Nonempty A] : Nonempty ((evenMarkInterp d).Map A) :=
  letI := (evenMarkInterp d).expStructure A
  ⟨⟨((), fun _ => Classical.arbitrary A), Formula.realize_top.mpr trivial⟩⟩

/-- **EVEN FO(LFP)-reduces to NONEMPTYMARK**: the reduction marks everything
when the universe is even and nothing when it is odd, the decision being made
by the induction that puts EVEN in PTIME. -/
theorem even_lfpReduction_nonemptyMark : Nonempty (EVEN ≤ˡᶠᵖ NONEMPTYMARK) := by
  obtain ⟨d, hd⟩ := (ifpDefinable_iff_mem_PTIME EVEN).mpr even_mem_PTIME
  refine ⟨{ Tag := Unit
            dim := 1
            toInterpretation := evenMarkInterp d
            map_nonempty := fun A _ _ _ _ => evenMarkInterp_nonempty A
            correct := fun A _ _ _ _ => ?_ }⟩
  have hne : Nonempty ((evenMarkInterp d).Map A) := evenMarkInterp_nonempty A
  refine (hd A).trans ⟨fun hIFP => ?_, fun ⟨x, hx⟩ => ?_⟩
  · exact ⟨hne.some, (relMap_evenMarkInterp A _).mpr hIFP⟩
  · exact (relMap_evenMarkInterp A _).mp hx

/-! ### The separation -/

/-- **EVEN does not first-order reduce to NONEMPTYMARK**: the target is
first-order definable and EVEN is not, and definability travels backward along
first-order reductions. -/
theorem even_not_orderedReduction_nonemptyMark : IsEmpty (EVEN ≤ᶠᵒ[≤] NONEMPTYMARK) :=
  even_not_le_of_foDefinable nonemptyMark_foDefinable

/-- **FO(LFP) reductions are strictly stronger than first-order ones**, with
EVEN as the witness: it reduces to `DescriptiveComplexity.NONEMPTYMARK` in
FO(LFP) and by no first-order reduction. No complexity-theoretic assumption
enters either half. -/
theorem exists_lfpReduction_not_orderedReduction :
    ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (Q : DecisionProblem L),
      Nonempty (EVEN ≤ˡᶠᵖ Q) ∧ IsEmpty (EVEN ≤ᶠᵒ[≤] Q) :=
  ⟨Language.markedSet, inferInstance, NONEMPTYMARK,
    even_lfpReduction_nonemptyMark, even_not_orderedReduction_nonemptyMark⟩

end DescriptiveComplexity
