/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FirstOrderDefinable
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.OrderedComposition

/-!
# First-order definability travels backward along reductions

The bottom of the ladder is closed under reductions, exactly as every class
above it is: pull the defining sentence of the target back through the
interpretation (`DescriptiveComplexity.FOInterpretation.pullSentence`) and it
defines the source. For the order-invariant notion the interpretation is first
extended with the lexicographic order of its tagged tuples
(`DescriptiveComplexity.FOInterpretation.ordExtend`), so that the pulled
sentence may mention the order the target's sentence mentions.

The point of these lemmas is their **contrapositive**
(`DescriptiveComplexity.not_le_of_not_foDefinable` and its order-free twin): a
problem that is not first-order definable reduces to no problem that is. This
is what turns an inexpressibility result into a *non-reducibility* result, and
so the only route this library has to a negative statement about the reduction
order – everything else it proves is the existence of a reduction. It is
applied to `DescriptiveComplexity.EVEN`
(`DescriptiveComplexity.even_not_foDefinable`), whence
`DescriptiveComplexity.even_not_le_of_foDefinable`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
variable {P : DecisionProblem L} {Q : DecisionProblem L'}

/-! ### Closure under reductions -/

/-- **Order-free first-order definability travels backward along FO
reductions**: the defining sentence of the target, pulled back through the
interpretation, defines the source. -/
theorem FODefinableFree.of_foReduction (h : FODefinableFree Q) (f : P ≤ᶠᵒ Q) :
    FODefinableFree P := by
  letI := f.tagFinite
  letI := f.tagNonempty
  obtain ⟨φ, hφ⟩ := h
  refine ⟨f.toInterpretation.pullSentence φ, fun A _ _ _ => ?_⟩
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  rw [f.toInterpretation.realize_pullSentence φ A]
  exact (f.correct A).trans (hφ _)

/-- **Order-invariant first-order definability travels backward along ordered
FO reductions**. The interpretation is extended with the lexicographic order on
its tagged tuples, so the pulled sentence can still read an order; the
extension is definable from the order of the input, which is what keeps the
result inside FO(≤). -/
theorem FODefinable.of_orderedReduction (h : FODefinable Q) (f : P ≤ᶠᵒ[≤] Q) :
    FODefinable P := by
  letI := f.tagFinite
  letI := f.tagNonempty
  letI : LinearOrder f.Tag := finiteLinearOrder f.Tag
  obtain ⟨φ, hφ⟩ := h
  refine ⟨f.toInterpretation.ordExtend.pullSentence φ, fun A _ _ _ _ => ?_⟩
  letI := f.toInterpretation.mapLinearOrder A
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  rw [f.toInterpretation.ordExtend.realize_pullSentence φ A,
    StrongHomClass.realize_sentence (f.toInterpretation.ordExtendLEquiv A) φ]
  exact (f.correct A).trans (hφ _)

/-- Order-invariant definability travels backward along plain FO reductions
too, a plain reduction being an ordered one. -/
theorem FODefinable.of_foReduction (h : FODefinable Q) (f : P ≤ᶠᵒ Q) : FODefinable P :=
  h.of_orderedReduction f.toOrdered

/-! ### Non-reducibility -/

/-- **A problem that is not FO(≤)-definable reduces to no problem that is.**
The contrapositive of `DescriptiveComplexity.FODefinable.of_orderedReduction`,
and the shape in which an inexpressibility result becomes a statement about the
reduction order. -/
theorem not_le_of_not_foDefinable (hP : ¬FODefinable P) (hQ : FODefinable Q) :
    IsEmpty (P ≤ᶠᵒ[≤] Q) :=
  ⟨fun f => hP (hQ.of_orderedReduction f)⟩

/-- The order-free twin. -/
theorem not_le_of_not_foDefinableFree (hP : ¬FODefinableFree P) (hQ : FODefinableFree Q) :
    IsEmpty (P ≤ᶠᵒ Q) :=
  ⟨fun f => hP (hQ.of_foReduction f)⟩

end DescriptiveComplexity
