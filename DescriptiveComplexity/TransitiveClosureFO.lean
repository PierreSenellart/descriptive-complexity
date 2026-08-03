/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FirstOrderDefinable
import DescriptiveComplexity.TransitiveClosure

/-!
# First-order logic sits inside FO(TC)

The trivial half of `FO ⊆ FO(TC)`, needed to state the strict inclusion that
`DescriptiveComplexity.Problems.Even` proves: a sentence is the walk that
takes no step at all – arity `0`, one mode, no transition, the sentence as the
condition on starting nodes and nothing to check at the end. Reachability is
then reflexivity, and acceptance is the sentence.

The converse fails, unconditionally: `EVEN` is a walk and is not a sentence
(`DescriptiveComplexity.exists_tcDefinable_not_foDefinable`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The walk that takes no step: the sentence decides the starting node, and
the node it starts at is already accepting. -/
noncomputable def sentenceSpec (φ : (L.sum Language.order).Sentence) : TCSpec L where
  Mode := Unit
  k := 0
  step _ _ := ⊥
  src _ := φ.relabel Empty.elim
  tgt _ := ⊤

omit [L.IsRelational] in
theorem accepts_sentenceSpec_iff (φ : (L.sum Language.order).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] [Nonempty A] :
    (sentenceSpec φ).Accepts A ↔ A ⊨ φ := by
  have hsrc : ∀ u : (sentenceSpec φ).Node A, (sentenceSpec φ).IsSrc u ↔ A ⊨ φ := by
    intro u
    change (Formula.relabel Empty.elim φ).Realize u.2 ↔ _
    rw [Formula.realize_relabel]
    have hv : (u.2 ∘ Empty.elim) = (default : Empty → A) := funext fun e => e.elim
    rw [hv]
    exact Iff.rfl
  constructor
  · rintro ⟨u, -, hu, -, -⟩
    exact (hsrc u).mp hu
  · intro h
    refine ⟨((), fun _ => Classical.arbitrary A), ((), fun _ => Classical.arbitrary A),
      (hsrc _).mpr h, ?_, Relation.ReflTransGen.refl⟩
    exact Formula.realize_top.mpr trivial

/-- **A first-order definable problem is FO(TC) definable**: the walk that
takes no step. -/
theorem FODefinable.tcDefinable {P : DecisionProblem L} (h : FODefinable P) :
    TCDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨sentenceSpec φ, fun A _ _ _ _ => (hφ A).trans (accepts_sentenceSpec_iff φ A).symm⟩

end DescriptiveComplexity
