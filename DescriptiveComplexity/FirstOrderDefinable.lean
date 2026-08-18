/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered

/-!
# Plain first-order definability of a decision problem

The bottom of every ladder in this library: a problem is first-order definable
when a single sentence decides it on finite structures. The two variants are
the usual ones, and are named as everywhere else here –
`DescriptiveComplexity.FODefinableFree` is the order-free notion,
`DescriptiveComplexity.FODefinable` the order-invariant one, whose sentence
may mention a linear order on the universe but whose truth value may not
depend on which one.

Nothing is *proved* first-order definable by these notions – they exist to be
*refuted*. Every logic of this library extends first-order logic, so a problem
shown here to escape it (`DescriptiveComplexity.EVEN`, in
`DescriptiveComplexity.Problems.Even`) separates first-order logic from all of
them unconditionally, with no complexity-theoretic assumption. The refutations
themselves are Ehrenfeucht–Fraïssé arguments
(`DescriptiveComplexity.Games.Ehrenfeucht`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A decision problem is *order-free first-order definable* if a single
sentence over its own vocabulary decides it on nonempty finite structures. -/
def FODefinableFree (P : DecisionProblem L) : Prop :=
  ∃ φ : L.Sentence, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

/-- A decision problem is *FO(≤) definable* if a single sentence over the
ordered expansion of its vocabulary decides it on nonempty finite ordered
structures. As everywhere in this library, the equivalence is required for
*every* linear order, so the notion is order-invariant: the sentence sees the
order, the problem does not. -/
def FODefinable (P : DecisionProblem L) : Prop :=
  ∃ φ : (L.sum Language.order).Sentence,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

/-- Order-free first-order definability only depends on the finite instances
of a problem. -/
theorem foDefinableFree_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    FODefinableFree P ↔ FODefinableFree Q := by
  constructor <;> rintro ⟨φ, hφ⟩ <;> refine ⟨φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- FO(≤) definability only depends on the finite instances of a problem. -/
theorem foDefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    FODefinable P ↔ FODefinable Q := by
  constructor <;> rintro ⟨φ, hφ⟩ <;> refine ⟨φ, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- An order-free first-order definition is in particular an order-invariant
one: the order symbol is simply not used. -/
theorem FODefinableFree.foDefinable {P : DecisionProblem L} (h : FODefinableFree P) :
    FODefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(LHom.sumInl : L →ᴸ L.sum Language.order).onSentence φ, ?_⟩
  intro A _ _ _ _
  let := orderStructure (M := A)
  rw [hφ A]
  exact (LHom.realize_onSentence A LHom.sumInl φ).symm

end DescriptiveComplexity
