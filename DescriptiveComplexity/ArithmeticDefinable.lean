/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Arithmetic
import DescriptiveComplexity.FirstOrderDefinable
import DescriptiveComplexity.Complexity

/-!
# AC⁰ definability: first-order logic with the numeric predicates

**The class AC⁰**, as a logic: a problem is `AC⁰` definable when a single
sentence over the *arithmetic* expansion of its vocabulary decides it on
nonempty finite ordered structures – first-order logic with `≤`, `+` and `×` on
the ranks of the elements (`DescriptiveComplexity.AC0Definable`). Classically
this is `FO(≤, +, ×) = FO(≤, BIT)`, and (DLOGTIME-)uniform AC⁰ ([Immerman
1999][immerman1999descriptive], Thm 1.17; Barrington–Immerman–Straubing 1990);
here, as everywhere in this library, the logic is the *definition*, and the
identification with a circuit model is a bridge that is not built – see below.

## Why `+` and `×` rather than `BIT`

Expressively it makes no difference (the two are classically interdefinable), so
the choice is made by a proof obligation elsewhere: the closure of the class
under first-order reductions must define the numeric predicates of the
*interpreted* universe – lexicographically ordered tagged tuples, hence base-`n`
digits – from those of the base. For `+` and `×` that is schoolbook arithmetic
on a constant number of digits; for `BIT` it is base-`n`-to-base-2 conversion,
whose only route is to define `+` and `×` on the tuples first. So `BIT` is a
later addition, not the primitive.

## Order-invariance, and the absence of an order-free variant

The definition quantifies over structures carrying a `LinearOrder`, and requires
the equivalence for *every* linear order: the sentence sees `≤, +, ×`, the
problem does not. This is verbatim the convention of
`DescriptiveComplexity.FODefinable`, and it is not a convenience here but a
necessity: the numeric predicates are *functions of the order*
(`DescriptiveComplexity.Arithmetic`), so there is no order-free reading of this
logic to state, and no `AC0DefinableFree` in this file. Together with
`DescriptiveComplexity.LOGSPACE`, whose logic is an operator rather than a
fragment, this is the second place where the bottom of the ladder breaks the
pattern of the classes above it.

## What is proved here, and what is not

* `FO(≤) ⊆ AC⁰` (`DescriptiveComplexity.FODefinable.ac0Definable`), by transport
  along `DescriptiveComplexity.sumOrderToArith`; the inclusion is **strict**
  (`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`, in
  `DescriptiveComplexity.Problems.Even`), so the numeric predicates genuinely add
  power, unconditionally and with no complexity assumption.
* Closure under complement (`DescriptiveComplexity.AC0Definable.compl`) – free,
  since the defining object is a sentence, where every class above needed an
  argument (Immerman–Szelepcsényi for NL, a determinized walk for LOGSPACE).
* **Not** here: that AC⁰ definability is closed under first-order reductions
  (the arithmetic of an interpreted universe, as above), and therefore no
  `DescriptiveComplexity.ComplexityClass` yet; and no circuit model, so no
  capture theorem. The inclusion in `DescriptiveComplexity.LOGSPACE` is proved
  separately, through the multi-head automaton, and gives every consumer that
  the missing closure lemma would.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The definition -/

/-- A decision problem is **AC⁰ definable** if a single sentence over the
arithmetic expansion of its vocabulary decides it on nonempty finite ordered
structures. The equivalence is required for *every* linear order, so the notion
is order-invariant: the sentence sees `≤`, `+` and `×`, the problem does not.

There is deliberately no order-free variant: the numeric predicates are computed
from the order (`DescriptiveComplexity.arithStructure`), so without one there is
nothing for them to mean. -/
def AC0Definable (P : DecisionProblem L) : Prop :=
  ∃ φ : (L.sum Language.arith).Sentence,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

/-- AC⁰ definability only depends on the finite instances of a problem – the
hypothesis a `DescriptiveComplexity.ComplexityClass` demands of its membership
predicate. -/
theorem ac0Definable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    AC0Definable P ↔ AC0Definable Q := by
  constructor <;> rintro ⟨φ, hφ⟩ <;> refine ⟨φ, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-! ### First-order definability, read arithmetically -/

/-- **`FO(≤) ⊆ AC⁰`**: an order-invariant first-order definition is an
arithmetic one, by transport along `DescriptiveComplexity.sumOrderToArith` – the
numeric predicates are simply not used. The inclusion is strict
(`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`). -/
theorem FODefinable.ac0Definable {P : DecisionProblem L} (h : FODefinable P) :
    AC0Definable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(sumOrderToArith L).onSentence φ, ?_⟩
  intro A _ _ _ _
  rw [hφ A]
  exact (LHom.realize_onSentence A (sumOrderToArith L) φ).symm

/-- An order-free first-order definition is in particular an arithmetic one. -/
theorem FODefinableFree.ac0Definable {P : DecisionProblem L} (h : FODefinableFree P) :
    AC0Definable P :=
  h.foDefinable.ac0Definable

/-! ### Boolean closure -/

/-- **AC⁰ is closed under complement**: negate the sentence. Nothing like
Immerman–Szelepcsényi is needed at this level – the defining object is a
sentence, not a walk. -/
theorem AC0Definable.compl {P : DecisionProblem L} (h : AC0Definable P) :
    AC0Definable Pᶜ := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨∼φ, ?_⟩
  intro A _ _ _ _
  exact not_congr (hφ A)

end DescriptiveComplexity
