/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Interpretation
import Mathlib.ModelTheory.Order
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Ordered first-order reductions

Textbook FO reductions ([Immerman 1999][immerman1999descriptive],
*Descriptive Complexity*, ch. 3) operate on *ordered* finite structures: the
input structure comes with a linear order on
its universe, which the defining formulas may mention. The order is essential
for many reductions: e.g., reducing SAT to 3-colorability threads an OR-gadget
chain along the order of each clause's literals, which no order-free
first-order interpretation can express.

This file provides the ordered variant of `Lax624099Proofs.DescriptiveComplexity.FOReduction`:

* an `(L.sum Language.order).Structure` instance on any linearly ordered
  `L`-structure, realizing the extra binary symbol `leSymb` as `≤`;
* `Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction P Q`: a first-order interpretation of `L'` in
  the ordered expansion `L.sum Language.order`, mapping yes-instances of `P`
  exactly to yes-instances of `Q` – for every *finite* linearly ordered input
  structure. Finiteness matters: gadget constructions traverse the order and
  need minima, maxima and successors.

Since the problem `P` does not mention the order and correctness is required
for *every* linear order on the input structure, an `OrderedFOReduction` is
what descriptive complexity calls an order-invariant FO reduction.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

section OrderedStructures

variable (A : Type) [L.Structure A] [LE A]

variable {L A}

@[simp]
theorem relMap_sumInl {n : ℕ} (r : L.Relations n) (x : Fin n → A) :
    RelMap (L := L.sum Language.order) (Sum.inl r) x ↔ RelMap r x :=
  Iff.rfl

end OrderedStructures

variable {L} {L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ[≤] " Q:51 => Lax904597.Interpretations.OrderedFOReduction P Q

end Lax624099Proofs.DescriptiveComplexity


