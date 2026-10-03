/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.SecondOrderPull
import Lax624099Proofs.DescriptiveComplexity.SecondOrderLift
import Lax624099Proofs.DescriptiveComplexity.OrderedComposition
import Mathlib.Tactic.FinCases
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

namespace Lax624099Proofs.DescriptiveComplexity.PiSODefinable
end Lax624099Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax624099Proofs.DescriptiveComplexity.SOBlock
end Lax624099Proofs.DescriptiveComplexity.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable

/-!
# Closure of second-order definability under ordered FO reductions

If `P ≤ᶠᵒ[≤] Q` and `Q` is `Σₖ₊₁`- (resp. `Πₖ₊₁`-) definable, then so is `P`
(`Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable.of_orderedReduction`,
`Lax624099Proofs.DescriptiveComplexity.PiSODefinable.of_orderedReduction`).

Pulling the defining sentence back through the interpretation
(`Lax624099Proofs.DescriptiveComplexity.SecondOrderPull`) yields a sentence over the *ordered*
expansion `L.sum Language.order` – correct for every linear order on the
input, by order-invariance of the reduction. The order is then eliminated by
re-quantifying it inside the first second-order block:

* the first block is extended with one binary relation variable, the order
  (`Lax624099Proofs.DescriptiveComplexity.SOBlock.withOrder`);
* the sentence is transported along the language morphism
  `Lax624099Proofs.DescriptiveComplexity.orderElimLHom` mapping the order symbol to the new variable;
* it is guarded by the first-order sentence `Lax624099Proofs.DescriptiveComplexity.linearGuard` stating
  that the variable is a linear order – as a conjunct if the block is
  existential (`Σₖ₊₁`), as a premise if it is universal (`Πₖ₊₁`).

Correctness of the guard uses `Lax624099Proofs.DescriptiveComplexity.linearOrderOfGuard` to promote a
guarded relation variable to an actual `LinearOrder` instance, and the
order-invariance clause of `OrderedFOReduction.correct` to connect different
choices of the order. This requires at least one second-order block to
piggyback on, whence the level `k + 1`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Adding an order variable to a block -/

/-- The block `B` extended with one extra binary relation variable, used to
re-quantify the order of an ordered reduction. -/
def SOBlock.withOrder (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Unit ⊕ B.ι
  arity := Sum.elim (fun _ => 2) B.arity

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (withOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order variable of the extended block. -/
def SOBlock.orderSym (B : Lax904597.SecondOrder.SOBlock) : B.withOrder.lang.Relations 2 :=
  ⟨Sum.inl (), rfl⟩

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (orderSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order variable, as a relation symbol of the expanded language. -/
abbrev ordVarSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) :
    (L.sum B.withOrder.lang).Relations 2 :=
  Sum.inr B.orderSym

variable {A : Type}

/-- The assignment of the original block variables underlying an assignment
of the extended block. -/
def SOBlock.restPart (B : Lax904597.SecondOrder.SOBlock) (ρ : B.withOrder.Assignment A) : B.Assignment A :=
  fun i => ρ (Sum.inr i)

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (restPart)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-- The assignment of the extended block determined by a binary relation (for
the order variable) and an assignment of the original block. -/
def SOBlock.joinOrder (B : Lax904597.SecondOrder.SOBlock) (R : (Fin 2 → A) → Prop) (ρ : B.Assignment A) :
    B.withOrder.Assignment A :=
  fun p => match p with
    | Sum.inl _ => R
    | Sum.inr i => ρ i

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (joinOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-! ### The linear-order guard -/

section Guard

variable (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock)

end Guard

/-! ### Promoting a guarded order variable to a linear order -/

/-- A binary relation variable satisfying the guard axioms determines a
linear order (decidability by choice). -/
@[instance_reducible]
noncomputable def linearOrderOfGuard (r : (Fin 2 → A) → Prop)
    (hrefl : ∀ a : A, r ![a, a])
    (htrans : ∀ a b c : A, r ![a, b] → r ![b, c] → r ![a, c])
    (hantisymm : ∀ a b : A, r ![a, b] → r ![b, a] → a = b)
    (htotal : ∀ a b : A, r ![a, b] ∨ r ![b, a]) : LinearOrder A where
  le a b := r ![a, b]
  le_refl := hrefl
  le_trans := htrans
  le_antisymm := hantisymm
  le_total := htotal
  toDecidableLE := fun _ _ => Classical.propDecidable _

/-! ### Eliminating the order symbol -/

/-! ### Order elimination, as a statement about sentences

The two theorems below are the order-elimination construction on its own,
separated from the reduction that usually produces the sentence: a problem
defined – over the *ordered* expansion, so with the order visible to the
sentence – by a `Σₖ₊₁` sentence *for some* linear order, or by a `Πₖ₊₁`
sentence *for every* linear order, is definable at that level over the bare
vocabulary. The closure theorems of the next section are the case where the
sentence comes from pulling a definition back through an ordered reduction,
where order-invariance makes “for some” and “for every” agree.

Stated this way the construction also applies where no single order-invariant
problem is in sight – to each half of a `Lax624099Proofs.DescriptiveComplexity.DPDefinable`
definition separately, say, whose two halves are *not* individually
order-invariant. -/

section OrderPull

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {k : ℕ}

end OrderPull

/-! ### Closure of the definability levels under ordered FO reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {k : ℕ}

end Closure

end Lax624099Proofs.DescriptiveComplexity


