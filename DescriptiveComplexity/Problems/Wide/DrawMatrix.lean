/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawAlphabet

/-!
# A quantifier-free matrix is a Boolean function of its atoms

The machine evaluates the matrix of its step formula **atom by atom**: a
subroutine per atom, each ending in a state that records whether that atom holds,
the accumulating assignment kept in the *coordinates* of the state – one
coordinate per atom, holding one of the two designated elements of
`DescriptiveComplexity.Problems.Wide.DrawAlphabet`. When every atom has been
evaluated, one transition reads off the answer.

For that to be correct the matrix must be a function of its atoms' truths, and
this file says so:

* `DescriptiveComplexity.Draw.qfValue` – the value of a formula given a truth value
  for each atom;
* `DescriptiveComplexity.Draw.realize_qfValue` – on a quantifier-free formula it is
  the realization;
* `DescriptiveComplexity.Draw.qfAtoms` – the atoms, finitely many;
* `DescriptiveComplexity.Draw.qfValue_congr` – only those matter, so a machine that
  has evaluated them has evaluated the matrix.

The last two are what make the phase count *linear* in the number of atoms rather
than exponential in it: the machine visits `qfAtoms` once and the final transition
is a disjunction over the assignments that satisfy `qfValue`, a finite list a
defining formula can write out.

**The recursion is total, the correctness is not.** `IsQF` is a `Prop`, so a
definition cannot recurse on it; `qfValue` and `qfAtoms` are therefore defined on
*every* bounded formula, sending a quantifier node to `False` and to `[]`, and
correctness is proved by induction on `FirstOrder.Language.BoundedFormula.IsQF`,
where no such node is reachable. This is the shape of
`DescriptiveComplexity.ExpExpansion.translQF` in `Exponential/Matrix.lean`, and it
is the standard way to recurse on a syntactic class carved out by a `Prop`.
Discarding the quantifier node is also why the list stays at one depth: a
quantifier-free formula never changes it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

section Matrix

variable {L : Language.{0, 0}} {α : Type}

/-- **The atoms of a formula**, left to right. Total on every bounded formula: a
quantifier node contributes none, which is what keeps the list at one depth. -/
def qfAtoms : ∀ {n : ℕ}, L.BoundedFormula α n → List (L.BoundedFormula α n)
  | _, .falsum => []
  | _, .equal t₁ t₂ => [.equal t₁ t₂]
  | _, .rel r ts => [.rel r ts]
  | _, .imp φ ψ => qfAtoms φ ++ qfAtoms ψ
  | _, .all _ => []

/-- **The value of a formula given a truth value for each atom**: the Boolean
function a machine computes once its subroutines have evaluated the atoms. Total,
for the reason in the module docstring. -/
def qfValue : ∀ {n : ℕ}, L.BoundedFormula α n → (L.BoundedFormula α n → Prop) → Prop
  | _, .falsum, _ => False
  | _, .equal t₁ t₂, val => val (.equal t₁ t₂)
  | _, .rel r ts, val => val (.rel r ts)
  | _, .imp φ ψ, val => qfValue φ val → qfValue ψ val
  | _, .all _, _ => False

/-- **Only the atoms matter.** Two assignments agreeing on the atoms of a formula
give it the same value – so a machine that has evaluated `qfAtoms` has evaluated
the matrix, and the finitely many assignments to those atoms are what the final
transition is a disjunction over. -/
theorem qfValue_congr : ∀ {n : ℕ} (φ : L.BoundedFormula α n)
    (val val' : L.BoundedFormula α n → Prop),
    (∀ a ∈ qfAtoms φ, (val a ↔ val' a)) → (qfValue φ val ↔ qfValue φ val') := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ _ => Iff.rfl
  | equal t₁ t₂ => exact fun _ _ h => h _ (List.mem_singleton_self _)
  | rel r ts => exact fun _ _ h => h _ (List.mem_singleton_self _)
  | imp φ ψ ihφ ihψ =>
    intro val val' h
    exact imp_congr (ihφ val val' fun a ha => h a (List.mem_append_left _ ha))
      (ihψ val val' fun a ha => h a (List.mem_append_right _ ha))
  | all φ _ => exact fun _ _ _ => Iff.rfl

variable {M : Type} [L.Structure M]

/-- **A quantifier-free formula is the Boolean function of its atoms.** Its
realization is `DescriptiveComplexity.Draw.qfValue` at the assignment that reads
each atom off the structure – which is exactly what the machine's subroutines
compute, one atom at a time. -/
theorem realize_qfValue : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF →
    ∀ (v : α → M) (xs : Fin n → M),
      (φ.Realize v xs ↔ qfValue φ fun a => a.Realize v xs) := by
  intro n φ hqf
  induction hqf with
  | falsum => exact fun _ _ => Iff.rfl
  | of_isAtomic hat =>
    cases hat with
    | equal t₁ t₂ => exact fun _ _ => Iff.rfl
    | rel r ts => exact fun _ _ => Iff.rfl
  | imp _ _ ihφ ihψ => exact fun v xs => imp_congr (ihφ v xs) (ihψ v xs)

end Matrix

end Draw

end DescriptiveComplexity
