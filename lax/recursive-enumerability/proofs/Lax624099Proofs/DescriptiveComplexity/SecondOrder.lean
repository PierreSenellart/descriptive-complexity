/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Lax624099Proofs.DescriptiveComplexity.Complexity
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

namespace Lax624099Proofs.DescriptiveComplexity.SOBlock
end Lax624099Proofs.DescriptiveComplexity.SOBlock

/-!
# Second-order definability with bounded alternation

Foundation for *defining* the levels `Σₖ`/`Πₖ` (`k ≥ 1`) of the polynomial
hierarchy logically, by Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: `Σₖᵖ`
consists of
the problems definable by a second-order sentence with `k` alternating blocks
of second-order quantifiers starting existentially – on unordered finite
structures (the first existential block can guess a linear order, so the
order-free definition is equivalent to the classical ordered one).

No object-level second-order syntax is needed: a second-order quantifier
block (`Lax624099Proofs.DescriptiveComplexity.SOBlock`) is a finite family of relation variables with
given arities, its instantiations are Lean-level (`SOBlock.structure` turns
an assignment of relations into a structure over the block's vocabulary
`SOBlock.lang`), and only the first-order kernel is object-level – a sentence
over the base language expanded by all blocks (`Lax624099Proofs.DescriptiveComplexity.soLang`).
`Lax624099Proofs.DescriptiveComplexity.SORealize` evaluates the alternating quantification, and
`Lax624099Proofs.DescriptiveComplexity.SigmaSODefinable` / `Lax624099Proofs.DescriptiveComplexity.PiSODefinable` state that a
decision problem is defined by such a sentence *on nonempty finite
structures*.

This file proves the two structural facts about these notions that do not
involve reductions:

* isomorphism-invariance (`Lax624099Proofs.DescriptiveComplexity.sorealize_iso`) – so second-order
  definable properties are bona fide decision problems;
* the duality `Πₖ = co-Σₖ` (`Lax624099Proofs.DescriptiveComplexity.piSODefinable_iff_compl`), by
  negating the kernel and flipping the quantifiers.

The rest of the definitional theory lives in dedicated files: functoriality
and padding in `Lax624099Proofs.DescriptiveComplexity.SecondOrderLift`, closure under FO reductions in
`Lax624099Proofs.DescriptiveComplexity.SecondOrderPull`, closure under ordered FO reductions in
`Lax624099Proofs.DescriptiveComplexity.SecondOrderOrdered`, and the resulting definition of the levels
`Σₖᵖ`/`Πₖᵖ` for `k ≥ 1` in `Lax624099Proofs.DescriptiveComplexity.Hierarchy`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Second-order quantifier blocks -/

attribute [instance] Lax904597.SecondOrder.SOBlock.ιFinite

variable {L : Language.{0, 0}}

/-! ### Isomorphism-invariance -/

section Iso

/-- Transport of a block assignment along an equivalence. -/
def SOBlock.mapAssign (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A') (ρ : B.Assignment A) :
    B.Assignment A' :=
  fun i x => ρ i fun j => e.symm (x j)

end Iso

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (mapAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Iso

/-- An `L`-isomorphism extends to the vocabulary expanded by a block, when
the block is interpreted by an assignment on one side and its transport on
the other. -/
def SOBlock.extendEquiv (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (ρ : B.Assignment A) :
    @Language.Equiv (L.sum B.lang) A A'
      (@sumStructure L B.lang A _ (B.structure ρ))
      (@sumStructure L B.lang A' _ (B.structure (B.mapAssign e.toEquiv ρ))) :=
  letI := B.structure ρ
  letI := B.structure (B.mapAssign e.toEquiv ρ)
  { toEquiv := e.toEquiv
    map_fun' := fun {n} f => by
      cases f with
      | inl f => exact HomClass.map_fun e.toHom f
      | inr f => exact isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r => exact StrongHomClass.map_rel e r x
      | inr r =>
        change B.mapAssign e.toEquiv ρ r.1 _ ↔ ρ r.1 _
        rw [SOBlock.mapAssign]
        refine iff_of_eq (congrArg _ (funext fun j => ?_))
        exact e.toEquiv.symm_apply_apply _ }

end Iso

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax624099Proofs.DescriptiveComplexity.SOBlock (extendEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Iso

private theorem sorealize_iso_aux :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A A' : Type) (instA : L.Structure A)
      (instA' : L.Structure A'), @Language.Equiv L A A' instA instA' →
      ∀ (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A instA Bs φ pol → @Lax904597.SecondOrder.SORealize L A' instA' Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A A' instA instA' e φ pol h
    exact (StrongHomClass.realize_sentence (L := L) e φ).mp h
  | cons B Bs ih =>
    intro L A A' instA instA' e φ pol h
    cases pol with
    | true =>
      obtain ⟨ρ, hρ⟩ := h
      exact ⟨B.mapAssign e.toEquiv ρ, ih _ _ _ _ _ (B.extendEquiv e ρ) φ false hρ⟩
    | false =>
      intro ρ'
      have key : B.mapAssign e.toEquiv (B.mapAssign e.toEquiv.symm ρ') = ρ' := by
        funext i x
        rw [SOBlock.mapAssign, SOBlock.mapAssign]
        exact congrArg _ (funext fun j => e.toEquiv.apply_symm_apply _)
      have h' := ih _ _ _ _ _ (B.extendEquiv e (B.mapAssign e.toEquiv.symm ρ')) φ true
        (h (B.mapAssign e.toEquiv.symm ρ'))
      rwa [key] at h'

/-- Alternating second-order satisfaction is isomorphism-invariant: what a
second-order sentence expresses is a decision problem. -/
theorem sorealize_iso {A A' : Type} [L.Structure A] [L.Structure A'] (e : A ≃[L] A')
    (Bs : List Lax904597.SecondOrder.SOBlock) (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool) :
    Lax904597.SecondOrder.SORealize L A Bs φ pol ↔ Lax904597.SecondOrder.SORealize L A' Bs φ pol :=
  ⟨sorealize_iso_aux Bs L A A' _ _ e φ pol,
    sorealize_iso_aux Bs L A' A _ _ e.symm φ pol⟩

end Iso

/-! ### Duality: `Πₖ` is co-`Σₖ` -/

section Duality

end Duality

/-! ### Atoms in the relation variables of a block

The clausal fragments of existential second-order logic – SO-Horn
(`Lax624099Proofs.DescriptiveComplexity.SecondOrderHorn`) and SO-Krom
(`Lax624099Proofs.DescriptiveComplexity.SecondOrderKrom`) – represent their first-order kernel as
data: a list of clauses built from *atoms* in the quantified relation
variables, over a shared list of universally quantified first-order variables.
The atom type and its semantics are common to both fragments, so they live
here. -/

section Atoms

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

end Atoms

end Lax624099Proofs.DescriptiveComplexity


