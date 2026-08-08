/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesAltSpace
import DescriptiveComplexity.Problems.Machine.AltDefs

/-!
# Alternating machine acceptance in bounded space, as a decision problem

EXPTIME's complete problem: an alternating Turing machine is *data in an
instance*, and

> does this machine accept its input, with the tape indexed by the positions and
> no bound whatever on the length of a play?

is `DescriptiveComplexity.ATMAcceptSpace`, an ordinary iso-invariant problem of
the catalog. It stands to `DescriptiveComplexity.ATMAccept` exactly as
`DescriptiveComplexity.DTMAcceptSpace` stands to
`DescriptiveComplexity.DTMAccept`: the step bound is dropped and the space stays
bounded by construction.

Two differences from the polynomial-hierarchy problem, both of them
*relaxations*:

* the vocabulary is `FirstOrder.Language.turingAlt 2` – two marks, one per
  player – and the promise folded into the yes-instances is only that they
  **split** the states (`DescriptiveComplexity.ATMData.BlocksSplit`), not
  `DescriptiveComplexity.ATMData.BlocksWellFormed`, whose ordering clause is
  what bounds the number of alternations. Here the alternation is unbounded,
  which is the whole point;
* acceptance is `DescriptiveComplexity.ATMData.AltAcceptsSpace`, the least fixed
  point of the game operator rather than a budgeted recursion.

Isomorphism-invariance is proved from the *two* agreements an isomorphism
supplies – one per direction – so that only the forward transport lemmas of
`DescriptiveComplexity.MachinesAltSpace` are needed and no finiteness is
assumed.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Problem

variable {A B : Type} [(Language.turingAlt 2).Structure A] [(Language.turingAlt 2).Structure B]

/-- The agreement an isomorphism supplies in the other direction. -/
private theorem altAgree_of_equiv' (e : A ≃[Language.turingAlt 2] B) :
    (atmData 2 A).AltAgree e.toEquiv (atmData 2 B) := by
  have h := altAgree_of_equiv (k := 2) e.symm
  exact h

end Problem

/-- **Alternating acceptance in bounded space**: the machine is well formed,
its two marks split the states, and the existential player wins the game on the
configuration graph from some initial configuration. -/
def ATMAcceptSpace : DecisionProblem (Language.turingAlt 2) where
  Holds := fun A inst => @TMData.WellFormed A (atmData 2 A).toTMData ∧
    @ATMData.BlocksSplit A (atmData 2 A) ∧
    @ATMData.AltAcceptsSpace A (atmData 2 A) true
  iso_invariant := fun {A B} _ _ e => by
    have h := altAgree_of_equiv (k := 2) e
    have h' := altAgree_of_equiv' e
    constructor
    · rintro ⟨hwf, hsp, hacc⟩
      exact ⟨h'.base.wellFormed.mp hwf, h'.blocksSplit_mp hsp, h'.altAcceptsSpace_mp true hacc⟩
    · rintro ⟨hwf, hsp, hacc⟩
      exact ⟨h.base.wellFormed.mp hwf, h.blocksSplit_mp hsp, h.altAcceptsSpace_mp true hacc⟩

@[simp]
theorem atmAcceptSpace_holds_iff (A : Type) [(Language.turingAlt 2).Structure A] :
    ATMAcceptSpace A ↔ (atmData 2 A).toTMData.WellFormed ∧ (atmData 2 A).BlocksSplit ∧
      (atmData 2 A).AltAcceptsSpace true :=
  Iff.rfl

end DescriptiveComplexity
