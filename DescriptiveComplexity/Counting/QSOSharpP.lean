/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.QSOQuantifiers
import DescriptiveComplexity.Counting.Class

/-!
# ΣQSO(FO) is the logic of `#P`

`#P` is defined in the library by witness counts
(`DescriptiveComplexity.SharpPDefinable`): the number of assignments of a
block of relation variables satisfying a first-order sentence over the
ordered expansion. [Arenas, Muñoz, Riveros 2020][arenas2020descriptive] read
`#P` as the logic ΣQSO(FO) instead, whose terms add and multiply, sum and
take products over elements, and sum over relations
(`DescriptiveComplexity.SQTerm`). The two readings coincide
(`DescriptiveComplexity.mem_sharpP_iff_sqDefinable`):

* a witness count is the term `ΣX̄. [φ]`;
* every term is a witness count with free variables
  (`DescriptiveComplexity.SQTerm.wcount`), by induction on the term, each
  construction of the logic being a closure property of witness counts
  (`DescriptiveComplexity.Counting.QSOWitness`,
  `DescriptiveComplexity.Counting.QSOQuantifiers`).

So a problem stated as a ΣQSO(FO) term – the permanent as
`ΣS. [S is a permutation] · Πx. (∃y. S(x, y) ∧ M(x, y))`, a probability of a
query as a weighted count – is in `#P` without writing its kernel.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- **Every ΣQSO(FO) term is a witness count**, with its free variables. -/
theorem SQTerm.wcount : ∀ {M : Language.{0, 0}} {α : Type} (t : SQTerm M α),
    WCount M α fun A _ v => t.eval A v
  | _, _, .ind φ => WCount.ind φ
  | _, _, .const s => WCount.const s
  | _, _, .add s t => WCount.add s.wcount t.wcount
  | _, _, .mul s t => WCount.mul s.wcount t.wcount
  | _, _, .sum n t => WCount.sum n t.wcount
  | _, _, .prod n t => WCount.prod n t.wcount
  | _, _, .sosum B t => WCount.sosum B t.wcount

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **A counting problem is ΣQSO(FO)-definable** when, on nonempty finite
ordered structures, it is the value of a closed term of ΣQSO(FO) over the
ordered expansion, whatever the linear order. -/
def SQDefinable (C : CountingProblem L) : Prop :=
  ∃ t : SQTerm (L.sum Language.order) Empty,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], C A = t.value A

/-- **ΣQSO(FO) captures `#P`**: a counting problem is in `#P` iff it is
ΣQSO(FO)-definable. -/
theorem mem_sharpP_iff_sqDefinable (C : CountingProblem L) : C ∈ SharpP ↔ SQDefinable C := by
  constructor
  · rintro ⟨B, φ, h⟩
    refine ⟨.sosum B (.ind φ), fun A _ _ _ _ => (h A).trans ?_⟩
    classical
    have := Fintype.ofFinite (B.Assignment A)
    rw [SQTerm.value, SQTerm.eval, finsum_eq_sum_of_fintype, witnessCount]
    simp only [SQTerm.eval]
    rw [Finset.sum_boole, Nat.cast_id, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  · rintro ⟨t, h⟩
    obtain ⟨B, φ, hφ⟩ := t.wcount
    exact ⟨B, φ, fun A _ _ _ _ => (h A).trans (hφ A default)⟩

end DescriptiveComplexity
