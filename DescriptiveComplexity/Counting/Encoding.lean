/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Encoding
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.Counting

/-!
# Faithful encodings, for counting problems

`DescriptiveComplexity.Encoding` bundles a concrete instance type with its
encoding as a structure and the two size bounds that keep the encoding honest.
Its semantic obligation, `DescriptiveComplexity.Encoding.Faithful`, is stated
for decision problems. This file states it for counting problems:
`DescriptiveComplexity.Encoding.CountFaithful` asks the abstract counting
problem to return, on every encoded instance, the number the concrete
definition returns. The encoding itself, with its size bounds and its
computability, is the same object. The converse direction has its counting
form too: `DescriptiveComplexity.CountDecoding`, a computable decoder whose
decoded instances have the count of the structure they come from.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Encoding

variable {L : Language.{0, 0}} {ι : Type*} [L.IsRelational]

/-- Semantic equivalence for a counting problem: the abstract problem `C`
computes the concrete count `conc` on every encoded instance. -/
def CountFaithful (e : Encoding L ι) (conc : ι → ℕ) (C : CountingProblem L) : Prop :=
  ∀ i, conc i = C (e.Univ i)

/-- Counting faithfulness transports along equality of the counts on finite
structures, the universe of an encoded instance being finite. -/
theorem countFaithful_congr {e : Encoding L ι} {conc : ι → ℕ} {C D : CountingProblem L}
    (hCD : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) :
    e.CountFaithful conc C ↔ e.CountFaithful conc D := by
  have hfin : ∀ i, Finite (e.Univ i) := fun i => @Finite.of_fintype _ (e.fintype i)
  exact forall_congr' fun i => by rw [@hCD (e.Univ i) _ (hfin i)]

/-- A faithful encoding for a counting problem is faithful for its support:
the concrete count is positive exactly on the yes-instances. -/
theorem CountFaithful.support {e : Encoding L ι} {conc : ι → ℕ} {C : CountingProblem L}
    (h : e.CountFaithful conc C) : e.Faithful (fun i => 0 < conc i) C.support :=
  fun i => by
    change 0 < conc i ↔ _
    rw [h i, CountingProblem.support_iff]

end Encoding

/-- **A computable decoding, for a counting problem**: the counterpart of
`DescriptiveComplexity.Decoding`. `dec` is a computation from presented
structures to concrete instances, `none` on junk; `sound` says the concrete
count of a decoded instance is the abstract count of the structure it came
from; `total` says well-formed nonempty presentations always decode. -/
structure CountDecoding (L : Language.{0, 0}) [L.IsRelational] {ι : Type*}
    (W : DecisionProblem L) (conc : ι → ℕ) (C : CountingProblem L) where
  /-- The decoder. -/
  dec : FinPresentation L → Option ι
  /-- A decoded instance has the count of the presented structure. -/
  sound : ∀ (S : FinPresentation L) (i : ι), i ∈ dec S → conc i = C (Fin S.card)
  /-- Well-formed nonempty presentations always decode. -/
  total : ∀ S : FinPresentation L, 0 < S.card → W (Fin S.card) → (dec S).isSome

end DescriptiveComplexity
