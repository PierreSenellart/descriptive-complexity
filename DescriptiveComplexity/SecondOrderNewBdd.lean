/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.Finite
import DescriptiveComplexity.SecondOrderNew

/-!
# Value invention, bounded

`DescriptiveComplexity.SigmaSONewDefinable` guesses a finite extension
`A ⊕ Fin m` of the instance with `m` **unbounded**, and that single freedom is
what takes existential second-order logic from NP up to RE: the yes-instances
become those found by an unbounded search over finite witnesses.

This file puts the bound back, as a parameter. `∃SO[new, d]` guesses an
extension with at most `Nat.card (Fin d → A)` invented values – as many as there
are `d`-tuples of the instance – and the point of the notion is that the bound
does exactly what it should: it hands the search space back to the instance, so
the class is NP again. Read beside `PSPACE = NL.exp`, the family reads *invent
nothing* (`Σ₁`), *invent polynomially many* (here), *invent exponentially many*
(NEXPTIME) and *invent unboundedly many* (RE): one definition with one parameter.

## What is here

* `DescriptiveComplexity.SigmaSONewBddDefinable`: the polynomial bound;
* `DescriptiveComplexity.SigmaSONewExpDefinable`: the exponential one, whose
  invented values are as many as the instance has tuples of `c` relations of
  arity `d`;
* `DescriptiveComplexity.SigmaSODefinable.toNewBdd`: `Σ₁ ⊆ ∃SO[new, d]`, by
  inventing nothing, which is the easy half of `∃SO[new, d] = NP`.

The converse half – that a bounded extension is definable inside the instance's
own `d`-tuples, so the guess can be moved back onto `A` – is the substance, and
lives in `DescriptiveComplexity.SecondOrderNewBddPull`, where the
`d`-dimensional interpreted universe enters; together the two give
`DescriptiveComplexity.sigmaSONewBddDefinable_iff_sigmaSODefinable`.

Note that neither the bound nor its absence is a *weakening* of the other: a
definability statement is an equivalence, so relaxing the bound loses the
backward direction and tightening it loses the forward one. Passing between the
notions means re-guarding the sentence, not reusing it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **Definability in `∃SO[new, d]`**: one existential second-order block over a
universe extended by at most `Nat.card (Fin d → A)` invented values, and a
first-order kernel. The bound is the only difference from
`DescriptiveComplexity.SigmaSONewDefinable`. -/
def SigmaSONewBddDefinable [L.IsRelational] (d : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ B : SOBlock, ∃ φ : (soLang (newLang L) [B]).Sentence,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ m ≤ Nat.card (Fin d → A), SORealize (newLang L) (A ⊕ Fin m) [B] φ true

/-- **`∃SO[new, d]`-definability only depends on the finite instances** of a
problem, as `∃SO[new]`-definability does. -/
theorem sigmaSONewBddDefinable_congr [L.IsRelational] {d : ℕ} {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SigmaSONewBddDefinable d P ↔ SigmaSONewBddDefinable d Q := by
  constructor <;> rintro ⟨B, φ, hφ⟩ <;> refine ⟨B, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- **`Σ₁ ⊆ ∃SO[new, d]`**: an `∃SO` sentence becomes an `∃SO[new, d]` sentence
when guarded by “nothing was invented”, the bound being satisfied by inventing
nothing at all. -/
theorem SigmaSODefinable.toNewBdd [L.IsRelational] {d : ℕ} {P : DecisionProblem L}
    (h : SigmaSODefinable 1 P) : SigmaSONewBddDefinable d P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  obtain ⟨B, rfl⟩ : ∃ B, Bs = [B] := by
    match Bs, hk with
    | [B], _ => exact ⟨B, rfl⟩
  refine ⟨B, (soLangEmbed [B] (newLang L)).onSentence (noNewSentence L) ⊓
    (soLangLift [B] L (newLang L) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  constructor
  · intro hP
    exact ⟨0, Nat.zero_le _, (sorealize_guardNoNew_iff φ A 0).mpr ⟨inferInstance, (hφ A).mp hP⟩⟩
  · rintro ⟨m, -, hm⟩
    exact (hφ A).mpr ((sorealize_guardNoNew_iff φ A m).mp hm).2

/-! ### Inventing exponentially many values -/

/-- **Definability in `∃SO[new, exp c d]`**: the same logic with the number of
invented values held to `2 ^ (c · nᵈ)` – as many as the instance has tuples of
`c` relations of arity `d`, which is the size of an exponential expansion of it.
This is the middle rung of the family: *invent nothing* is `Σ₁`, *invent
polynomially many* is `DescriptiveComplexity.SigmaSONewBddDefinable`, *invent
unboundedly many* is `DescriptiveComplexity.SigmaSONewDefinable`.

Two constants and not one: at a one-element instance `nᵈ` is `1` whatever `d`
is, so a bound of `2 ^ nᵈ` would be the constant `2` there, while an expansion's
points at such an instance are `|Tag| · 2 ^ |B.ι|` – a constant the expansion
chooses. The factor `c` is what lets an arbitrary expansion fit. -/
def SigmaSONewExpDefinable [L.IsRelational] (c d : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ B : SOBlock, ∃ φ : (soLang (newLang L) [B]).Sentence,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ m ≤ 2 ^ (c * Nat.card (Fin d → A)),
        SORealize (newLang L) (A ⊕ Fin m) [B] φ true

/-- **`∃SO[new, exp d]`-definability only depends on the finite instances** of a
problem. -/
theorem sigmaSONewExpDefinable_congr [L.IsRelational] {c d : ℕ} {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SigmaSONewExpDefinable c d P ↔ SigmaSONewExpDefinable c d Q := by
  constructor <;> rintro ⟨B, φ, hφ⟩ <;> refine ⟨B, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

end DescriptiveComplexity
