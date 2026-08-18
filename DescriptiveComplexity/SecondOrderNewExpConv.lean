/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewExpBuild
import DescriptiveComplexity.SecondOrderNewBdd
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.Exponential.Classes

/-!
# From a problem over an expansion to one with value invention

The two halves built in `DescriptiveComplexity.SecondOrderNewExpPull` and
`DescriptiveComplexity.SecondOrderNewExpBuild` meet here: a problem that a `Σ₁`
sentence decides over an exponential expansion is decided by a `Σ₁` sentence
with **exponentially bounded value invention**
(`DescriptiveComplexity.ExpDefinable.toSigmaSONewExp`).

The two constants of the bound are read off the expansion: one invented value
per assignment of its block *with one nullary variable added per tag*, so their
number is `2 ^ (c · nᵈ)` with `c` the number of variables and `d` the largest
arity. Nothing about the source problem enters the bound – its own `Σ₁` block
rides along inside the guess, over the extended universe, and is read at the
values naming the points.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure ExpExpansion

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

/-- **`NEXPTIME ⊆ ∃SO[new, exp c d]`**: a problem decided in NP over an
exponential expansion is decided by a `Σ₁` sentence that invents at most
`2 ^ (c · nᵈ)` values. -/
theorem ExpDefinable.toSigmaSONewExp (h : ExpDefinable NP P) :
    ∃ c d : ℕ, SigmaSONewExpDefinable c d P := by
  obtain ⟨X, Q, hQ, hX⟩ := h
  have hQ' : SigmaSODefinable 1 Q := hQ
  obtain ⟨Bs, hlen, φ, hφ⟩ := hQ'
  obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨Nat.card (taggedBlock X).ι, blockArityBound (taggedBlock X),
    pullBlock X C, pullSentence X C φ, ?_⟩
  intro A _ _ _
  constructor
  · intro hPA
    let := finiteLinearOrder A
    obtain ⟨σ, hσ⟩ := (hφ (X.Map A)).mp ((hX A).mp hPA)
    obtain ⟨enum⟩ : Nonempty (Fin (Nat.card ((taggedBlock X).Assignment A)) ≃
        (taggedBlock X).Assignment A) := by
      let := Fintype.ofFinite ((taggedBlock X).Assignment A)
      rw [Nat.card_eq_fintype_card]
      exact ⟨(Fintype.equivFin _).symm⟩
    exact ⟨_, card_taggedAssign_le X, buildAssign σ enum,
      pullSentence_forward σ enum φ hσ⟩
  · rintro ⟨m, -, ρ, hρ⟩
    obtain ⟨inst, σ, hσ⟩ := pullSentence_back φ ρ hρ
    let := inst
    exact (hX A).mpr ((hφ (X.Map A)).mpr ⟨σ, hσ⟩)

/-- **`∃SO[new, exp] = NEXPTIME`**: a problem is decided one exponential up in NP
exactly when a `Σ₁` sentence with exponentially bounded value invention decides
it. The two constants are the expansion's – how many variables its block has,
once one nullary variable per tag is added, and how wide they are – and no
single pair serves every problem, so they are quantified. -/
theorem mem_NEXPTIME_iff_sigmaSONewExpDefinable (P : DecisionProblem L) :
    P ∈ NEXPTIME ↔ ∃ c d : ℕ, SigmaSONewExpDefinable c d P := by
  rw [NEXPTIME, ComplexityClass.mem_exp]
  exact ⟨ExpDefinable.toSigmaSONewExp, fun ⟨_, _, h⟩ => h.toExpDefinable⟩

end DescriptiveComplexity
