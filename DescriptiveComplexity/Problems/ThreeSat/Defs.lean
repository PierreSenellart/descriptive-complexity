/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceOrder

/-!
# 3SAT: definition

The problem 3SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT: a
CNF structure is a yes-instance iff every clause has at most three literal
occurrences (`DescriptiveComplexity.WidthAtMostThree`) *and* the CNF is satisfiable
(`DescriptiveComplexity.ThreeSatisfiable`, bundled as `DescriptiveComplexity.ThreeSAT`).

Folding the width bound into the yes-instances (rather than into the
vocabulary) is what makes 3SAT a decision problem on arbitrary
`Language.sat`-structures; the bound "at most three" is expressed without
counting, as: among any four literal occurrences of a clause, two coincide.

The reductions to and from SAT, and NP-completeness, are in
`DescriptiveComplexity.Problems.ThreeSat`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

section ThreeSat

variable (A : Type) [Language.sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most three literal
occurrences: among any four occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostThree : Prop :=
  ∀ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

/-- A `Language.sat`-structure is a yes-instance of 3SAT if every clause has
at most three literal occurrences and the CNF is satisfiable. -/
def ThreeSatisfiable : Prop :=
  WidthAtMostThree A ∧ Satisfiable A

end ThreeSat

section Iso

private theorem comp_vec₁ {A B : Type} (f : A → B) (a : A) : f ∘ ![a] = ![f a] := by
  funext j
  fin_cases j
  simp

private theorem comp_vec₂ {A B : Type} (f : A → B) (a b : A) : f ∘ ![a, b] = ![f a, f b] := by
  funext j
  fin_cases j <;> simp

/-- Isomorphisms preserve literal occurrences. -/
private theorem occIn_map {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]
    (e : A ≃[Language.sat] B) {c x : A} {s : Bool} (h : OccIn c x s) : OccIn (e c) (e x) s := by
  obtain ⟨hc, hs⟩ := h
  constructor
  · have h' := StrongHomClass.map_rel e satIsClause ![c]
    rw [comp_vec₁] at h'
    exact h'.mpr hc
  · cases s with
    | false =>
      have h' := StrongHomClass.map_rel e satNegIn ![c, x]
      rw [comp_vec₂] at h'
      exact h'.mpr hs
    | true =>
      have h' := StrongHomClass.map_rel e satPosIn ![c, x]
      rw [comp_vec₂] at h'
      exact h'.mpr hs

private theorem widthAtMostThree_of_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) (h : WidthAtMostThree A) :
    WidthAtMostThree B := by
  intro c x s hocc
  obtain ⟨i, j, hij, hx, hs⟩ :=
    h (e.symm c) (fun i => e.symm (x i)) s fun i => occIn_map e.symm (hocc i)
  refine ⟨i, j, hij, ?_, hs⟩
  have := congrArg e hx
  simpa using this

/-- 3-satisfiability is isomorphism-invariant. -/
theorem threeSatisfiable_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) :
    ThreeSatisfiable A ↔ ThreeSatisfiable B :=
  and_congr ⟨widthAtMostThree_of_iso e, widthAtMostThree_of_iso e.symm⟩ (satisfiable_iso e)

end Iso

/-- 3SAT, as a problem on `Language.sat`-structures: the same vocabulary as
SAT, with the width bound folded into the yes-instances. -/
def ThreeSAT : DecisionProblem Language.sat where
  Holds := fun A inst => @ThreeSatisfiable A inst
  iso_invariant := fun e => threeSatisfiable_iso e

end DescriptiveComplexity
