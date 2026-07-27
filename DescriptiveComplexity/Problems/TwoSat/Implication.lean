/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.TwoSat.Defs
import DescriptiveComplexity.TwoCnf

/-!
# The implication graph of a width-two CNF

The criterion for 2-satisfiability ([Aspvall, Plass & Tarjan
1979][aspvall1979linear]) in the form the PTIME membership of 2SAT needs: a
width-two CNF with no empty clause is satisfiable **iff no variable reaches its
own negation and back** in the implication graph.

The criterion itself is proved once and for all, without any logic, in
`DescriptiveComplexity.TwoCnf`: it is about an arbitrary 2-CNF, given as a relation on
literals over a finite type of variables. This file is its instance for CNF
*structures*: the variables are the elements of the universe, and the clauses
are the pairs of occurrences that cover a clause of the structure
(`DescriptiveComplexity.TwoSatImpl.clauseRel`, using
`DescriptiveComplexity.exists_covering_pair` for the width promise). A clause covered by
`(x, s)` and `(y, u)` is the disjunction `ℓ(x, s) ∨ ℓ(y, u)`, hence the two
implications `¬ℓ(x, s) → ℓ(y, u)` and `¬ℓ(y, u) → ℓ(x, s)`; a unit clause is the
case `(y, u) = (x, s)`, whose implication `¬ℓ(x, s) → ℓ(x, s)` forces the
literal, so it needs no separate treatment.

What the instance has to supply is the dictionary in both directions between
satisfying the structure (some occurrence of every clause is true) and
satisfying the abstract 2-CNF (some literal of every clause is true), which is
where the width promise and the absence of an empty clause are used.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace TwoSatImpl

variable {A : Type} [Language.sat.Structure A]

/-! ### The implication graph of a CNF structure -/

/-- The clause `c` is covered by the two signed occurrences `(x, s)` and
`(y, u)`: both occur in it, and nothing else does. -/
def Covers (c x : A) (s : Bool) (y : A) (u : Bool) : Prop :=
  OccIn c x s ∧ OccIn c y u ∧ ∀ z t, OccIn c z t → (z = x ∧ t = s) ∨ (z = y ∧ t = u)

/-- One step of the implication graph: a clause covered by `(x, s)` and
`(y, u)` implies `¬ℓ(x, s) → ℓ(y, u)` and `¬ℓ(y, u) → ℓ(x, s)`. -/
def Step (p q : A × Bool) : Prop :=
  ∃ (c x : A) (s : Bool) (y : A) (u : Bool), Covers c x s y u ∧
    ((p = (x, !s) ∧ q = (y, u)) ∨ (p = (y, !u) ∧ q = (x, s)))

/-- Reachability in the implication graph. -/
abbrev Reach : (A × Bool) → (A × Bool) → Prop := Relation.ReflTransGen Step

/-! ### Reading the structure as an abstract 2-CNF -/

variable (A) in
/-- The structure read as a 2-CNF in the sense of `DescriptiveComplexity.TwoCnf`: the
variables are the elements, and `p ∨ q` is a clause when some clause of the
structure is covered by the occurrences `p` and `q`. -/
def clauseRel (p q : A × Bool) : Prop := ∃ c : A, Covers c p.1 p.2 q.1 q.2

theorem step_iff (p q : A × Bool) : Step p q ↔ TwoCnf.Step (clauseRel A) p q := by
  constructor
  · rintro ⟨c, x, s, y, u, hcov, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨c, by simpa [TwoCnf.neg] using hcov⟩
    · exact Or.inr ⟨c, by simpa [TwoCnf.neg] using hcov⟩
  · rintro (⟨c, hcov⟩ | ⟨c, hcov⟩)
    · exact ⟨c, p.1, !p.2, q.1, q.2, by simpa [TwoCnf.neg] using hcov,
        Or.inl ⟨by simp, rfl⟩⟩
    · exact ⟨c, q.1, q.2, p.1, !p.2, by simpa [TwoCnf.neg] using hcov,
        Or.inr ⟨by simp, rfl⟩⟩

theorem reach_iff (p q : A × Bool) : Reach p q ↔ TwoCnf.Reach (clauseRel A) p q :=
  ⟨fun h => Relation.ReflTransGen.mono (fun a b hab => (step_iff a b).mp hab) _ _ h,
    fun h => Relation.ReflTransGen.mono (fun a b hab => (step_iff a b).mpr hab) _ _ h⟩

/-- A satisfying assignment of the structure satisfies the abstract 2-CNF. -/
theorem satisfies_of_satClauses {ν : A → Prop}
    (hν : ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s) :
    TwoCnf.Satisfies (clauseRel A) ν := by
  rintro p q ⟨c, hp, hq, hcov⟩
  obtain ⟨z, t, hz, hzT⟩ := hν c hp.isCl
  rcases hcov z t hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hzT
  · exact Or.inr hzT

/-- Conversely, an assignment satisfying the abstract 2-CNF satisfies the
structure – provided the width promise holds and no clause is empty, which is
what makes every clause the disjunction of a covering pair. -/
theorem satisfiable_of_satisfies (hw : WidthAtMostTwo A) (hempty : ∀ c : A, ¬EmptyCl c)
    {ν : A → Prop} (h : TwoCnf.Satisfies (clauseRel A) ν) : Satisfiable A := by
  refine ⟨ν, fun c hc => ?_⟩
  obtain ⟨x, s, hx⟩ : ∃ (x : A) (s : Bool), OccIn c x s := by
    by_contra hno
    push Not at hno
    exact hempty c ⟨hc, fun z t => hno z t⟩
  obtain ⟨y, u, hy, hcov⟩ := exists_covering_pair hw hx
  have hcl : clauseRel A (x, s) (y, u) := ⟨c, hx, hy, hcov⟩
  rcases h _ _ hcl with hT | hT
  · cases s with
    | false => exact ⟨x, Or.inr ⟨hx.2, hT⟩⟩
    | true => exact ⟨x, Or.inl ⟨hx.2, hT⟩⟩
  · cases u with
    | false => exact ⟨y, Or.inr ⟨hy.2, hT⟩⟩
    | true => exact ⟨y, Or.inl ⟨hy.2, hT⟩⟩

/-! ### The criterion, for CNF structures -/

/-- **No satisfiable instance has a bad cycle**: a variable reaching its own
negation and back would be both true and false. -/
theorem no_bad_cycle_of_satisfiable (h : Satisfiable A) (x : A) (s : Bool) :
    ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s)) := by
  obtain ⟨ν, hν⟩ := h
  rintro ⟨h1, h2⟩
  refine TwoCnf.no_bad_cycle_of_satisfies (clauseRel A)
    (satisfies_of_satClauses (satClauses_occ hν)) (x, s) ⟨?_, ?_⟩
  · exact (reach_iff _ _).mp h1
  · exact (reach_iff _ _).mp h2

variable [Finite A]

/-- **The criterion for 2-satisfiability**: a width-two CNF with no empty
clause and no variable reaching its own negation and back is satisfiable. This
is `DescriptiveComplexity.TwoCnf.exists_satisfies_of_no_bad_cycle` read through the
dictionary above. -/
theorem satisfiable_of_no_bad_cycle (hw : WidthAtMostTwo A)
    (hempty : ∀ c : A, ¬EmptyCl c)
    (hcyc : ∀ (x : A) (s : Bool),
      ¬(Reach ((x, s) : A × Bool) (x, !s) ∧ Reach ((x, !s) : A × Bool) (x, s))) :
    Satisfiable A := by
  obtain ⟨ν, hν⟩ := TwoCnf.exists_satisfies_of_no_bad_cycle (Cl := clauseRel A) fun x s => by
    rintro ⟨h1, h2⟩
    exact hcyc x s ⟨(reach_iff _ _).mpr h1, (reach_iff _ _).mpr h2⟩
  exact satisfiable_of_satisfies hw hempty hν

end TwoSatImpl

end DescriptiveComplexity
