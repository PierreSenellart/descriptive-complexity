/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Sat
import Mathlib.Data.Set.Finite.Lemmas
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity.SatOcc.OccIn
end Lax564036Proofs.DescriptiveComplexity.SatOcc.OccIn

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Sat
end Lax904597.Sat

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax564036Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue NegIn OccIn PosIn)
end Lax564036Proofs.DescriptiveComplexity.SatOcc

/-!
# Literal occurrences of a CNF structure, ordered

Semantic layer shared by the reductions *from* SAT (to 3-colorability, to
3SAT…): literal *occurrences* of a `Language.sat`-structure, their traversal
along a linear order of the universe, and the truth of literals and of prefix
disjunctions under an assignment.

An occurrence of a clause `c` is a pair `(x, s)` with `x` an element and
`s : Bool` a sign, such that `x` occurs in `c` with sign `s` (`OccIn`).
Occurrences are ordered lexicographically (variable first, then sign,
`false < true`): `occLt`. On a finite universe every clause with at least one
occurrence has a first (`MinOcc`) and last (`MaxOcc`) occurrence, and every
occurrence that is not first has an immediate predecessor (`SuccOcc`,
`exists_succOcc`), which is unique in both directions. These are the facts
needed to thread a gadget chain (an OR-gadget chain for 3-colorability, a
clause-splitting chain for 3SAT) along the occurrences of each clause.

For chain-correctness arguments, `LitTrue` states that a literal is true under
an assignment, and `PrefixOr`/`PrefixOrStrict` state that some occurrence of a
clause up to (resp. strictly before) a given position is true; the lemmas
relating them to `MinOcc`/`MaxOcc`/`SuccOcc` implement the usual invariant of
chain constructions.

Everything in this file is first-order definable over
`Language.sat.sum Language.order`; the corresponding formulas and their
realization lemmas are in `DescriptiveComplexity.OccurrenceFormulas`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp] theorem occIn_true {c x : A} : Lax799700.Common.SatOcc.OccIn c x true ↔ Lax799700.Common.SatOcc.IsCl c ∧ Lax799700.Common.SatOcc.PosIn c x := Iff.rfl

@[simp] theorem occIn_false {c x : A} : Lax799700.Common.SatOcc.OccIn c x false ↔ Lax799700.Common.SatOcc.IsCl c ∧ Lax799700.Common.SatOcc.NegIn c x := Iff.rfl

theorem OccIn.isCl {c x : A} {s : Bool} (h : Lax799700.Common.SatOcc.OccIn c x s) : Lax799700.Common.SatOcc.IsCl c := h.1

end SatOcc

end Lax564036Proofs.DescriptiveComplexity

namespace Lax799700.Common.SatOcc.OccIn

export Lax564036Proofs.DescriptiveComplexity.SatOcc.OccIn (isCl)

end Lax799700.Common.SatOcc.OccIn

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- `c` is a clause with no literal: an unsatisfiable clause. -/
def EmptyCl (c : A) : Prop := Lax799700.Common.SatOcc.IsCl c ∧ ∀ x s, ¬Lax799700.Common.SatOcc.OccIn c x s

/-- Bridge from the `Satisfiable` form of clause satisfaction to the
occurrence form. -/
theorem satClauses_occ {ν : A → Prop}
    (hν : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x : A, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x)) :
    ∀ c : A, Lax799700.Common.SatOcc.IsCl c → ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s := by
  intro c hc
  obtain ⟨x, hx⟩ := hν c hc
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · exact ⟨x, true, ⟨hc, hp⟩, hT⟩
  · exact ⟨x, false, ⟨hc, hn⟩, hT⟩

section Order

variable [LinearOrder A]

/-- Strict lexicographic order on occurrence positions: variable first, then
sign (with `false < true`). -/
def occLt (x : A) (s : Bool) (y : A) (t : Bool) : Prop :=
  x < y ∨ (x = y ∧ s < t)

omit [Lax904597.Sat.sat.Structure A] in
theorem occLt_trans {x y z : A} {s t u : Bool} (h₁ : occLt x s y t) (h₂ : occLt y t z u) :
    occLt x s z u := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl h₁
  · exact Or.inl h₂
  · exact Or.inr ⟨rfl, h₁.trans h₂⟩

omit [Lax904597.Sat.sat.Structure A] in
theorem occLt_trichotomy (x : A) (s : Bool) (y : A) (t : Bool) :
    occLt x s y t ∨ (x = y ∧ s = t) ∨ occLt y t x s := by
  rcases lt_trichotomy x y with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy s t with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- `(x, s)` is the first occurrence of the clause `c`. -/
def MinOcc (c x : A) (s : Bool) : Prop :=
  Lax799700.Common.SatOcc.OccIn c x s ∧ ∀ y t, Lax799700.Common.SatOcc.OccIn c y t → ¬occLt y t x s

/-- `(x, s)` is the last occurrence of the clause `c`. -/
def MaxOcc (c x : A) (s : Bool) : Prop :=
  Lax799700.Common.SatOcc.OccIn c x s ∧ ∀ y t, Lax799700.Common.SatOcc.OccIn c y t → ¬occLt x s y t

/-- `(x, s)` is an occurrence of `c` immediately preceded by the occurrence
`(y, t)`. -/
def SuccOcc (c y : A) (t : Bool) (x : A) (s : Bool) : Prop :=
  Lax799700.Common.SatOcc.OccIn c y t ∧ Lax799700.Common.SatOcc.OccIn c x s ∧ occLt y t x s ∧
    ∀ z u, Lax799700.Common.SatOcc.OccIn c z u → ¬(occLt y t z u ∧ occLt z u x s)

/-- `(x, s)` is an occurrence of `c` that is not the first one: an OR-gate of
the chain of `c` sits on it. -/
def Chained (c x : A) (s : Bool) : Prop := Lax799700.Common.SatOcc.OccIn c x s ∧ ¬MinOcc c x s

theorem MaxOcc.occIn {c x : A} {s : Bool} (h : MaxOcc c x s) : Lax799700.Common.SatOcc.OccIn c x s := h.1

/-- Occurrences up to the immediate predecessor `(y, t)` of `(x, s)` are
exactly the occurrences strictly before `(x, s)`. -/
theorem succOcc_occLt_iff {c y x z : A} {t s u : Bool} (hsucc : SuccOcc c y t x s)
    (hz : Lax799700.Common.SatOcc.OccIn c z u) : occLt z u x s ↔ occLt z u y t ∨ (z = y ∧ u = t) := by
  constructor
  · intro h
    rcases occLt_trichotomy z u y t with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd ⟨h', h⟩ (hsucc.2.2.2 z u hz)
  · rintro (h | ⟨rfl, rfl⟩)
    · exact occLt_trans h hsucc.2.2.1
    · exact hsucc.2.2.1

/-- The successor of a given occurrence is unique. -/
theorem succOcc_right_unique {c y x₁ x₂ : A} {t s₁ s₂ : Bool}
    (h₁ : SuccOcc c y t x₁ s₁) (h₂ : SuccOcc c y t x₂ s₂) : x₁ = x₂ ∧ s₁ = s₂ := by
  rcases occLt_trichotomy x₁ s₁ x₂ s₂ with h | h | h
  · exact absurd ⟨h₁.2.2.1, h⟩ (h₂.2.2.2 x₁ s₁ h₁.2.1)
  · exact h
  · exact absurd ⟨h₂.2.2.1, h⟩ (h₁.2.2.2 x₂ s₂ h₂.2.1)

/-! ### Truth of prefix disjunctions -/

/-- Some occurrence of `c` strictly before `(x, s)` is true under `ν`. -/
def PrefixOrStrict (ν : A → Prop) (c x : A) (s : Bool) : Prop :=
  ∃ y t, Lax799700.Common.SatOcc.OccIn c y t ∧ occLt y t x s ∧ Lax799700.Common.SatOcc.LitTrue ν y t

/-- Some occurrence of `c` up to `(x, s)` (inclusive) is true under `ν`. -/
def PrefixOr (ν : A → Prop) (c x : A) (s : Bool) : Prop :=
  ∃ y t, Lax799700.Common.SatOcc.OccIn c y t ∧ (occLt y t x s ∨ (y = x ∧ t = s)) ∧ Lax799700.Common.SatOcc.LitTrue ν y t

theorem prefixOr_iff {ν : A → Prop} {c x : A} {s : Bool} (hx : Lax799700.Common.SatOcc.OccIn c x s) :
    PrefixOr ν c x s ↔ PrefixOrStrict ν c x s ∨ Lax799700.Common.SatOcc.LitTrue ν x s := by
  constructor
  · rintro ⟨y, t, hy, hlt | ⟨rfl, rfl⟩, hT⟩
    · exact Or.inl ⟨y, t, hy, hlt, hT⟩
    · exact Or.inr hT
  · rintro (⟨y, t, hy, hlt, hT⟩ | hT)
    · exact ⟨y, t, hy, Or.inl hlt, hT⟩
    · exact ⟨x, s, hx, Or.inr ⟨rfl, rfl⟩, hT⟩

theorem prefixOrStrict_succ {ν : A → Prop} {c y x : A} {t s : Bool}
    (hsucc : SuccOcc c y t x s) : PrefixOrStrict ν c x s ↔ PrefixOr ν c y t := by
  constructor
  · rintro ⟨z, u, hz, hlt, hT⟩
    exact ⟨z, u, hz, (succOcc_occLt_iff hsucc hz).mp hlt, hT⟩
  · rintro ⟨z, u, hz, h, hT⟩
    exact ⟨z, u, hz, (succOcc_occLt_iff hsucc hz).mpr h, hT⟩

variable [Finite A]

/-- A clause with an occurrence has a last occurrence. -/
theorem exists_maxOcc {c : A} (h : ∃ x s, Lax799700.Common.SatOcc.OccIn c x s) : ∃ x s, MaxOcc c x s := by
  obtain ⟨x₀, hx₀, hmax⟩ :=
    Set.exists_max_image {x : A | ∃ s, Lax799700.Common.SatOcc.OccIn c x s} id (Set.toFinite _)
      (by obtain ⟨x, s, hxs⟩ := h; exact ⟨x, s, hxs⟩)
  by_cases h1 : Lax799700.Common.SatOcc.OccIn c x₀ true
  · refine ⟨x₀, true, h1, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax y ⟨t, hyt⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀⟩ := hx₀
    have hs₀' : s₀ = false := by
      cases s₀ with
      | false => rfl
      | true => exact absurd hs₀ h1
    subst hs₀'
    refine ⟨x₀, false, hs₀, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax y ⟨t, hyt⟩) (not_le.mpr hlt)
    · have ht : t = true := by
        cases t with
        | false => exact absurd hlt (by simp)
        | true => rfl
      exact h1 (ht ▸ hyt)

/-- A non-first occurrence has an immediate predecessor. -/
theorem exists_succOcc {c x : A} {s : Bool} (h : Chained c x s) :
    ∃ y t, SuccOcc c y t x s := by
  have hne : ∃ y, ∃ t, Lax799700.Common.SatOcc.OccIn c y t ∧ occLt y t x s := by
    by_contra hne
    push Not at hne
    exact h.2 ⟨h.1, fun y t hyt hlt => hne y t hyt hlt⟩
  obtain ⟨y₀, hy₀, hmax⟩ :=
    Set.exists_max_image {y : A | ∃ t, Lax799700.Common.SatOcc.OccIn c y t ∧ occLt y t x s} id (Set.toFinite _) hne
  by_cases h1 : Lax799700.Common.SatOcc.OccIn c y₀ true ∧ occLt y₀ true x s
  · refine ⟨y₀, true, h1.1, h.1, h1.2, fun z u hz => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax z ⟨u, hz, hlt₂⟩) (not_le.mpr hlt₁)
    · exact absurd hlt₁ (by simp)
  · obtain ⟨t₀, ht₀, hlt₀⟩ := hy₀
    have ht₀' : t₀ = false := by
      cases t₀ with
      | false => rfl
      | true => exact absurd ⟨ht₀, hlt₀⟩ h1
    subst ht₀'
    refine ⟨y₀, false, ht₀, h.1, hlt₀, fun z u hz => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax z ⟨u, hz, hlt₂⟩) (not_le.mpr hlt₁)
    · have hu : u = true := by
        cases u with
        | false => exact absurd hlt₁ (by simp)
        | true => rfl
      subst hu
      exact h1 ⟨hz, hlt₂⟩

/-- An occurrence with a later occurrence has an immediate successor. -/
theorem exists_succOcc_right {c x : A} {s : Bool} (hx : Lax799700.Common.SatOcc.OccIn c x s)
    (hne : ∃ y t, Lax799700.Common.SatOcc.OccIn c y t ∧ occLt x s y t) : ∃ y t, SuccOcc c x s y t := by
  obtain ⟨y₀, hy₀, hmin⟩ :=
    Set.exists_min_image {y : A | ∃ t, Lax799700.Common.SatOcc.OccIn c y t ∧ occLt x s y t} id (Set.toFinite _)
      (by obtain ⟨y, t, hyt⟩ := hne; exact ⟨y, t, hyt⟩)
  by_cases h0 : Lax799700.Common.SatOcc.OccIn c y₀ false ∧ occLt x s y₀ false
  · refine ⟨y₀, false, hx, h0.1, h0.2, fun z u hz => ?_⟩
    rintro ⟨hlt₁, hlt₂ | ⟨rfl, hlt₂⟩⟩
    · exact absurd (hmin z ⟨u, hz, hlt₁⟩) (not_le.mpr hlt₂)
    · exact absurd hlt₂ (by simp)
  · obtain ⟨t₀, ht₀, hlt₀⟩ := hy₀
    have ht₀' : t₀ = true := by
      cases t₀ with
      | false => exact absurd ⟨ht₀, hlt₀⟩ h0
      | true => rfl
    subst ht₀'
    refine ⟨y₀, true, hx, ht₀, hlt₀, fun z u hz => ?_⟩
    rintro ⟨hlt₁, hlt₂ | ⟨rfl, hlt₂⟩⟩
    · exact absurd (hmin z ⟨u, hz, hlt₁⟩) (not_le.mpr hlt₂)
    · have hu : u = false := by
        cases u with
        | false => rfl
        | true => exact absurd hlt₂ (by simp)
      subst hu
      exact h0 ⟨hz, hlt₁⟩

end Order

end SatOcc

end Lax564036Proofs.DescriptiveComplexity


