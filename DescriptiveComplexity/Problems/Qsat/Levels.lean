/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Prefix

/-!
# The levels of the Savitch recursion, and what a valuation reads

Two independent pieces of bookkeeping for the correctness proof.

## Levels

Levels are the state variables of the input, in the ambient order: the first one
(`DescriptiveComplexity.IsMinSV`) carries the two endpoints of the walk, the last
one (`DescriptiveComplexity.IsMaxSV`) the base case, and each other level receives
its pair from the level just above (`DescriptiveComplexity.IsPredSV`). Those three
notions exist and are unique on a finite order, and
`DescriptiveComplexity.svAbove` – the number of levels from a given one down to the
last – decreases by one at each step, starting from
`DescriptiveComplexity.stateDepth` at the first level and ending at `1`. That is
the depth of `DescriptiveComplexity.SavPow` the level computes.

## What a valuation reads

A valuation of the constructed instance is a predicate on its elements; the
correctness proof only ever reads it through the ten projections below
(`DescriptiveComplexity.stS`, `DescriptiveComplexity.stU`,
`DescriptiveComplexity.bitB`, `DescriptiveComplexity.valP`…), one per variable tag,
which turn it back into the states, bits and valuations the reduction means.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The minimum of the input order -/

section Bot

variable (A : Type) [LinearOrder A] [Finite A] [Nonempty A]

/-- The minimum of the input order: the padding of the coordinates a tag does
not use. -/
noncomputable def qBot : A := (Finite.exists_min (id : A → A)).choose

theorem isBot_qBot : IsBot (qBot A) := (Finite.exists_min (id : A → A)).choose_spec

variable {A}

theorem eq_qBot {q : A} (h : IsBot q) : q = qBot A :=
  le_antisymm (h _) (isBot_qBot A q)

@[simp]
theorem isBot_iff_eq_qBot {q : A} : IsBot q ↔ q = qBot A :=
  ⟨eq_qBot, fun h => h ▸ isBot_qBot A⟩

end Bot

/-! ### The levels -/

section Levels

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
theorem IsMinSV.isSV {ℓ : A} (h : IsMinSV ℓ) : IsSV ℓ := h.1

omit [Finite A] in
theorem IsMaxSV.isSV {ℓ : A} (h : IsMaxSV ℓ) : IsSV ℓ := h.1

omit [Finite A] in
theorem IsMinSV.le {ℓ z : A} (h : IsMinSV ℓ) (hz : IsSV z) : ℓ ≤ z :=
  not_lt.mp (h.2 z hz)

omit [Finite A] in
theorem IsMaxSV.le {ℓ z : A} (h : IsMaxSV ℓ) (hz : IsSV z) : z ≤ ℓ :=
  not_lt.mp (h.2 z hz)

omit [Finite A] in
theorem isMaxSV_unique {ℓ ℓ' : A} (h : IsMaxSV ℓ) (h' : IsMaxSV ℓ') : ℓ = ℓ' :=
  le_antisymm (h'.le h.isSV) (h.le h'.isSV)

omit [Finite A] in
theorem isPredSV_unique {d d' ℓ : A} (h : IsPredSV d ℓ) (h' : IsPredSV d' ℓ) : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hlt
  · exact absurd ⟨hlt, h'.2.2.1⟩ (h.2.2.2 d' h'.1)
  · exact heq
  · exact absurd ⟨hlt, h.2.2.1⟩ (h'.2.2.2 d h.1)

theorem exists_isMinSV {x : A} (hx : IsSV x) : ∃ ℓ : A, IsMinSV ℓ := by
  have : Nonempty {z : A // IsSV z} := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_min (fun z : {z : A // IsSV z} => (z : A))
  exact ⟨m, m.2, fun z hz hlt => absurd (hm ⟨z, hz⟩) (not_le.mpr hlt)⟩

theorem exists_isMaxSV {x : A} (hx : IsSV x) : ∃ ℓ : A, IsMaxSV ℓ := by
  have : Nonempty {z : A // IsSV z} := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun z : {z : A // IsSV z} => (z : A))
  exact ⟨m, m.2, fun z hz hlt => absurd (hm ⟨z, hz⟩) (not_le.mpr hlt)⟩

theorem exists_isPredSV {ℓ : A} (hℓ : IsSV ℓ) (hmin : ¬IsMinSV ℓ) : ∃ d : A, IsPredSV d ℓ := by
  obtain ⟨x, hx, hlt⟩ : ∃ x : A, IsSV x ∧ x < ℓ := by
    by_contra hcon
    exact hmin ⟨hℓ, fun z hz hzl => hcon ⟨z, hz, hzl⟩⟩
  have : Nonempty {z : A // IsSV z ∧ z < ℓ} := ⟨⟨x, hx, hlt⟩⟩
  obtain ⟨d, hd⟩ := Finite.exists_max (fun z : {z : A // IsSV z ∧ z < ℓ} => (z : A))
  refine ⟨d, d.2.1, hℓ, d.2.2, fun z hz hzz => ?_⟩
  exact absurd (hd ⟨z, hz, hzz.2⟩) (not_le.mpr hzz.1)

omit [Finite A] in
theorem IsPredSV.not_isMinSV {d ℓ : A} (h : IsPredSV d ℓ) : ¬IsMinSV ℓ :=
  fun hmin => absurd (hmin.le h.1) (not_le.mpr h.2.2.1)

/-- The number of levels from `ℓ` down to the last one: the depth of the Savitch
recursion that level `ℓ` still has to unfold. -/
noncomputable def svAbove (ℓ : A) : ℕ := Set.ncard {z : A | IsSV z ∧ ℓ ≤ z}

omit [Finite A] in
theorem svAbove_of_isMaxSV {ℓ : A} (h : IsMaxSV ℓ) : svAbove ℓ = 1 := by
  have hset : {z : A | IsSV z ∧ ℓ ≤ z} = {ℓ} := by
    ext z
    refine ⟨fun ⟨hz, hle⟩ => le_antisymm (h.le hz) hle, ?_⟩
    rintro rfl
    exact ⟨h.isSV, le_rfl⟩
  rw [svAbove, hset, Set.ncard_singleton]

theorem svAbove_of_isPredSV {d ℓ : A} (h : IsPredSV d ℓ) : svAbove d = svAbove ℓ + 1 := by
  have hset : {z : A | IsSV z ∧ d ≤ z} = insert d {z : A | IsSV z ∧ ℓ ≤ z} := by
    ext z
    constructor
    · rintro ⟨hz, hle⟩
      rcases hle.lt_or_eq with hlt | heq
      · refine Or.inr ⟨hz, ?_⟩
        by_contra hcon
        exact h.2.2.2 z hz ⟨hlt, not_le.mp hcon⟩
      · exact Or.inl heq.symm
    · rintro (rfl | ⟨hz, hle⟩)
      · exact ⟨h.1, le_rfl⟩
      · exact ⟨hz, h.2.2.1.le.trans hle⟩
  have hnot : d ∉ {z : A | IsSV z ∧ ℓ ≤ z} := fun hd => absurd hd.2 (not_le.mpr h.2.2.1)
  rw [svAbove, hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _), svAbove]

omit [Finite A] in
theorem svAbove_of_isMinSV {ℓ : A} (h : IsMinSV ℓ) : svAbove ℓ = stateDepth A := by
  have hset : {z : A | IsSV z ∧ ℓ ≤ z} = {z : A | IsSV z} := by
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, h.le hz⟩⟩
  rw [svAbove, hset, stateDepth, ← Nat.card_coe_set_eq]
  rfl

theorem exists_isSuccSV {ℓ : A} (hℓ : IsSV ℓ) (hmax : ¬IsMaxSV ℓ) : ∃ ℓ' : A, IsPredSV ℓ ℓ' := by
  obtain ⟨x, hx, hlt⟩ : ∃ x : A, IsSV x ∧ ℓ < x := by
    by_contra hcon
    exact hmax ⟨hℓ, fun z hz hzl => hcon ⟨z, hz, hzl⟩⟩
  have : Nonempty {z : A // IsSV z ∧ ℓ < z} := ⟨⟨x, hx, hlt⟩⟩
  obtain ⟨e, he⟩ := Finite.exists_min (fun z : {z : A // IsSV z ∧ ℓ < z} => (z : A))
  refine ⟨e, hℓ, e.2.1, e.2.2, fun z hz hzz => ?_⟩
  exact absurd (he ⟨z, hz, hzz.1⟩) (not_le.mpr hzz.2)

theorem svAbove_pos {ℓ : A} (hℓ : IsSV ℓ) : 0 < svAbove ℓ := by
  refine Set.ncard_pos (Set.toFinite _) |>.mpr ⟨ℓ, hℓ, le_rfl⟩

end Levels

/-! ### What a valuation reads -/

section Readouts

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable (σ : QM A → Prop)

/-- The source endpoint of the walk, as read by a valuation. -/
def stS : A → Prop := fun a => σ (qVar .sS a (qBot A))

/-- The target endpoint of the walk, as read by a valuation. -/
def stT : A → Prop := fun a => σ (qVar .sT a (qBot A))

/-- The midpoint guessed at a level, as read by a valuation. -/
def stZ (ℓ : A) : A → Prop := fun a => σ (qVar .sZ ℓ a)

/-- The first component of the pair passed below a level. -/
def stU (ℓ : A) : A → Prop := fun a => σ (qVar .sU ℓ a)

/-- The second component of the pair passed below a level. -/
def stV (ℓ : A) : A → Prop := fun a => σ (qVar .sV ℓ a)

/-- The universal bit of a level. -/
def bitB (ℓ : A) : Prop := σ (qVar .sB ℓ (qBot A))

/-- The valuation satisfying the source clauses. -/
def valS : A → Prop := fun a => σ (qVar .aS a (qBot A))

/-- The valuation satisfying the target clauses. -/
def valT : A → Prop := fun a => σ (qVar .aT a (qBot A))

/-- The valuation satisfying the transition clauses. -/
def valP : A → Prop := fun a => σ (qVar .aP a (qBot A))

/-- The bit saying that the base case is an equality rather than a step. -/
def bitE : Prop := σ (qVar .sE (qBot A) (qBot A))

end Readouts

end DescriptiveComplexity
