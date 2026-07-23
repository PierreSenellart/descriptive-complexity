/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Defs
import DescriptiveComplexity.Problems.ThreeSat.ToSat

/-!
# The three slots of a clause

The semantic layer of the reduction of 3SAT to 1-in-SAT. Under the width
bound, a clause has at most three occurrences, so naming them *first*,
*second* and *third* – `DescriptiveComplexity.OneInRed.NthOcc`, defined by walking the
occurrence order from the minimum – covers all of them
(`DescriptiveComplexity.OneInRed.exists_nthOcc`). The gadget then works with three
*slots* per clause, whether or not the corresponding occurrence exists, which
is what removes the width case analysis from the classical construction.

The formulas defining `NthOcc` over the ordered expansion, and their
realization lemmas, are here too: they are built from `minOccF` and `succOccF`
of `DescriptiveComplexity.OccurrenceFormulas`.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace OneInRed

open Language Structure SatOcc

/-- The three slots of a clause. -/
inductive Ix3 : Type
  /-- The first occurrence. -/
  | one
  /-- The second occurrence. -/
  | two
  /-- The third occurrence. -/
  | three
  deriving DecidableEq

instance : Fintype Ix3 := ⟨{Ix3.one, Ix3.two, Ix3.three}, fun x => by cases x <;> decide⟩

instance : Nonempty Ix3 := ⟨Ix3.one⟩

/-- The four fresh variables of the gadget of a clause. -/
inductive Ix4 : Type
  /-- `d`, of the first gadget clause. -/
  | d
  /-- `e`, shared by the first two gadget clauses. -/
  | e
  /-- `f`, shared by the last two gadget clauses. -/
  | f
  /-- `g`, of the last gadget clause. -/
  | g
  deriving DecidableEq

instance : Fintype Ix4 := ⟨{Ix4.d, Ix4.e, Ix4.f, Ix4.g}, fun x => by cases x <;> decide⟩

instance : Nonempty Ix4 := ⟨Ix4.d⟩

/-! ### The `i`-th occurrence of a clause -/

section Semantics

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- `(x, s)` is the `i`-th occurrence of `c`, counted from the first one along
the occurrence order. -/
def NthOcc : Ix3 → A → A → Bool → Prop
  | .one, c, x, s => MinOcc c x s
  | .two, c, x, s => ∃ y t, MinOcc c y t ∧ SuccOcc c y t x s
  | .three, c, x, s => ∃ y t z u, MinOcc c z u ∧ SuccOcc c z u y t ∧ SuccOcc c y t x s

/-- The first occurrence of a clause is unique. -/
theorem minOcc_unique {c x y : A} {s t : Bool} (h₁ : MinOcc c x s) (h₂ : MinOcc c y t) :
    x = y ∧ s = t := by
  rcases occLt_trichotomy x s y t with hlt | heq | hlt
  · exact absurd hlt (h₂.2 x s h₁.occIn)
  · exact heq
  · exact absurd hlt (h₁.2 y t h₂.occIn)

theorem NthOcc.occIn {i : Ix3} {c x : A} {s : Bool} (h : NthOcc i c x s) : OccIn c x s := by
  cases i with
  | one => exact h.1
  | two =>
    obtain ⟨y, t, -, hs⟩ := h
    exact hs.2.1
  | three =>
    obtain ⟨y, t, z, u, -, -, hs⟩ := h
    exact hs.2.1

/-- The `i`-th occurrence of a clause is unique. -/
theorem nthOcc_unique {i : Ix3} {c x y : A} {s t : Bool}
    (h₁ : NthOcc i c x s) (h₂ : NthOcc i c y t) : x = y ∧ s = t := by
  cases i with
  | one => exact minOcc_unique h₁ h₂
  | two =>
    obtain ⟨y₁, t₁, hm₁, hs₁⟩ := h₁
    obtain ⟨y₂, t₂, hm₂, hs₂⟩ := h₂
    obtain ⟨rfl, rfl⟩ := minOcc_unique hm₁ hm₂
    exact succOcc_right_unique hs₁ hs₂
  | three =>
    obtain ⟨y₁, t₁, z₁, u₁, hm₁, ha₁, hs₁⟩ := h₁
    obtain ⟨y₂, t₂, z₂, u₂, hm₂, ha₂, hs₂⟩ := h₂
    obtain ⟨rfl, rfl⟩ := minOcc_unique hm₁ hm₂
    obtain ⟨rfl, rfl⟩ := succOcc_right_unique ha₁ ha₂
    exact succOcc_right_unique hs₁ hs₂

omit [Language.sat.Structure A] in
/-- Occurrences linked by the successor relation are pairwise distinct: they
increase strictly along the occurrence order. -/
private theorem occLt_ne {x y : A} {s t : Bool} (h : occLt x s y t) : ¬(x = y ∧ s = t) := by
  rintro ⟨rfl, rfl⟩
  exact occLt_irrefl x s h

variable [Finite A]

/-- **Under the width bound every occurrence is one of the first three.** A
fourth one would exhibit a chain of four distinct occurrences of the same
clause. -/
theorem exists_nthOcc (hw : WidthAtMostThree A) {c x : A} {s : Bool} (h : OccIn c x s) :
    ∃ i, NthOcc i c x s := by
  by_cases h1 : MinOcc c x s
  · exact ⟨.one, h1⟩
  obtain ⟨y, t, hs1⟩ := exists_succOcc ⟨h, h1⟩
  by_cases h2 : MinOcc c y t
  · exact ⟨.two, y, t, h2, hs1⟩
  obtain ⟨z, u, hs2⟩ := exists_succOcc ⟨hs1.1, h2⟩
  by_cases h3 : MinOcc c z u
  · exact ⟨.three, y, t, z, u, h3, hs2, hs1⟩
  obtain ⟨w, r, hs3⟩ := exists_succOcc ⟨hs2.1, h3⟩
  -- four occurrences `(w, r) < (z, u) < (y, t) < (x, s)`: too many
  exfalso
  have hwz : occLt w r z u := hs3.2.2.1
  have hzy : occLt z u y t := hs2.2.2.1
  have hyx : occLt y t x s := hs1.2.2.1
  obtain ⟨i, j, hij, hxx, hss⟩ :=
    hw c ![w, z, y, x] ![r, u, t, s] (by
      intro i
      fin_cases i
      exacts [hs3.1, hs2.1, hs1.1, h])
  have d12 : ¬(w = z ∧ r = u) := occLt_ne hwz
  have d13 : ¬(w = y ∧ r = t) := occLt_ne (occLt_trans hwz hzy)
  have d14 : ¬(w = x ∧ r = s) := occLt_ne (occLt_trans (occLt_trans hwz hzy) hyx)
  have d23 : ¬(z = y ∧ u = t) := occLt_ne hzy
  have d24 : ¬(z = x ∧ u = s) := occLt_ne (occLt_trans hzy hyx)
  have d34 : ¬(y = x ∧ t = s) := occLt_ne hyx
  fin_cases i <;> fin_cases j <;> simp_all

/-! ### The value carried by a slot -/

/-- The value of the `i`-th slot of `c` under `ν`: the value of the `i`-th
literal of `c`, and `False` when `c` has no `i`-th occurrence. -/
def SlotVal (ν : A → Prop) (i : Ix3) (c : A) : Prop :=
  ∃ x s, NthOcc i c x s ∧ LitTrue ν x s

omit [Finite A] in
theorem slotVal_of_nth {ν : A → Prop} {i : Ix3} {c x : A} {s : Bool}
    (h : NthOcc i c x s) : SlotVal ν i c ↔ LitTrue ν x s := by
  constructor
  · rintro ⟨y, t, hy, hT⟩
    obtain ⟨rfl, rfl⟩ := nthOcc_unique hy h
    exact hT
  · exact fun hT => ⟨x, s, h, hT⟩

/-- **A clause has a true literal iff one of its three slots is true.** -/
theorem exists_litTrue_iff_slot (hw : WidthAtMostThree A) {ν : A → Prop} {c : A} :
    (∃ x s, OccIn c x s ∧ LitTrue ν x s) ↔
      SlotVal ν .one c ∨ SlotVal ν .two c ∨ SlotVal ν .three c := by
  constructor
  · rintro ⟨x, s, hx, hT⟩
    obtain ⟨i, hi⟩ := exists_nthOcc hw hx
    cases i with
    | one => exact Or.inl ⟨x, s, hi, hT⟩
    | two => exact Or.inr (Or.inl ⟨x, s, hi, hT⟩)
    | three => exact Or.inr (Or.inr ⟨x, s, hi, hT⟩)
  · rintro (⟨x, s, hi, hT⟩ | ⟨x, s, hi, hT⟩ | ⟨x, s, hi, hT⟩) <;>
      exact ⟨x, s, hi.occIn, hT⟩

end Semantics

/-! ### The `i`-th occurrence, as a formula -/

section Builders

variable {α : Type}

/-- `(x, s)` is the `i`-th occurrence of `c`, as a formula. -/
noncomputable def nthF : Ix3 → Bool → α → α → satOrd.Formula α
  | .one, s, c, x => minOccF s c x
  | .two, s, c, x =>
      (Formula.iSup fun t : Bool =>
        minOccF t (Sum.inl c) (Sum.inr ()) ⊓
          succOccF t s (Sum.inl c) (Sum.inr ()) (Sum.inl x)).iExs Unit
  | .three, s, c, x =>
      (Formula.iSup fun tu : Bool × Bool =>
        (minOccF tu.2 (Sum.inl c) (Sum.inr 1) ⊓
            succOccF tu.2 tu.1 (Sum.inl c) (Sum.inr 1) (Sum.inr 0)) ⊓
          succOccF tu.1 s (Sum.inl c) (Sum.inr 0) (Sum.inl x)).iExs (Fin 2)

end Builders

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

@[simp]
theorem realize_nthF {i : Ix3} {s : Bool} {c x : α} :
    (nthF i s c x).Realize v ↔ NthOcc i (v c) (v x) s := by
  cases i with
  | one => exact realize_minOccF
  | two =>
    simp only [nthF, NthOcc, Formula.realize_iExs, Formula.realize_iSup,
      Formula.realize_inf, realize_minOccF, realize_succOccF, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨w, t, hm, hs⟩
      exact ⟨w (), t, hm, hs⟩
    · rintro ⟨y, t, hm, hs⟩
      exact ⟨fun _ => y, t, hm, hs⟩
  | three =>
    simp only [nthF, NthOcc, Formula.realize_iExs, Formula.realize_iSup,
      Formula.realize_inf, realize_minOccF, realize_succOccF, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨w, ⟨t, u⟩, ⟨hm, ha⟩, hs⟩
      exact ⟨w 0, t, w 1, u, hm, ha, hs⟩
    · rintro ⟨y, t, z, u, hm, ha, hs⟩
      exact ⟨![y, z], (t, u), ⟨by simpa using hm, by simpa using ha⟩, by simpa using hs⟩

end Realize

end OneInRed

end DescriptiveComplexity
