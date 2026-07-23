/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Sort

/-!
# A tour is a cyclic enumeration

`DescriptiveComplexity.TourOn` reads a Hamilton circuit as a *linear order* of the
universe, which is what an existential second-order block can guess. This file
shows that reading is the intended one: a tour is exactly a **cyclic
enumeration** of the universe along which consecutive elements are adjacent
(`DescriptiveComplexity.tourOn_iff_enum`).

Both halves are what a reduction into either Hamilton problem consumes. A
gadget builds its circuit as an explicit enumeration and needs
`DescriptiveComplexity.tourOn_of_enum`; conversely it reads a given circuit through
the cyclic successor `f (nextIdx i)` (`DescriptiveComplexity.enum_of_tourOn`), whose
local structure – every vertex is left once and reached once – is what forces
a gadget to be traversed the intended way.
-/

namespace DescriptiveComplexity

open FirstOrder

section Enum

variable {A : Type}

/-- The next index, cyclically: the last one wraps around to the first. -/
def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩

theorem nextIdx_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n) :
    (nextIdx i : ℕ) = (i : ℕ) + 1 := by
  rw [nextIdx]
  exact Nat.mod_eq_of_lt h

theorem nextIdx_of_last {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 = n) : (nextIdx i : ℕ) = 0 := by
  rw [nextIdx]
  simp [h]

/-- **An enumeration is a tour**: order the universe by the position of each
element; consecutive positions are then consecutive in that order, and the
last position wraps to the first. -/
theorem tourOn_of_enum {R : A → A → Prop} {n : ℕ} (f : Fin n ≃ A)
    (h : ∀ i : Fin n, R (f i) (f (nextIdx i))) : TourOn R := by
  classical
  refine ⟨fun x y => f.symm x ≤ f.symm y,
    isLinOrd_of_key isLinOrd_le f.symm f.symm.injective fun _ _ => Iff.rfl, ?_, ?_⟩
  · rintro x y ⟨hle, hne, hbetween⟩
    have hlt : f.symm x < f.symm y := lt_of_le_of_ne hle fun he => hne (f.symm.injective he)
    have hstep : (f.symm y : ℕ) = (f.symm x : ℕ) + 1 := by
      by_contra hcon
      have hgt : (f.symm x : ℕ) + 1 < (f.symm y : ℕ) := by
        have hlt' := hlt
        simp only [Fin.lt_def] at hlt'
        omega
      set k : Fin n := ⟨(f.symm x : ℕ) + 1, lt_trans hgt (f.symm y).isLt⟩ with hk
      have h₁ : f.symm x ≤ k := by
        simp only [Fin.le_def, hk]
        omega
      have h₂ : k ≤ f.symm y := by
        simp only [Fin.le_def, hk]
        omega
      rcases hbetween (f k) (by simpa using h₁) (by simpa using h₂) with hx | hy
      · have hkx : k = f.symm x := by
          rw [← hx]
          simp
        rw [hk] at hkx
        exact absurd (congrArg Fin.val hkx) (by simp)
      · have hky : k = f.symm y := by
          rw [← hy]
          simp
        rw [hk] at hky
        exact absurd (congrArg Fin.val hky) (by simp; omega)
    have hsucc : nextIdx (f.symm x) = f.symm y := by
      refine Fin.ext ?_
      rw [nextIdx_of_lt (by rw [← hstep]; exact (f.symm y).isLt), hstep]
    have hR := h (f.symm x)
    rw [hsucc] at hR
    simpa using hR
  · intro x y hx hy
    have hx0 : (f.symm x : ℕ) = 0 := by
      have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact (f.symm x).elim0)
      have h0 := hx (f ⟨0, hpos⟩)
      simp only [Equiv.symm_apply_apply, Fin.le_def] at h0
      omega
    have hylast : (f.symm y : ℕ) + 1 = n := by
      have hle : ∀ i : Fin n, i ≤ f.symm y := fun i => by simpa using hy (f i)
      have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact (f.symm y).elim0)
      have hle' : (n : ℕ) - 1 ≤ (f.symm y : ℕ) := by
        have := hle ⟨n - 1, by omega⟩
        simpa [Fin.le_def] using this
      have := (f.symm y).isLt
      omega
    have hwrap : nextIdx (f.symm y) = f.symm x :=
      Fin.ext ((nextIdx_of_last hylast).trans hx0.symm)
    have hR := h (f.symm y)
    rw [hwrap] at hR
    simpa using hR

variable [Finite A]

/-- **A tour is an enumeration**: reading the universe along the order the
tour carries lists every element exactly once, consecutive ones being
adjacent, and the last one adjacent to the first. -/
theorem enum_of_tourOn {R : A → A → Prop} (h : TourOn R) :
    ∃ (n : ℕ) (f : Fin n ≃ A), ∀ i : Fin n, R (f i) (f (nextIdx i)) := by
  classical
  obtain ⟨Le, hlin, hsucc, hwrap⟩ := h
  letI : LinearOrder A := IsLinOrd.toLinearOrder hlin
  haveI : Fintype A := Fintype.ofFinite A
  refine ⟨Fintype.card A, (monoEquivOfFin A rfl).toEquiv, fun i => ?_⟩
  set f := (monoEquivOfFin A rfl).toEquiv with hf
  have hle : ∀ a b : A, a ≤ b ↔ Le a b := fun _ _ => Iff.rfl
  have hmono : ∀ j k : Fin (Fintype.card A), Le (f j) (f k) ↔ j ≤ k := fun j k =>
    (hle _ _).symm.trans (monoEquivOfFin A rfl).le_iff_le
  have hinv : ∀ j : Fin (Fintype.card A), f.symm (f j) = j := fun j => f.symm_apply_apply j
  by_cases hlast : (i : ℕ) + 1 < Fintype.card A
  · -- an interior index: the next one is its immediate successor in the order
    have hkval : (nextIdx i : ℕ) = (i : ℕ) + 1 := nextIdx_of_lt hlast
    refine hsucc (f i) (f (nextIdx i))
      ⟨(hmono i (nextIdx i)).mpr (by simp [Fin.le_def, hkval]), ?_, ?_⟩
    · intro he
      have hii := congrArg f.symm he
      rw [hinv, hinv] at hii
      exact absurd (congrArg Fin.val hii) (by simp [hkval])
    · intro z h₁ h₂
      have h₁' : i ≤ f.symm z := (hmono i (f.symm z)).mp (by simpa using h₁)
      have h₂' : f.symm z ≤ nextIdx i := (hmono (f.symm z) (nextIdx i)).mp (by simpa using h₂)
      simp only [Fin.le_def] at h₁' h₂'
      rcases Nat.lt_or_ge (f.symm z : ℕ) ((i : ℕ) + 1) with hz | hz
      · left
        have hzi : f.symm z = i := Fin.ext (by omega)
        rw [← hzi]
        simp
      · right
        have hzi : f.symm z = nextIdx i := Fin.ext (by omega)
        rw [← hzi]
        simp
  · -- the last index: it wraps to the first, which is the bottom of the order
    have hcard : (i : ℕ) + 1 = Fintype.card A := by
      have := i.isLt
      omega
    have hzero : (nextIdx i : ℕ) = 0 := nextIdx_of_last hcard
    have hbot : ∀ z : A, Le (f (nextIdx i)) z := by
      intro z
      have := (hmono (nextIdx i) (f.symm z)).mpr (by simp [Fin.le_def, hzero])
      simpa using this
    have htop : ∀ z : A, Le z (f i) := by
      intro z
      have hz : f.symm z ≤ i := by
        have := (f.symm z).isLt
        simp only [Fin.le_def]
        omega
      have := (hmono (f.symm z) i).mpr hz
      simpa using this
    exact hwrap (f (nextIdx i)) (f i) hbot htop

/-- **A tour is exactly a cyclic enumeration**: the two readings of a Hamilton
circuit agree. -/
theorem tourOn_iff_enum {R : A → A → Prop} :
    TourOn R ↔ ∃ (n : ℕ) (f : Fin n ≃ A), ∀ i : Fin n, R (f i) (f (nextIdx i)) :=
  ⟨enum_of_tourOn, fun ⟨_, f, h⟩ => tourOn_of_enum f h⟩

end Enum

end DescriptiveComplexity
