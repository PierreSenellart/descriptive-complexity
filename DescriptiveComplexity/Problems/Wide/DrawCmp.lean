/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawName
import DescriptiveComplexity.Problems.Wide.DrawOrd

/-!
# What a comparison loop decides

The two remaining atom kinds of a step matrix – equality and order of two
points – are the ones the machine settles by *comparing two argument
blocks*. It cannot look at a block value as a whole: it walks the cells its
marks name, one canonically padded tuple at a time, reading one bit from
each of the two blocks (a **paired** read, which is why these are element
loops and not file tests). This file says that this is enough.

* `DescriptiveComplexity.Draw.Data.encMap_eq_iff_padBits` – two encodings
  are equal exactly when they agree at every padded tuple, because an
  encoding is supported on padded tuples
  (`DescriptiveComplexity.Draw.Data.isPad_of_encMap`) and the encoding is
  injective. So the equality atom is *the loop found no difference*.
* `DescriptiveComplexity.Draw.Data.wmSetLe_encMap_iff_padBits` – the
  binary order of two encodings is decided at the **lexicographically least
  padded tuple where they differ**, the second block containing it. So the
  order atom is *the loop's first difference*, which is why the loop keeps
  the first verdict rather than the last.
* `DescriptiveComplexity.Draw.Data.encOrder_le_iff_padBits` reads the same
  through the order the reduction puts on the points
  (`DescriptiveComplexity.Draw.encOrder`), which is where an order atom of the
  matrix actually lives.

The bridge underneath is `padLt_iff`: padding is an order embedding of the
`dd₀`-tuples the control enumerates into the `dd`-tuples the cells are, since
two padded tuples agree beyond `dd₀` and so are compared inside it.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A : Type}
variable [L.Structure A] [LinearOrder A] [Finite A]

/-! ### Padding is an order embedding -/

variable {dt}

omit [L.Structure A] [Finite A] in
/-- **Two padded tuples compare inside the coordinates they carry**: they
agree beyond `dd₀`, so the lexicographic comparison is settled before it. -/
theorem padLt_iff (zero : A) (w w' : Fin dt.dd0 → A) :
    (∃ p : Fin dt.dd, (∀ j : Fin dt.dd, j < p →
        pad (dd := dt.dd) zero w j = pad (dd := dt.dd) zero w' j) ∧
      pad (dd := dt.dd) zero w p < pad (dd := dt.dd) zero w' p) ↔
      ∃ p : Fin dt.dd0, (∀ j : Fin dt.dd0, j < p → w j = w' j) ∧ w p < w' p := by
  constructor
  · rintro ⟨p, hagree, hlt⟩
    have hp : (p : ℕ) < dt.dd0 := by
      by_contra hc
      rw [pad_of_ge p (Nat.not_lt.mp hc), pad_of_ge p (Nat.not_lt.mp hc)] at hlt
      exact absurd hlt (lt_irrefl zero)
    refine ⟨⟨(p : ℕ), hp⟩, fun j hj => ?_, ?_⟩
    · have hjd : (j : ℕ) < dt.dd0 := lt_trans (Fin.lt_def.mp hj) hp
      have hjp : (⟨(j : ℕ), lt_of_lt_of_le hjd dt.dd0Le⟩ : Fin dt.dd) < p :=
        Fin.lt_def.mpr (Fin.lt_def.mp hj)
      have h := hagree _ hjp
      rw [pad_of_lt (c := dt.dd0) (zero := zero) (w := w)
          (⟨(j : ℕ), lt_of_lt_of_le hjd dt.dd0Le⟩ : Fin dt.dd) hjd,
        pad_of_lt (c := dt.dd0) (zero := zero) (w := w')
          (⟨(j : ℕ), lt_of_lt_of_le hjd dt.dd0Le⟩ : Fin dt.dd) hjd] at h
      exact h
    · rw [pad_of_lt (c := dt.dd0) (zero := zero) (w := w) p hp,
        pad_of_lt (c := dt.dd0) (zero := zero) (w := w') p hp] at hlt
      exact hlt
  · rintro ⟨p, hagree, hlt⟩
    refine ⟨Fin.castLE dt.dd0Le p, fun j hj => ?_, ?_⟩
    · have hjd : (j : ℕ) < dt.dd0 := lt_trans (Fin.lt_def.mp hj) p.isLt
      rw [pad_of_lt (c := dt.dd0) (zero := zero) (w := w) j hjd,
        pad_of_lt (c := dt.dd0) (zero := zero) (w := w') j hjd]
      exact hagree ⟨(j : ℕ), hjd⟩ (Fin.lt_def.mpr (Fin.lt_def.mp hj))
    · rw [pad_of_lt (c := dt.dd0) (zero := zero) (w := w) (Fin.castLE dt.dd0Le p) p.isLt,
        pad_of_lt (c := dt.dd0) (zero := zero) (w := w') (Fin.castLE dt.dd0Le p) p.isLt]
      exact hlt

omit [L.Structure A] [Finite A] in
/-- The strict order the address layer reads on tuples, spelled out. -/
theorem wmLt_tupLeLex_iff' (x y : Fin dt.dd → A) :
    WMLt tupLeLex x y ↔ ∃ p : Fin dt.dd, (∀ j : Fin dt.dd, j < p → x j = y j) ∧ x p < y p := by
  rw [wmLt_tupLeLex_iff]
  exact lex_lt_iff

/-! ### What the loop sees of a block value -/

variable (dt)

/-- **The bits of a block value the loops can read**: its membership question
at the canonically padded tuple of each `dd₀`-tuple – the cells the marks
name. -/
noncomputable def padBits (zero : A) (S : (Fin dt.dd → A) → Prop)
    (w : Fin dt.dd0 → A) : Prop :=
  S (pad (dd := dt.dd) zero w)

variable {dt}

omit [Finite A] in
/-- **An encoding is what its padded bits say**: two encodings agreeing at
every padded tuple agree everywhere, since neither holds off the padded
tuples. -/
theorem encMap_eq_padBits {zero one : A} {p q : dt.X.Map A}
    (h : ∀ w : Fin dt.dd0 → A,
      dt.padBits zero (encMap dt.ly zero one p) w ↔
        dt.padBits zero (encMap dt.ly zero one q) w) :
    encMap dt.ly zero one p = encMap dt.ly zero one q := by
  refine funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩
  · have hpad : v = pad (dd := dt.dd) zero (unpad dt.dd0Le v) :=
      (pad_unpad dt.dd0Le fun j hj => isPad_of_encMap hv j hj).symm
    rw [hpad] at hv ⊢
    exact (h _).mp hv
  · have hpad : v = pad (dd := dt.dd) zero (unpad dt.dd0Le v) :=
      (pad_unpad dt.dd0Le fun j hj => isPad_of_encMap hv j hj).symm
    rw [hpad] at hv ⊢
    exact (h _).mpr hv

omit [Finite A] in
/-- **The equality atom is «the loop found no difference»**: two points are
equal exactly when their encodings agree at every cell the loop visits. -/
theorem encMap_eq_iff_padBits {zero one : A} (hzo : zero ≠ one) {p q : dt.X.Map A} :
    p = q ↔ ∀ w : Fin dt.dd0 → A,
      (dt.padBits zero (encMap dt.ly zero one p) w ↔
        dt.padBits zero (encMap dt.ly zero one q) w) := by
  constructor
  · rintro rfl _
    exact Iff.rfl
  · intro h
    exact encMap_injective dt.ly hzo (encMap_eq_padBits h)

omit [Finite A] in
/-- **The order atom is the loop's first difference**: the binary order of
two encodings is decided at the lexicographically least padded tuple where
they differ. -/
theorem wmSetLe_encMap_iff_padBits {zero one : A} {p q : dt.X.Map A} :
    WMSetLe tupLeLex (encMap dt.ly zero one p) (encMap dt.ly zero one q) ↔
      ((∀ w : Fin dt.dd0 → A,
          (dt.padBits zero (encMap dt.ly zero one p) w ↔
            dt.padBits zero (encMap dt.ly zero one q) w)) ∨
        ∃ w : Fin dt.dd0 → A,
          (∀ w' : Fin dt.dd0 → A,
            (∃ r : Fin dt.dd0, (∀ j : Fin dt.dd0, j < r → w' j = w j) ∧ w' r < w r) →
              (dt.padBits zero (encMap dt.ly zero one p) w' ↔
                dt.padBits zero (encMap dt.ly zero one q) w')) ∧
          ¬dt.padBits zero (encMap dt.ly zero one p) w ∧
            dt.padBits zero (encMap dt.ly zero one q) w) := by
  constructor
  · rintro (hag | ⟨x, hbelow, hpx, hqx⟩)
    · exact Or.inl fun w => hag _
    · have hxpad : pad (dd := dt.dd) zero (unpad dt.dd0Le x) = x :=
        pad_unpad dt.dd0Le fun j hj => isPad_of_encMap hqx j hj
      refine Or.inr ⟨unpad dt.dd0Le x, fun w' hlt => ?_, ?_, ?_⟩
      · have hstep : WMLt tupLeLex (pad (dd := dt.dd) zero w') x := by
          rw [wmLt_tupLeLex_iff' (dt := dt), ← hxpad]
          exact (padLt_iff (dt := dt) zero w' (unpad dt.dd0Le x)).mpr hlt
        exact hbelow _ hstep
      · rw [padBits, hxpad]
        exact hpx
      · rw [padBits, hxpad]
        exact hqx
  · rintro (hag | ⟨w, hbelow, hpw, hqw⟩)
    · exact Or.inl fun v => iff_of_eq (congrFun (encMap_eq_padBits hag) v)
    · refine Or.inr ⟨pad (dd := dt.dd) zero w, fun y hy => ?_, hpw, hqw⟩
      by_cases hypad : ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → y j = zero
      · have hypd : pad (dd := dt.dd) zero (unpad dt.dd0Le y) = y := pad_unpad dt.dd0Le hypad
        have hlt : ∃ r : Fin dt.dd0,
            (∀ j : Fin dt.dd0, j < r → unpad dt.dd0Le y j = w j) ∧
              unpad dt.dd0Le y r < w r := by
          refine (padLt_iff (dt := dt) zero (unpad dt.dd0Le y) w).mp ?_
          rw [hypd]
          exact (wmLt_tupLeLex_iff' (dt := dt) y (pad (dd := dt.dd) zero w)).mp hy
        have hstep := hbelow _ hlt
        rw [padBits, padBits, hypd] at hstep
        exact hstep
      · constructor
        · intro hcon
          exact absurd (fun j hj => isPad_of_encMap hcon j hj) hypad
        · intro hcon
          exact absurd (fun j hj => isPad_of_encMap hcon j hj) hypad

/-- **The order atom, in the order the reduction chose**: the comparison the
loop runs is exactly the order the points carry
(`DescriptiveComplexity.Draw.encOrder`). -/
theorem encOrder_le_iff_padBits {zero one : A} (hzo : zero ≠ one) (p q : dt.X.Map A) :
    (encOrder dt.ly zero one hzo).le p q ↔
      ((∀ w : Fin dt.dd0 → A,
          (dt.padBits zero (encMap dt.ly zero one p) w ↔
            dt.padBits zero (encMap dt.ly zero one q) w)) ∨
        ∃ w : Fin dt.dd0 → A,
          (∀ w' : Fin dt.dd0 → A,
            (∃ r : Fin dt.dd0, (∀ j : Fin dt.dd0, j < r → w' j = w j) ∧ w' r < w r) →
              (dt.padBits zero (encMap dt.ly zero one p) w' ↔
                dt.padBits zero (encMap dt.ly zero one q) w')) ∧
          ¬dt.padBits zero (encMap dt.ly zero one p) w ∧
            dt.padBits zero (encMap dt.ly zero one q) w) :=
  (encOrder_le_iff dt.ly zero one hzo p q).trans wmSetLe_encMap_iff_padBits

end Data

end Draw

end DescriptiveComplexity
