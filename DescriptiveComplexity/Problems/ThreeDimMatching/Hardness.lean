/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.OccurrenceVar
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.Padding

/-!
# 3-dimensional matching is NP-hard

The reduction is Karp's, from SATISFIABILITY, with its three families of
triples read off the *occurrences* of the input formula. Write `(c, s)` for a
signed occurrence – the clause `c` contains the literal `(x, s)` – and let a
*tip* be one of the two `X`-elements `tip(x, c, s, σ)` attached to it.

* **The truth-setting gadget.** For each occurrence of a variable `x` there is
  a `Y`-element `a(x, c, s)` and a `Z`-element `b(x, c, s)`, and two triples

  ```
  (tip(x, c, s, true),  a(x, c, s),   b(x, c, s))
  (tip(x, c, s, false), a(x, c', t),  b(x, c, s))     (c', t) = next(c, s)
  ```

  where `next` runs **cyclically** through the occurrences of `x`
  (`DescriptiveComplexity.SatOcc.VarNext`). Covering every `b` picks one triple per
  occurrence, and covering every `a` then forces the choice to be the *same*
  all around the cycle: the gadget is a truth value, and it frees the tips of
  one side.
* **The clause gadget.** Each clause `c` has a `Y`-element and a `Z`-element
  of its own, coverable only by a triple `(tip(x, c, s, !s), …)`. That tip is
  free exactly when the literal `(x, s)` is true, so covering the clause pair
  is satisfying the clause.
* **Garbage collection.** The tips left over have to be covered too, by
  triples pairing *any* tip with a private `Y`/`Z` pair. There must be exactly
  as many such pairs as there are leftover tips, and that number is
  `#occurrences − #clauses`: the pairs are therefore indexed by the
  occurrences that are **not the first of their clause**
  (`DescriptiveComplexity.SatOcc.Chained`), the same counting trick the reductions to
  Partition and to job sequencing use for their slack items.

Nothing here bounds the width of a clause, so the source is SAT itself; an
empty clause leaves its two elements uncoverable, which is the right answer.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace TDMRed

open Language Structure SatOcc

/-! ### The tags -/

/-- Tags of the reduction: the two tips of an occurrence, the two elements of
its truth-setting gadget, the two elements of a clause, and the two elements
of a garbage pair. -/
inductive TTag : Type
  /-- The `σ`-tip of the occurrence `(c, s)` of `x`; its tuple is `(x, c)`. -/
  | tip (s σ : Bool)
  /-- The `Y`-element of the occurrence `(c, s)` of `x`; its tuple is
  `(x, c)`. -/
  | av (s : Bool)
  /-- The `Z`-element of the occurrence `(c, s)` of `x`; its tuple is
  `(x, c)`. -/
  | bv (s : Bool)
  /-- The `Y`-element of the clause `c`; its tuple is `(c, ⊥)`. -/
  | cy
  /-- The `Z`-element of the clause `c`; its tuple is `(c, ⊥)`. -/
  | cz
  /-- The `Y`-element of the garbage pair of a non-first occurrence `(x, s)`
  of `c`; its tuple is `(x, c)`. -/
  | gy (s : Bool)
  /-- The `Z`-element of that garbage pair; its tuple is `(x, c)`. -/
  | gz (s : Bool)
  deriving DecidableEq

instance : Fintype TTag where
  elems :=
    {.tip false false, .tip false true, .tip true false, .tip true true,
      .av false, .av true, .bv false, .bv true, .cy, .cz,
      .gy false, .gy true, .gz false, .gz true}
  complete := by
    intro t
    cases t with
    | tip s σ => cases s <;> cases σ <;> decide
    | av s => cases s <;> decide
    | bv s => cases s <;> decide
    | cy => decide
    | cz => decide
    | gy s => cases s <;> decide
    | gz s => cases s <;> decide

instance : Nonempty TTag := ⟨TTag.cy⟩

/-! ### The interpretation -/

section Formulas

variable {α : Type}

/-- A minimum of the order, as a formula over the ordered expansion of the
vocabulary of CNF instances. -/
noncomputable def minF (x : α) : satOrd.Formula α := botF (L := Language.sat) x

@[simp]
theorem realize_minF {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : α → A}
    {x : α} : (minF x).Realize v ↔ IsBot (v x) :=
  realize_botF

/-- Defining formula for the first class: the tips of the occurrences. -/
noncomputable def xElF : TTag → satOrd.Formula (Fin 1 × Fin 2)
  | .tip s _ => occF s (0, 1) (0, 0)
  | _ => ⊥

/-- Defining formula for the second class: one element per occurrence, per
clause and per non-first occurrence. -/
noncomputable def yElF : TTag → satOrd.Formula (Fin 1 × Fin 2)
  | .av s => occF s (0, 1) (0, 0)
  | .cy => clF (0, 0) ⊓ minF (0, 1)
  | .gy s => chainedF s (0, 1) (0, 0)
  | _ => ⊥

/-- Defining formula for the third class, mirroring the second. -/
noncomputable def zElF : TTag → satOrd.Formula (Fin 1 × Fin 2)
  | .bv s => occF s (0, 1) (0, 0)
  | .cz => clF (0, 0) ⊓ minF (0, 1)
  | .gz s => chainedF s (0, 1) (0, 0)
  | _ => ⊥

/-- Defining formula for the triples: the two of the truth-setting gadget of
each occurrence, one per occurrence of a clause, and one per tip and garbage
pair. -/
noncomputable def tripF : TTag → TTag → TTag → satOrd.Formula (Fin 3 × Fin 2)
  | .tip s σ, .av t, .bv u =>
      if σ = true then
        (if s = t ∧ s = u then
          occF s (0, 1) (0, 0) ⊓ eqF (1, 0) (0, 0) ⊓ eqF (1, 1) (0, 1) ⊓
            eqF (2, 0) (0, 0) ⊓ eqF (2, 1) (0, 1)
        else ⊥)
      else
        (if s = u then
          varNextF s t (0, 0) (0, 1) (1, 1) ⊓ eqF (1, 0) (0, 0) ⊓
            eqF (2, 0) (0, 0) ⊓ eqF (2, 1) (0, 1)
        else ⊥)
  | .tip s σ, .cy, .cz =>
      if σ = !s then
        occF s (0, 1) (0, 0) ⊓ eqF (1, 0) (0, 1) ⊓ minF (1, 1) ⊓
          eqF (2, 0) (0, 1) ⊓ minF (2, 1)
      else ⊥
  | .tip s _, .gy t, .gz u =>
      if t = u then
        occF s (0, 1) (0, 0) ⊓ chainedF t (1, 1) (1, 0) ⊓
          eqF (2, 0) (1, 0) ⊓ eqF (2, 1) (1, 1)
      else ⊥
  | _, _, _ => ⊥

/-- The interpretation of a triple system in a CNF structure. -/
noncomputable def tdmInterp : FOInterpretation satOrd Language.tripleSys TTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .xEl => fun t => xElF (t 0)
    | _, .yEl => fun t => yElF (t 0)
    | _, .zEl => fun t => zElF (t 0)
    | _, .trip => fun t => tripF (t 0) (t 1) (t 2)

end Formulas

/-! ### The points of the interpreted structure -/

section Points

variable {A : Type}

/-- The point of tag `t` over the pair `w`. -/
def tPt (t : TTag) (w : Fin 2 → A) : tdmInterp.Map A := (t, w)

theorem tPt_surj (q : tdmInterp.Map A) : ∃ t w, q = tPt t w := ⟨q.1, q.2, rfl⟩

theorem tPt_eq_iff {t t' : TTag} {w w' : Fin 2 → A} :
    tPt t w = tPt t' w' ↔ t = t' ∧ w = w' := by
  constructor
  · intro h
    exact ⟨congrArg (fun q : tdmInterp.Map A => q.1) h,
      congrArg (fun q : tdmInterp.Map A => q.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Two `2`-tuples with the same coordinates are equal. -/
theorem tuple₂_ext {w w' : Fin 2 → A} (h0 : w 0 = w' 0) (h1 : w 1 = w' 1) : w = w' := by
  funext j
  fin_cases j
  · exact h0
  · exact h1

/-- The `σ`-tip of the occurrence `(c, s)` of `x`. -/
def tTip (s σ : Bool) (x c : A) : tdmInterp.Map A := tPt (.tip s σ) ![x, c]

/-- The second-class element of the occurrence `(c, s)` of `x`. -/
def tAv (s : Bool) (x c : A) : tdmInterp.Map A := tPt (.av s) ![x, c]

/-- The third-class element of the occurrence `(c, s)` of `x`. -/
def tBv (s : Bool) (x c : A) : tdmInterp.Map A := tPt (.bv s) ![x, c]

/-- The second-class element of the clause `c`. -/
def tCy (a₀ c : A) : tdmInterp.Map A := tPt .cy ![c, a₀]

/-- The third-class element of the clause `c`. -/
def tCz (a₀ c : A) : tdmInterp.Map A := tPt .cz ![c, a₀]

/-- The second-class element of the garbage pair of the occurrence `(x, s)`
of `c`. -/
def tGy (s : Bool) (x c : A) : tdmInterp.Map A := tPt (.gy s) ![x, c]

/-- The third-class element of that garbage pair. -/
def tGz (s : Bool) (x c : A) : tdmInterp.Map A := tPt (.gz s) ![x, c]

theorem tTip_eq_iff {s σ s' σ' : Bool} {x c x' c' : A} :
    tTip s σ x c = tTip s' σ' x' c' ↔ s = s' ∧ σ = σ' ∧ x = x' ∧ c = c' := by
  rw [tTip, tTip, tPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · injection ht
    · injection ht
    · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tAv_eq_iff {s s' : Bool} {x c x' c' : A} :
    tAv s x c = tAv s' x' c' ↔ s = s' ∧ x = x' ∧ c = c' := by
  rw [tAv, tAv, tPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · injection ht
    · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tBv_eq_iff {s s' : Bool} {x c x' c' : A} :
    tBv s x c = tBv s' x' c' ↔ s = s' ∧ x = x' ∧ c = c' := by
  rw [tBv, tBv, tPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · injection ht
    · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tGy_eq_iff {s s' : Bool} {x c x' c' : A} :
    tGy s x c = tGy s' x' c' ↔ s = s' ∧ x = x' ∧ c = c' := by
  rw [tGy, tGy, tPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · injection ht
    · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tGz_eq_iff {s s' : Bool} {x c x' c' : A} :
    tGz s x c = tGz s' x' c' ↔ s = s' ∧ x = x' ∧ c = c' := by
  rw [tGz, tGz, tPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · injection ht
    · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
    · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tCz_eq_iff {a₀ c c' : A} : tCz a₀ c = tCz a₀ c' ↔ c = c' := by
  rw [tCz, tCz, tPt_eq_iff]
  constructor
  · rintro ⟨-, hw⟩
    simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem tCy_eq_iff {a₀ c c' : A} : tCy a₀ c = tCy a₀ c' ↔ c = c' := by
  rw [tCy, tCy, tPt_eq_iff]
  constructor
  · rintro ⟨-, hw⟩
    simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  · rintro rfl
    exact ⟨rfl, rfl⟩

end Points

/-! ### The three classes -/

section Classes

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

@[simp]
theorem tsX_tip (s σ : Bool) (x c : A) : TSXEl (tTip s σ x c) ↔ OccIn c x s := by
  rw [TSXEl, tTip, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, xElF]

@[simp]
theorem tsY_av (s : Bool) (x c : A) : TSYEl (tAv s x c) ↔ OccIn c x s := by
  rw [TSYEl, tAv, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, yElF]

@[simp]
theorem tsZ_bv (s : Bool) (x c : A) : TSZEl (tBv s x c) ↔ OccIn c x s := by
  rw [TSZEl, tBv, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, zElF]

@[simp]
theorem tsY_cy {a₀ : A} (ha₀ : IsBot a₀) (c : A) : TSYEl (tCy a₀ c) ↔ IsCl c := by
  rw [TSYEl, tCy, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, yElF, ha₀]

@[simp]
theorem tsZ_cz {a₀ : A} (ha₀ : IsBot a₀) (c : A) : TSZEl (tCz a₀ c) ↔ IsCl c := by
  rw [TSZEl, tCz, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, zElF, ha₀]

@[simp]
theorem tsY_gy (s : Bool) (x c : A) : TSYEl (tGy s x c) ↔ Chained c x s := by
  rw [TSYEl, tGy, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, yElF]

@[simp]
theorem tsZ_gz (s : Bool) (x c : A) : TSZEl (tGz s x c) ↔ Chained c x s := by
  rw [TSZEl, tGz, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, zElF]

/-- Every element of the first class is a tip. -/
theorem tsX_shape {q : tdmInterp.Map A} (h : TSXEl q) :
    ∃ s σ x c, OccIn c x s ∧ q = tTip s σ x c := by
  obtain ⟨t, w, rfl⟩ := tPt_surj q
  rw [TSXEl, tPt, FOInterpretation.relMap_map] at h
  cases t with
  | tip s σ =>
    refine ⟨s, σ, w 0, w 1, by simpa [tdmInterp, xElF] using h, ?_⟩
    rw [tTip]
    exact congrArg (tPt (TTag.tip s σ)) (tuple₂_ext (by simp) (by simp)).symm
  | av s => exact absurd h (by simp [tdmInterp, xElF])
  | bv s => exact absurd h (by simp [tdmInterp, xElF])
  | cy => exact absurd h (by simp [tdmInterp, xElF])
  | cz => exact absurd h (by simp [tdmInterp, xElF])
  | gy s => exact absurd h (by simp [tdmInterp, xElF])
  | gz s => exact absurd h (by simp [tdmInterp, xElF])

/-- Every element of the second class is one of the three kinds. -/
theorem tsY_shape {a₀ : A} (ha₀ : IsBot a₀) {q : tdmInterp.Map A} (h : TSYEl q) :
    (∃ s x c, OccIn c x s ∧ q = tAv s x c) ∨ (∃ c, IsCl c ∧ q = tCy a₀ c) ∨
      ∃ s x c, Chained c x s ∧ q = tGy s x c := by
  obtain ⟨t, w, rfl⟩ := tPt_surj q
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  rw [TSYEl, tPt, FOInterpretation.relMap_map] at h
  cases t with
  | av s =>
    refine Or.inl ⟨s, w 0, w 1, by simpa [tdmInterp, yElF] using h, ?_⟩
    rw [tAv]
    exact congrArg (tPt (TTag.av s)) (tuple₂_ext (by simp) (by simp)).symm
  | cy =>
    have h' : IsCl (w 0) ∧ IsBot (w 1) := by simpa [tdmInterp, yElF] using h
    refine Or.inr (Or.inl ⟨w 0, h'.1, ?_⟩)
    rw [tCy]
    exact congrArg (tPt TTag.cy)
      (tuple₂_ext (by simp) (by simp [hbot (w 1) h'.2])).symm
  | gy s =>
    refine Or.inr (Or.inr ⟨s, w 0, w 1, by simpa [tdmInterp, yElF] using h, ?_⟩)
    rw [tGy]
    exact congrArg (tPt (TTag.gy s)) (tuple₂_ext (by simp) (by simp)).symm
  | tip s σ => exact absurd h (by simp [tdmInterp, yElF])
  | bv s => exact absurd h (by simp [tdmInterp, yElF])
  | cz => exact absurd h (by simp [tdmInterp, yElF])
  | gz s => exact absurd h (by simp [tdmInterp, yElF])

/-- Every element of the third class is one of the three kinds. -/
theorem tsZ_shape {a₀ : A} (ha₀ : IsBot a₀) {q : tdmInterp.Map A} (h : TSZEl q) :
    (∃ s x c, OccIn c x s ∧ q = tBv s x c) ∨ (∃ c, IsCl c ∧ q = tCz a₀ c) ∨
      ∃ s x c, Chained c x s ∧ q = tGz s x c := by
  obtain ⟨t, w, rfl⟩ := tPt_surj q
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  rw [TSZEl, tPt, FOInterpretation.relMap_map] at h
  cases t with
  | bv s =>
    refine Or.inl ⟨s, w 0, w 1, by simpa [tdmInterp, zElF] using h, ?_⟩
    rw [tBv]
    exact congrArg (tPt (TTag.bv s)) (tuple₂_ext (by simp) (by simp)).symm
  | cz =>
    have h' : IsCl (w 0) ∧ IsBot (w 1) := by simpa [tdmInterp, zElF] using h
    refine Or.inr (Or.inl ⟨w 0, h'.1, ?_⟩)
    rw [tCz]
    exact congrArg (tPt TTag.cz)
      (tuple₂_ext (by simp) (by simp [hbot (w 1) h'.2])).symm
  | gz s =>
    refine Or.inr (Or.inr ⟨s, w 0, w 1, by simpa [tdmInterp, zElF] using h, ?_⟩)
    rw [tGz]
    exact congrArg (tPt (TTag.gz s)) (tuple₂_ext (by simp) (by simp)).symm
  | tip s σ => exact absurd h (by simp [tdmInterp, zElF])
  | av s => exact absurd h (by simp [tdmInterp, zElF])
  | cy => exact absurd h (by simp [tdmInterp, zElF])
  | gy s => exact absurd h (by simp [tdmInterp, zElF])

end Classes

/-! ### The triples -/

section Triples

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The triple of the truth-setting gadget that frees the `false`-tip. -/
theorem tsTrip_wheelT {s : Bool} {x c : A} (h : OccIn c x s) :
    TSTrip (tTip s true x c) (tAv s x c) (tBv s x c) := by
  rw [TSTrip, tTip, tAv, tBv, tPt, tPt, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, tripF, h]

/-- The triple of the truth-setting gadget that frees the `true`-tip: it
carries the `Y`-element of the *next* occurrence of the variable. -/
theorem tsTrip_wheelF {s t : Bool} {x c c' : A} (h : VarNext x c s c' t) :
    TSTrip (tTip s false x c) (tAv t x c') (tBv s x c) := by
  rw [TSTrip, tTip, tAv, tBv, tPt, tPt, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, tripF, h]

/-- The triple of a clause, hanging on the tip of one of its occurrences. -/
theorem tsTrip_clause {a₀ : A} (ha₀ : IsBot a₀) {s : Bool} {x c : A} (h : OccIn c x s) :
    TSTrip (tTip s (!s) x c) (tCy a₀ c) (tCz a₀ c) := by
  rw [TSTrip, tTip, tCy, tCz, tPt, tPt, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, tripF, h, ha₀]

/-- A garbage triple: any tip together with any garbage pair. -/
theorem tsTrip_garbage {s σ t : Bool} {x c x' c' : A} (h : OccIn c x s)
    (h' : Chained c' x' t) : TSTrip (tTip s σ x c) (tGy t x' c') (tGz t x' c') := by
  rw [TSTrip, tTip, tGy, tGz, tPt, tPt, tPt, FOInterpretation.relMap_map]
  simp [tdmInterp, tripF, h, h']

/-- **What can cover a `b`-element**: only the two triples of the
truth-setting gadget of its own occurrence. -/
theorem tsTrip_bv_inv {s : Bool} {x c : A} {p q : tdmInterp.Map A}
    (h : TSTrip p q (tBv s x c)) :
    (p = tTip s true x c ∧ q = tAv s x c ∧ OccIn c x s) ∨
      ∃ c' t, VarNext x c s c' t ∧ p = tTip s false x c ∧ q = tAv t x c' := by
  obtain ⟨tp, wp, rfl⟩ := tPt_surj p
  obtain ⟨tq, wq, rfl⟩ := tPt_surj q
  rw [TSTrip, tBv, tPt, tPt, tPt, FOInterpretation.relMap_map] at h
  cases tp with
  | tip sp σp =>
    cases tq with
    | av t' =>
      by_cases hσ : σp = true
      · subst hσ
        by_cases hc : sp = t' ∧ sp = s
        · obtain ⟨rfl, rfl⟩ := hc
          have h' : OccIn (wp 1) (wp 0) sp ∧ wq 0 = wp 0 ∧ wq 1 = wp 1 ∧ x = wp 0 ∧ c = wp 1 := by
            simpa [tdmInterp, tripF, and_assoc] using h
          obtain ⟨hocc, h1, h2, h3, h4⟩ := h'
          subst h3
          subst h4
          refine Or.inl ⟨?_, ?_, hocc⟩
          · rw [tTip]
            exact congrArg (tPt (TTag.tip sp true)) (tuple₂_ext (by simp) (by simp))
          · rw [tAv]
            exact congrArg (tPt (TTag.av sp)) (tuple₂_ext (by simp [h1]) (by simp [h2]))
        · exact absurd h (by simp [tdmInterp, tripF, hc])
      · have hσ' : σp = false := by
          cases σp
          exacts [rfl, absurd rfl hσ]
        subst hσ'
        by_cases hc : sp = s
        · subst hc
          have h' : VarNext (wp 0) (wp 1) sp (wq 1) t' ∧ wq 0 = wp 0 ∧ x = wp 0 ∧ c = wp 1 := by
            simpa [tdmInterp, tripF, and_assoc] using h
          obtain ⟨hnext, h1, h2, h3⟩ := h'
          subst h2
          subst h3
          refine Or.inr ⟨wq 1, t', hnext, ?_, ?_⟩
          · rw [tTip]
            exact congrArg (tPt (TTag.tip sp false)) (tuple₂_ext (by simp) (by simp))
          · rw [tAv]
            exact congrArg (tPt (TTag.av t')) (tuple₂_ext (by simp [h1]) (by simp))
        · exact absurd h (by simp [tdmInterp, tripF, hc])
    | tip _ _ => exact absurd h (by simp [tdmInterp, tripF])
    | bv _ => exact absurd h (by simp [tdmInterp, tripF])
    | cy => exact absurd h (by simp [tdmInterp, tripF])
    | cz => exact absurd h (by simp [tdmInterp, tripF])
    | gy _ => exact absurd h (by simp [tdmInterp, tripF])
    | gz _ => exact absurd h (by simp [tdmInterp, tripF])
  | av _ => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])
  | bv _ => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])
  | cy => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])
  | cz => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])
  | gy _ => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])
  | gz _ => cases tq <;> exact absurd h (by simp [tdmInterp, tripF])

/-- **What can cover an `a`-element**: the gadget triple of its own
occurrence, or the one of the occurrence *before* it. -/
theorem tsTrip_av_inv {s : Bool} {x c : A} {p r : tdmInterp.Map A}
    (h : TSTrip p (tAv s x c) r) :
    (p = tTip s true x c ∧ r = tBv s x c ∧ OccIn c x s) ∨
      ∃ c₀ s₀, VarNext x c₀ s₀ c s ∧ p = tTip s₀ false x c₀ ∧ r = tBv s₀ x c₀ := by
  obtain ⟨tp, wp, rfl⟩ := tPt_surj p
  obtain ⟨tr, wr, rfl⟩ := tPt_surj r
  rw [TSTrip, tAv, tPt, tPt, tPt, FOInterpretation.relMap_map] at h
  cases tp with
  | tip sp σp =>
    cases tr with
    | bv u =>
      by_cases hσ : σp = true
      · subst hσ
        by_cases hc : sp = s ∧ sp = u
        · obtain ⟨rfl, rfl⟩ := hc
          have h' : OccIn (wp 1) (wp 0) sp ∧ x = wp 0 ∧ c = wp 1 ∧ wr 0 = wp 0 ∧ wr 1 = wp 1 := by
            simpa [tdmInterp, tripF, and_assoc] using h
          obtain ⟨hocc, h1, h2, h3, h4⟩ := h'
          subst h1
          subst h2
          refine Or.inl ⟨?_, ?_, hocc⟩
          · rw [tTip]
            exact congrArg (tPt (TTag.tip sp true)) (tuple₂_ext (by simp) (by simp))
          · rw [tBv]
            exact congrArg (tPt (TTag.bv sp)) (tuple₂_ext (by simp [h3]) (by simp [h4]))
        · exact absurd h (by simp [tdmInterp, tripF, hc])
      · have hσ' : σp = false := by
          cases σp
          exacts [rfl, absurd rfl hσ]
        subst hσ'
        by_cases hc : sp = u
        · subst hc
          have h' : VarNext (wp 0) (wp 1) sp c s ∧ x = wp 0 ∧ wr 0 = wp 0 ∧ wr 1 = wp 1 := by
            simpa [tdmInterp, tripF, and_assoc] using h
          obtain ⟨hnext, h1, h2, h3⟩ := h'
          subst h1
          refine Or.inr ⟨wp 1, sp, hnext, ?_, ?_⟩
          · rw [tTip]
            exact congrArg (tPt (TTag.tip sp false)) (tuple₂_ext (by simp) (by simp))
          · rw [tBv]
            exact congrArg (tPt (TTag.bv sp)) (tuple₂_ext (by simp [h2]) (by simp [h3]))
        · exact absurd h (by simp [tdmInterp, tripF, hc])
    | tip _ _ => exact absurd h (by simp [tdmInterp, tripF])
    | av _ => exact absurd h (by simp [tdmInterp, tripF])
    | cy => exact absurd h (by simp [tdmInterp, tripF])
    | cz => exact absurd h (by simp [tdmInterp, tripF])
    | gy _ => exact absurd h (by simp [tdmInterp, tripF])
    | gz _ => exact absurd h (by simp [tdmInterp, tripF])
  | av _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | bv _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | cy => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | cz => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | gy _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | gz _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])

/-- **What can cover the `Y`-element of a clause**: only a triple hanging on
the tip of one of its occurrences. -/
theorem tsTrip_cy_inv {a₀ : A} (ha₀ : IsBot a₀) {c : A} {p r : tdmInterp.Map A}
    (h : TSTrip p (tCy a₀ c) r) :
    ∃ x s, OccIn c x s ∧ p = tTip s (!s) x c ∧ r = tCz a₀ c := by
  obtain ⟨tp, wp, rfl⟩ := tPt_surj p
  obtain ⟨tr, wr, rfl⟩ := tPt_surj r
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  rw [TSTrip, tCy, tPt, tPt, tPt, FOInterpretation.relMap_map] at h
  cases tp with
  | tip sp σp =>
    cases tr with
    | cz =>
      by_cases hσ : σp = !sp
      · subst hσ
        have h' : OccIn (wp 1) (wp 0) sp ∧ c = wp 1 ∧ IsBot a₀ ∧ wr 0 = wp 1 ∧ IsBot (wr 1) := by
          simpa [tdmInterp, tripF, and_assoc] using h
        obtain ⟨hocc, h1, -, h3, h4⟩ := h'
        subst h1
        refine ⟨wp 0, sp, hocc, ?_, ?_⟩
        · rw [tTip]
          exact congrArg (tPt (TTag.tip sp (!sp))) (tuple₂_ext (by simp) (by simp))
        · rw [tCz]
          exact congrArg (tPt TTag.cz) (tuple₂_ext (by simp [h3]) (by simp [hbot (wr 1) h4]))
      · exact absurd h (by simp [tdmInterp, tripF, hσ])
    | tip _ _ => exact absurd h (by simp [tdmInterp, tripF])
    | av _ => exact absurd h (by simp [tdmInterp, tripF])
    | bv _ => exact absurd h (by simp [tdmInterp, tripF])
    | cy => exact absurd h (by simp [tdmInterp, tripF])
    | gy _ => exact absurd h (by simp [tdmInterp, tripF])
    | gz _ => exact absurd h (by simp [tdmInterp, tripF])
  | av _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | bv _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | cy => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | cz => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | gy _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])
  | gz _ => cases tr <;> exact absurd h (by simp [tdmInterp, tripF])

end Triples

/-! ### From a matching to an assignment -/

section Reverse

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The truth-setting gadget of `x` uses, at the occurrence `(c, s)`, the
triple that frees the `false`-tip. -/
def WheelTrue (M : tdmInterp.Map A → tdmInterp.Map A → tdmInterp.Map A → Prop)
    (x c : A) (s : Bool) : Prop :=
  M (tTip s true x c) (tAv s x c) (tBv s x c)

variable {a₀ : A} {M : tdmInterp.Map A → tdmInterp.Map A → tdmInterp.Map A → Prop}
  (hM : IsMatchingOn (TSXEl (A := tdmInterp.Map A)) TSYEl TSZEl TSTrip M)

include hM

omit [Finite A] in
/-- **One triple per occurrence**: the gadget of `x` either frees the
`false`-tip of `(c, s)` or the `true` one. -/
theorem wheel_other {x c : A} {s : Bool} (hocc : OccIn c x s) (hn : ¬WheelTrue M x c s) :
    ∃ c' t, VarNext x c s c' t ∧ M (tTip s false x c) (tAv t x c') (tBv s x c) := by
  obtain ⟨p, q, hpq⟩ := hM.2.2.2.1 (tBv s x c) ((tsZ_bv s x c).mpr hocc)
  rcases tsTrip_bv_inv (hM.1 _ _ _ hpq).1 with ⟨rfl, rfl, -⟩ | ⟨c', t, hnext, rfl, rfl⟩
  · exact absurd hpq hn
  · exact ⟨c', t, hnext, hpq⟩

omit [Finite A] in
/-- **The gadget is consistent**: neighbouring occurrences of a variable make
the same choice. -/
theorem wheel_step {x c₀ c : A} {s₀ s : Bool} (hnext : VarNext x c₀ s₀ c s) :
    (WheelTrue M x c s ↔ WheelTrue M x c₀ s₀) := by
  obtain ⟨p, r, hp⟩ := hM.2.2.1 (tAv s x c) ((tsY_av s x c).mpr hnext.occIn_right)
  rcases tsTrip_av_inv (hM.1 _ _ _ hp).1 with ⟨rfl, rfl, -⟩ | ⟨c₁, s₁, hnext₁, rfl, rfl⟩
  · refine ⟨fun _ => ?_, fun _ => hp⟩
    by_contra hn
    obtain ⟨c', t', hnext', hF⟩ := wheel_other hM hnext.occIn_left hn
    obtain ⟨rfl, rfl⟩ := varNext_right_unique hnext' hnext
    have heq := (hM.2.2.2.2.2.1 _ _ _ _ _ hp hF).1
    rw [tTip_eq_iff] at heq
    exact absurd heq.2.1 (by simp)
  · obtain ⟨rfl, rfl⟩ := varNext_left_unique hnext₁ hnext
    constructor
    · intro hT
      exfalso
      have heq := (hM.2.2.2.2.2.1 _ _ _ _ _ hT hp).1
      rw [tTip_eq_iff] at heq
      exact absurd heq.2.1 (by simp)
    · intro hT
      exfalso
      have heq := (hM.2.2.2.2.2.2 _ _ _ _ _ hT hp).1
      rw [tTip_eq_iff] at heq
      exact absurd heq.2.1 (by simp)

/-- **The gadget is a truth value**: all the occurrences of a variable make
the same choice, since the walk closes into a cycle. -/
theorem wheel_const {x c c' : A} {s s' : Bool} (hocc : OccIn c x s) (hocc' : OccIn c' x s') :
    (WheelTrue M x c s ↔ WheelTrue M x c' s') := by
  obtain ⟨cm, sm, hmin⟩ := exists_varMin ⟨c, s, hocc⟩
  have key : ∀ d : A, ∀ u : Bool, OccIn d x u → (WheelTrue M x d u ↔ WheelTrue M x cm sm) := by
    intro d₁ u₁ hd₁
    by_contra hP₁
    obtain ⟨d, u, hdu, hP, hmin'⟩ :=
      exists_minOccP (P := fun d u => ¬(WheelTrue M x d u ↔ WheelTrue M x cm sm))
        ⟨d₁, u₁, hd₁, hP₁⟩
    obtain ⟨d₀, u₀, hnext⟩ := exists_varPrev hdu
    have hstep := wheel_step hM hnext
    have hne : ¬(d = cm ∧ u = sm) := by
      rintro ⟨rfl, rfl⟩
      exact hP Iff.rfl
    have hlt : occLt d₀ u₀ d u := by
      rcases hnext with hstep' | ⟨-, hminD⟩
      · exact hstep'.2.2.1
      · exact absurd (varMin_unique hminD hmin) hne
    refine hmin' d₀ u₀ hnext.occIn_left (fun hiff => hP (hstep.trans hiff)) hlt
  exact (key c s hocc).trans (key c' s' hocc').symm

/-- The assignment a matching defines: a variable is true when its gadget
frees the `false`-tips. -/
def matchAssign (M : tdmInterp.Map A → tdmInterp.Map A → tdmInterp.Map A → Prop) (x : A) : Prop :=
  ∃ c s, OccIn c x s ∧ WheelTrue M x c s

theorem matchAssign_iff {x c : A} {s : Bool} (hocc : OccIn c x s) :
    matchAssign M x ↔ WheelTrue M x c s := by
  constructor
  · rintro ⟨c', s', hocc', hw⟩
    exact (wheel_const hM hocc' hocc).mp hw
  · intro hw
    exact ⟨c, s, hocc, hw⟩

/-- **A matching satisfies every clause**: covering the pair of a clause
takes the tip of one of its occurrences, and that tip is free exactly when the
literal is true. -/
theorem matchAssign_sat (ha₀ : IsBot a₀) {c : A} (hc : IsCl c) :
    ∃ x s, OccIn c x s ∧ LitTrue (matchAssign M) x s := by
  obtain ⟨p, r, hp⟩ := hM.2.2.1 (tCy a₀ c) ((tsY_cy ha₀ c).mpr hc)
  obtain ⟨x, s, hocc, rfl, rfl⟩ := tsTrip_cy_inv ha₀ (hM.1 _ _ _ hp).1
  refine ⟨x, s, hocc, ?_⟩
  by_cases hw : WheelTrue M x c s
  · have hs : s = true := by
      by_contra hs
      have hs' : s = false := by
        cases s
        exacts [rfl, absurd rfl hs]
      subst hs'
      have heq := (hM.2.2.2.2.1 _ _ _ _ _ hw hp).1
      exact absurd heq (by simp [tAv, tCy, tPt_eq_iff])
    subst hs
    exact (matchAssign_iff hM hocc).mpr hw
  · obtain ⟨c', t, -, hF⟩ := wheel_other hM hocc hw
    have hs : s = false := by
      by_contra hs
      have hs' : s = true := by
        cases s
        exacts [absurd rfl hs, rfl]
      subst hs'
      have heq := (hM.2.2.2.2.1 _ _ _ _ _ hF hp).1
      exact absurd heq (by simp [tAv, tCy, tPt_eq_iff])
    subst hs
    intro hν
    exact hw ((matchAssign_iff hM hocc).mp hν)

end Reverse

/-! ### From an assignment to a matching -/

section Forward

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- Where the garbage pair of an occurrence goes: to itself, unless it is the
first occurrence of its clause, which is sent to the occurrence the clause
gadget consumes. This is the bijection between the tips left over and the
garbage pairs. -/
def gbMap (ch fst : A → A × Bool) (c x : A) (s : Bool) : A × Bool :=
  if (x, s) = fst c then ch c else (x, s)

/-- The matching an assignment defines: the gadget triples of the side the
assignment picks, one triple per clause, and a garbage triple for every tip
left over. -/
def satMatch (a₀ : A) (β : A → Bool) (nxt : A × A × Bool → A × Bool) (ch fst : A → A × Bool) :
    tdmInterp.Map A → tdmInterp.Map A → tdmInterp.Map A → Prop := fun p q r =>
  (∃ x c s, OccIn c x s ∧ β x = true ∧
      p = tTip s true x c ∧ q = tAv s x c ∧ r = tBv s x c) ∨
    (∃ x c s, OccIn c x s ∧ β x = false ∧ p = tTip s false x c ∧
      q = tAv (nxt (x, c, s)).2 x (nxt (x, c, s)).1 ∧ r = tBv s x c) ∨
    (∃ c, IsCl c ∧ p = tTip (ch c).2 (!(ch c).2) (ch c).1 c ∧
      q = tCy a₀ c ∧ r = tCz a₀ c) ∨
    ∃ x c s, OccIn c x s ∧ (x, s) ≠ ch c ∧ p = tTip s (!β x) x c ∧
      q = tGy (gbMap ch fst c x s).2 (gbMap ch fst c x s).1 c ∧
      r = tGz (gbMap ch fst c x s).2 (gbMap ch fst c x s).1 c

variable {a₀ : A} {β : A → Bool} {nxt : A × A × Bool → A × Bool} {ch fst : A → A × Bool}
  (hnxt : ∀ x c s, OccIn c x s → VarNext x c s (nxt (x, c, s)).1 (nxt (x, c, s)).2)
  (hch : ∀ c, IsCl c → OccIn c (ch c).1 (ch c).2 ∧ β (ch c).1 = (ch c).2)
  (hfst : ∀ c : A, (∃ x s, OccIn c x s) → MinOcc c (fst c).1 (fst c).2)

include hch hfst

omit [Finite A] in
/-- The garbage pair an occurrence is sent to is a genuine one: a non-first
occurrence of its clause. -/
theorem gbMap_chained {c x : A} {s : Bool} (hocc : OccIn c x s) (hne : (x, s) ≠ ch c) :
    Chained c (gbMap ch fst c x s).1 (gbMap ch fst c x s).2 := by
  have hmin := hfst c ⟨x, s, hocc⟩
  rw [gbMap]
  by_cases hx : (x, s) = fst c
  · rw [if_pos hx]
    refine ⟨(hch c hocc.1).1, fun hminc => ?_⟩
    have h1 : ch c = fst c := by simpa using minOcc_unique hminc hmin
    exact hne (hx.trans h1.symm)
  · rw [if_neg hx]
    refine ⟨hocc, fun hminx => ?_⟩
    exact hx (by simpa using minOcc_unique hminx hmin)

omit [Finite A] [Language.sat.Structure A] hch hfst in
/-- The garbage map is injective on the tips left over. -/
theorem gbMap_inj {c x x' : A} {s s' : Bool} (hne : (x, s) ≠ ch c) (hne' : (x', s') ≠ ch c)
    (h : gbMap ch fst c x s = gbMap ch fst c x' s') : (x, s) = (x', s') := by
  rw [gbMap, gbMap] at h
  by_cases hx : (x, s) = fst c <;> by_cases hx' : (x', s') = fst c
  · rw [hx, hx']
  · rw [if_pos hx, if_neg hx'] at h
    exact absurd h.symm hne'
  · rw [if_neg hx, if_pos hx'] at h
    exact absurd h hne
  · rw [if_neg hx, if_neg hx'] at h
    exact h

omit [Finite A] hch in
/-- Every garbage pair is used: the map is onto the non-first occurrences. -/
theorem gbMap_surj {c x' : A} {s' : Bool} (hchained : Chained c x' s') :
    ∃ x s, OccIn c x s ∧ (x, s) ≠ ch c ∧ gbMap ch fst c x s = (x', s') := by
  have hmin := hfst c ⟨x', s', hchained.1⟩
  have hnefst : ((x', s') : A × Bool) ≠ fst c := by
    intro h
    refine hchained.2 ?_
    have h1 : x' = (fst c).1 := congrArg Prod.fst h
    have h2 : s' = (fst c).2 := congrArg Prod.snd h
    rw [h1, h2]
    exact hmin
  by_cases hc : ((x', s') : A × Bool) = ch c
  · refine ⟨(fst c).1, (fst c).2, hmin.1, ?_, ?_⟩
    · rw [← hc]
      exact fun h => hnefst h.symm
    · rw [gbMap, if_pos (by simp), ← hc]
  · exact ⟨x', s', hchained.1, hc, by rw [gbMap, if_neg hnefst]⟩

include hnxt

/-- **The construction is a matching**: every marked element is covered
exactly once. -/
theorem satMatch_isMatching (ha₀ : IsBot a₀) :
    IsMatchingOn (TSXEl (A := tdmInterp.Map A)) TSYEl TSZEl TSTrip
      (satMatch a₀ β nxt ch fst) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the triples are available ones, inside the three classes
  · rintro p q r (⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ |
      ⟨c, hc, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hne, rfl, rfl, rfl⟩)
    · exact ⟨tsTrip_wheelT hocc, (tsX_tip _ _ _ _).mpr hocc, (tsY_av _ _ _).mpr hocc,
        (tsZ_bv _ _ _).mpr hocc⟩
    · have hn := hnxt x c s hocc
      exact ⟨tsTrip_wheelF hn, (tsX_tip _ _ _ _).mpr hocc,
        (tsY_av _ _ _).mpr hn.occIn_right, (tsZ_bv _ _ _).mpr hocc⟩
    · obtain ⟨hocc, -⟩ := hch c hc
      exact ⟨tsTrip_clause ha₀ hocc, (tsX_tip _ _ _ _).mpr hocc,
        (tsY_cy ha₀ c).mpr hc, (tsZ_cz ha₀ c).mpr hc⟩
    · have hg := gbMap_chained hch hfst hocc hne
      exact ⟨tsTrip_garbage hocc hg, (tsX_tip _ _ _ _).mpr hocc,
        (tsY_gy _ _ _).mpr hg, (tsZ_gz _ _ _).mpr hg⟩
  -- every tip is covered
  · intro p hp
    obtain ⟨s, σ, x, c, hocc, rfl⟩ := tsX_shape hp
    by_cases hσ : σ = β x
    · subst hσ
      cases hb : β x with
      | true => exact ⟨_, _, Or.inl ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩⟩
      | false => exact ⟨_, _, Or.inr (Or.inl ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩)⟩
    · have hσ' : σ = !β x := by
        cases σ <;> cases hb : β x <;> simp_all
      subst hσ'
      by_cases hc : (x, s) = ch c
      · obtain ⟨hoccc, hbc⟩ := hch c hocc.1
        refine ⟨_, _, Or.inr (Or.inr (Or.inl ⟨c, hocc.1, ?_, rfl, rfl⟩))⟩
        rw [Prod.ext_iff] at hc
        rw [← hc.1, ← hc.2] at hbc ⊢
        rw [hbc]
      · exact ⟨_, _, Or.inr (Or.inr (Or.inr ⟨x, c, s, hocc, hc, rfl, rfl, rfl⟩))⟩
  -- every element of the second class is covered
  · intro q hq
    rcases tsY_shape ha₀ hq with ⟨s, x, c, hocc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨s, x, c, hg, rfl⟩
    · cases hb : β x with
      | true => exact ⟨_, _, Or.inl ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩⟩
      | false =>
        obtain ⟨c₀, s₀, hprev⟩ := exists_varPrev hocc
        have hn := hnxt x c₀ s₀ hprev.occIn_left
        obtain ⟨hc', ht'⟩ := varNext_right_unique hn hprev
        refine ⟨_, _, Or.inr (Or.inl ⟨x, c₀, s₀, hprev.occIn_left, hb, rfl, ?_, rfl⟩)⟩
        rw [hc', ht']
    · obtain ⟨hoccc, -⟩ := hch c hc
      exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨c, hc, rfl, rfl, rfl⟩))⟩
    · obtain ⟨x₀, s₀, hocc₀, hne₀, hgb⟩ := gbMap_surj hfst hg
      refine ⟨_, _, Or.inr (Or.inr (Or.inr ⟨x₀, c, s₀, hocc₀, hne₀, rfl, ?_, rfl⟩))⟩
      rw [hgb]
  -- every element of the third class is covered
  · intro r hr
    rcases tsZ_shape ha₀ hr with ⟨s, x, c, hocc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨s, x, c, hg, rfl⟩
    · cases hb : β x with
      | true => exact ⟨_, _, Or.inl ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩⟩
      | false => exact ⟨_, _, Or.inr (Or.inl ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩)⟩
    · obtain ⟨hoccc, -⟩ := hch c hc
      exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨c, hc, rfl, rfl, rfl⟩))⟩
    · obtain ⟨x₀, s₀, hocc₀, hne₀, hgb⟩ := gbMap_surj hfst hg
      refine ⟨tTip s₀ (!β x₀) x₀ c,
        tGy (gbMap ch fst c x₀ s₀).2 (gbMap ch fst c x₀ s₀).1 c,
        Or.inr (Or.inr (Or.inr ⟨x₀, c, s₀, hocc₀, hne₀, rfl, rfl, ?_⟩))⟩
      rw [hgb]
  -- no two triples share their first coordinate
  · rintro p q r q' r' (⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ |
      ⟨c, hc, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hne, rfl, rfl, rfl⟩) <;>
    rintro (⟨x', c', s', hocc', hb', hp', rfl, rfl⟩ | ⟨x', c', s', hocc', hb', hp', rfl, rfl⟩ |
      ⟨c'', hc'', hp', rfl, rfl⟩ | ⟨x', c', s', hocc', hne', hp', rfl, rfl⟩) <;>
    rw [tTip_eq_iff] at hp'
    · obtain ⟨rfl, -, rfl, rfl⟩ := hp'
      exact ⟨rfl, rfl⟩
    · exact absurd hp'.2.1 (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      obtain ⟨-, hbc⟩ := hch _ hc''
      rw [← hbc] at hσ
      rw [hb] at hσ
      exact absurd hσ (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      rw [hb] at hσ
      exact absurd hσ (by simp)
    · exact absurd hp'.2.1 (by simp)
    · obtain ⟨rfl, -, rfl, rfl⟩ := hp'
      exact ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      obtain ⟨-, hbc⟩ := hch _ hc''
      rw [← hbc] at hσ
      rw [hb] at hσ
      exact absurd hσ (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      rw [hb] at hσ
      exact absurd hσ (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      obtain ⟨-, hbc⟩ := hch c hc
      rw [← hbc] at hσ
      rw [hb'] at hσ
      exact absurd hσ (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      obtain ⟨-, hbc⟩ := hch c hc
      rw [← hbc] at hσ
      rw [hb'] at hσ
      exact absurd hσ (by simp)
    · obtain ⟨-, -, -, rfl⟩ := hp'
      exact ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨rfl, -, rfl, rfl⟩ := hp'
      exact hne' (Prod.ext rfl rfl)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      rw [hb'] at hσ
      exact absurd hσ.symm (by simp)
    · exfalso
      obtain ⟨rfl, hσ, rfl, rfl⟩ := hp'
      rw [hb'] at hσ
      exact absurd hσ.symm (by simp)
    · exfalso
      obtain ⟨rfl, -, rfl, rfl⟩ := hp'
      exact hne (Prod.ext rfl rfl)
    · obtain ⟨rfl, -, rfl, rfl⟩ := hp'
      exact ⟨rfl, rfl⟩
  -- no two triples share their second coordinate
  · rintro p q r p' r' (⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ |
      ⟨c, hc, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hne, rfl, rfl, rfl⟩) <;>
    rintro (⟨x', c', s', hocc', hb', rfl, hq', rfl⟩ | ⟨x', c', s', hocc', hb', rfl, hq', rfl⟩ |
      ⟨c'', hc'', rfl, hq', rfl⟩ | ⟨x', c', s', hocc', hne', rfl, hq', rfl⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := tAv_eq_iff.mp hq'
      exact ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨-, rfl, -⟩ := tAv_eq_iff.mp hq'
      rw [hb] at hb'
      exact absurd hb' (by simp)
    · exact absurd hq' (by simp [tAv, tCy, tPt_eq_iff])
    · exact absurd hq' (by simp [tAv, tGy, tPt_eq_iff])
    · exfalso
      obtain ⟨-, rfl, -⟩ := tAv_eq_iff.mp hq'
      rw [hb] at hb'
      exact absurd hb' (by simp)
    · obtain ⟨ht, rfl, hc'⟩ := tAv_eq_iff.mp hq'
      have hn := hnxt x c s hocc
      have hn' := hnxt x c' s' hocc'
      rw [← hc', ← ht] at hn'
      obtain ⟨rfl, rfl⟩ := varNext_left_unique hn hn'
      exact ⟨rfl, rfl⟩
    · exact absurd hq' (by simp [tAv, tCy, tPt_eq_iff])
    · exact absurd hq' (by simp [tAv, tGy, tPt_eq_iff])
    · exact absurd hq'.symm (by simp [tAv, tCy, tPt_eq_iff])
    · exact absurd hq'.symm (by simp [tAv, tCy, tPt_eq_iff])
    · obtain rfl := tCy_eq_iff.mp hq'
      exact ⟨rfl, rfl⟩
    · exact absurd hq' (by simp [tCy, tGy, tPt_eq_iff])
    · exact absurd hq'.symm (by simp [tAv, tGy, tPt_eq_iff])
    · exact absurd hq'.symm (by simp [tAv, tGy, tPt_eq_iff])
    · exact absurd hq'.symm (by simp [tCy, tGy, tPt_eq_iff])
    · obtain ⟨hs, hx, rfl⟩ := tGy_eq_iff.mp hq'
      have := gbMap_inj hne hne' (Prod.ext hx hs)
      rw [Prod.ext_iff] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨rfl, rfl⟩
  -- no two triples share their third coordinate
  · rintro p q r p' q' (⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hb, rfl, rfl, rfl⟩ |
      ⟨c, hc, rfl, rfl, rfl⟩ | ⟨x, c, s, hocc, hne, rfl, rfl, rfl⟩) <;>
    rintro (⟨x', c', s', hocc', hb', rfl, rfl, hr'⟩ | ⟨x', c', s', hocc', hb', rfl, rfl, hr'⟩ |
      ⟨c'', hc'', rfl, rfl, hr'⟩ | ⟨x', c', s', hocc', hne', rfl, rfl, hr'⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := tBv_eq_iff.mp hr'
      exact ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨-, rfl, -⟩ := tBv_eq_iff.mp hr'
      rw [hb] at hb'
      exact absurd hb' (by simp)
    · exact absurd hr' (by simp [tBv, tCz, tPt_eq_iff])
    · exact absurd hr' (by simp [tBv, tGz, tPt_eq_iff])
    · exfalso
      obtain ⟨-, rfl, -⟩ := tBv_eq_iff.mp hr'
      rw [hb] at hb'
      exact absurd hb' (by simp)
    · obtain ⟨rfl, rfl, rfl⟩ := tBv_eq_iff.mp hr'
      exact ⟨rfl, rfl⟩
    · exact absurd hr' (by simp [tBv, tCz, tPt_eq_iff])
    · exact absurd hr' (by simp [tBv, tGz, tPt_eq_iff])
    · exact absurd hr'.symm (by simp [tBv, tCz, tPt_eq_iff])
    · exact absurd hr'.symm (by simp [tBv, tCz, tPt_eq_iff])
    · obtain rfl := tCz_eq_iff.mp hr'
      exact ⟨rfl, rfl⟩
    · exact absurd hr' (by simp [tCz, tGz, tPt_eq_iff])
    · exact absurd hr'.symm (by simp [tBv, tGz, tPt_eq_iff])
    · exact absurd hr'.symm (by simp [tBv, tGz, tPt_eq_iff])
    · exact absurd hr'.symm (by simp [tCz, tGz, tPt_eq_iff])
    · obtain ⟨hs, hx, rfl⟩ := tGz_eq_iff.mp hr'
      have := gbMap_inj hne hne' (Prod.ext hx hs)
      rw [Prod.ext_iff] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨rfl, rfl⟩

end Forward

/-! ### Correctness of the reduction -/

section Correct

/-- **Correctness**: a CNF structure is satisfiable exactly when the
interpreted triple system has a matching. -/
theorem satisfiable_iff_hasThreeDimMatching (A : Type) [Language.sat.Structure A]
    [LinearOrder A] [Finite A] [Nonempty A] :
    Satisfiable A ↔ HasThreeDimMatching (tdmInterp.Map A) := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  haveI : Finite (tdmInterp.Map A) := tdmInterp.map_finite A
  constructor
  · rintro ⟨ν, hν⟩
    have hsat := satClauses_occ hν
    set β : A → Bool := fun x => if ν x then true else false with hβdef
    have hβ : ∀ (x : A) (s : Bool), LitTrue ν x s ↔ β x = s := by
      intro x s
      cases s <;> by_cases h : ν x <;> simp [hβdef, LitTrue, h]
    -- the successor of an occurrence, the true occurrence of a clause, and
    -- the first occurrence of a clause, all chosen once and for all
    have hn : ∀ p : A × A × Bool, ∃ q : A × Bool,
        OccIn p.2.1 p.1 p.2.2 → VarNext p.1 p.2.1 p.2.2 q.1 q.2 := by
      rintro ⟨x, c, s⟩
      by_cases h : OccIn c x s
      · obtain ⟨c', t, hnext⟩ := exists_varNext h
        exact ⟨(c', t), fun _ => hnext⟩
      · exact ⟨(c, s), fun h' => absurd h' h⟩
    choose nxt hnxt using hn
    have hc : ∀ c : A, ∃ p : A × Bool, IsCl c → OccIn c p.1 p.2 ∧ β p.1 = p.2 := by
      intro c
      by_cases h : IsCl c
      · obtain ⟨x, s, hocc, hT⟩ := hsat c h
        exact ⟨(x, s), fun _ => ⟨hocc, (hβ x s).mp hT⟩⟩
      · exact ⟨(c, false), fun h' => absurd h' h⟩
    choose ch hch using hc
    have hf : ∀ c : A, ∃ p : A × Bool, (∃ x s, OccIn c x s) → MinOcc c p.1 p.2 := by
      intro c
      by_cases h : ∃ x s, OccIn c x s
      · obtain ⟨x, s, hmin⟩ := exists_minOcc h
        exact ⟨(x, s), fun _ => hmin⟩
      · exact ⟨(c, false), fun h' => absurd h' h⟩
    choose fst hfst using hf
    exact ⟨inferInstance, satMatch a₀ β nxt ch fst,
      satMatch_isMatching (fun x c s h => hnxt (x, c, s) h) hch hfst ha₀⟩
  · rintro ⟨-, M, hM⟩
    refine ⟨matchAssign M, fun c hc => ?_⟩
    obtain ⟨x, s, hocc, hT⟩ := matchAssign_sat hM ha₀ hc
    cases s
    · exact ⟨x, Or.inr ⟨hocc.2, hT⟩⟩
    · exact ⟨x, Or.inl ⟨hocc.2, hT⟩⟩

end Correct

end TDMRed

open TDMRed in
/-- **SAT ordered-FO-reduces to 3-dimensional matching**: two tips, a `Y` and
a `Z` element per occurrence, a pair per clause, and a garbage pair per
non-first occurrence. The truth-setting gadget of a variable runs cyclically
through its occurrences, so it admits exactly two matchings – the variable's
two truth values – and the pair of a clause can only be covered through the
tip of a true literal. -/
noncomputable def sat_ordered_fo_reduction_threeDimMatching : SAT ≤ᶠᵒ[≤] ThreeDimMatching where
  Tag := TTag
  dim := 2
  toInterpretation := tdmInterp
  correct A _ _ _ _ := satisfiable_iff_hasThreeDimMatching A

end DescriptiveComplexity
