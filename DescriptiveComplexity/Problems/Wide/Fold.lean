/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Increment
import DescriptiveComplexity.Exponential.AltQuant

/-!
# Evaluating a quantifier prefix by one monotone sweep

The machine-free half of the sweep, and the reason a *nondeterministic* wide
machine can evaluate a first-order kernel at all: an alternating quantifier
prefix over a linearly ordered universe is the fold of its matrix along the
**lexicographic enumeration of its valuations**.

`DescriptiveComplexity.altQuantFrom` (`Exponential.AltQuant`) is the prefix, with
the state a machine would carry – a level `j` and a valuation `v`. What a machine
sweeping the valuations in order actually holds at each moment is not that value
but a **partial** one:

> `DescriptiveComplexity.foldFrom pol P le j v` is the value of the subtree at
> level `j`, with the coordinates below `j` fixed to those of `v`, computed over
> the leaves **up to `v`** and no further.

Four facts make it a sweep, and together they are what a program's correctness
proof will discharge.

| fact | theorem |
|---|---|
| at the last level the accumulator is the matrix | `DescriptiveComplexity.foldFrom_last` |
| at the **first** valuation it is the matrix | `DescriptiveComplexity.foldFrom_bot` |
| at the **last** valuation it is the whole prefix | `DescriptiveComplexity.foldFrom_top` |
| across one step it folds | `foldFrom_above`, `foldFrom_carry`, `foldFrom_below` |

The step splits by comparison with the **carry level** `c` – the last coordinate
that is not maximal, which the enumeration increments. Above `c` nothing changes
but the deeper accumulator; at `c` the accumulator absorbs the subtree just
completed and takes in the new leaf; below `c` the accumulators reset to the new
leaf. That is one `∨` (or `∧`) per level and one matrix evaluation per step –
`k` bits of control and no addressing, which is the whole point.

Everything is stated at an arbitrary order relation on the values, and the
successor is a *hypothesis* (`∀ a, WMLt le a b' ↔ le a b`) rather than a
construction, so this file is independent of the address layer; it is
`DescriptiveComplexity.wmSetLt_iff_of_wmIncr` that supplies the hypothesis when
the values are addresses.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### The partial value of a prefix -/

section Fold

variable {A : Type} {n : ℕ}

/-- The recursion of `DescriptiveComplexity.foldFrom`, with the same explicit
fuel as `DescriptiveComplexity.altQuantAux`: the number of levels left. -/
def foldAux (pol : ℕ → Bool) (P : (Fin n → A) → Prop) (le : A → A → Prop) :
    ℕ → ℕ → (Fin n → A) → Prop
  | 0, _, v => P v
  | r + 1, j, v =>
      if h : j < n then
        (if pol j = true then
            (∃ a : A, WMLt le a (v ⟨j, h⟩) ∧
              altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∨
              foldAux pol P le r (j + 1) v
          else
            (∀ a : A, WMLt le a (v ⟨j, h⟩) →
              altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∧
              foldAux pol P le r (j + 1) v)
      else P v

/-- **The partial value of a prefix**: the value of the subtree at level `j`,
with the coordinates below `j` read off `v`, computed over the valuations up to
`v` in the lexicographic order and no further. This is what a machine sweeping
the valuations holds in its control. -/
def foldFrom (pol : ℕ → Bool) (P : (Fin n → A) → Prop) (le : A → A → Prop) (j : ℕ)
    (v : Fin n → A) : Prop :=
  foldAux pol P le (n - j) j v

variable {pol : ℕ → Bool} {P : (Fin n → A) → Prop} {le : A → A → Prop}

/-- Past the last level the accumulator is the matrix. -/
theorem foldFrom_of_le {j : ℕ} (h : n ≤ j) (v : Fin n → A) :
    foldFrom pol P le j v = P v := by
  rw [foldFrom, show n - j = 0 from Nat.sub_eq_zero_of_le h]
  rfl

/-- At the last level the accumulator is the matrix. -/
theorem foldFrom_last (v : Fin n → A) : foldFrom pol P le n v = P v :=
  foldFrom_of_le le_rfl v

private theorem foldAux_succ {r j : ℕ} (h : j < n) (v : Fin n → A) :
    foldAux pol P le (r + 1) j v =
      (if pol j = true then
          (∃ a : A, WMLt le a (v ⟨j, h⟩) ∧
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∨
            foldAux pol P le r (j + 1) v
        else
          (∀ a : A, WMLt le a (v ⟨j, h⟩) →
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∧
            foldAux pol P le r (j + 1) v) := by
  rw [foldAux, dif_pos h]

/-- **One existential level of the accumulator.** -/
theorem foldFrom_ex {j : ℕ} (h : j < n) (hp : pol j = true) (v : Fin n → A) :
    foldFrom pol P le j v ↔
      ((∃ a : A, WMLt le a (v ⟨j, h⟩) ∧
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∨
          foldFrom pol P le (j + 1) v) := by
  rw [foldFrom, show n - j = (n - (j + 1)) + 1 by omega, foldAux_succ h, if_pos hp]
  rfl

/-- **One universal level of the accumulator.** -/
theorem foldFrom_all {j : ℕ} (h : j < n) (hp : pol j = false) (v : Fin n → A) :
    foldFrom pol P le j v ↔
      ((∀ a : A, WMLt le a (v ⟨j, h⟩) →
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)) ∧
          foldFrom pol P le (j + 1) v) := by
  rw [foldFrom, show n - j = (n - (j + 1)) + 1 by omega, foldAux_succ h,
    if_neg (by simp [hp])]
  rfl

/-! ### The two ends of the enumeration -/

/-- **At the first valuation the accumulator is the matrix**, at every level: no
leaf before it has been seen, so nothing has been accumulated yet. -/
theorem foldFrom_bot {v : Fin n → A} {j₀ : ℕ}
    (hbot : ∀ i : Fin n, j₀ ≤ (i : ℕ) → ∀ a : A, le (v i) a) {j : ℕ} (hj : j₀ ≤ j) :
    foldFrom pol P le j v ↔ P v := by
  have key : ∀ r j : ℕ, j₀ ≤ j → (foldAux pol P le r j v ↔ P v) := by
    intro r
    induction r with
    | zero => intro _ _; exact Iff.rfl
    | succ r ih =>
      intro j hj
      by_cases h : j < n
      · have hno : ∀ a : A, ¬WMLt le a (v ⟨j, h⟩) := fun a hlt =>
          hlt.2 (hbot ⟨j, h⟩ hj a)
        rw [foldAux_succ h]
        by_cases hp : pol j = true
        · rw [if_pos hp]
          refine ⟨fun hc => ?_, fun hc => Or.inr ((ih (j + 1) (by omega)).mpr hc)⟩
          rcases hc with ⟨a, hlt, -⟩ | hc
          · exact absurd hlt (hno a)
          · exact (ih (j + 1) (by omega)).mp hc
        · rw [if_neg hp]
          exact ⟨fun hc => (ih (j + 1) (by omega)).mp hc.2,
            fun hc => ⟨fun a hlt => absurd hlt (hno a), (ih (j + 1) (by omega)).mpr hc⟩⟩
      · rw [foldAux, dif_neg h]
  exact key _ j hj

/-- **At the last valuation the accumulator is the whole prefix**: every leaf has
been seen, so the sweep has finished computing the value of the subtree. This is
the half that reads the answer off the machine when it reaches the end of its
tape. -/
theorem foldFrom_top {v : Fin n → A} {j₀ : ℕ} (h : IsLinOrd le)
    (htop : ∀ i : Fin n, j₀ ≤ (i : ℕ) → ∀ a : A, le a (v i)) {j : ℕ} (hj : j₀ ≤ j) :
    foldFrom pol P le j v ↔ altQuantFrom pol P j v := by
  -- Below the maximal value, “strictly below or equal to it” is “anything”.
  have hsplit : ∀ (i : Fin n), j₀ ≤ (i : ℕ) → ∀ Nn : A → Prop,
      ((∃ a : A, WMLt le a (v i) ∧ Nn a) ∨ Nn (v i)) ↔ ∃ a : A, Nn a := by
    intro i hi Nn
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rcases hc with ⟨a, -, ha⟩ | ha
      · exact ⟨a, ha⟩
      · exact ⟨v i, ha⟩
    · obtain ⟨a, ha⟩ := hc
      rcases eq_or_ne a (v i) with rfl | hne
      · exact Or.inr ha
      · exact Or.inl ⟨a, ⟨htop i hi a, fun hc' => hne (h.2.2.1 a _ (htop i hi a) hc')⟩, ha⟩
  have hsplit' : ∀ (i : Fin n), j₀ ≤ (i : ℕ) → ∀ Nn : A → Prop,
      ((∀ a : A, WMLt le a (v i) → Nn a) ∧ Nn (v i)) ↔ ∀ a : A, Nn a := by
    intro i hi Nn
    refine ⟨fun hc a => ?_, fun hc => ⟨fun a _ => hc a, hc _⟩⟩
    rcases eq_or_ne a (v i) with rfl | hne
    · exact hc.2
    · exact hc.1 a ⟨htop i hi a, fun hc' => hne (h.2.2.1 a _ (htop i hi a) hc')⟩
  have key : ∀ m j : ℕ, j₀ ≤ j → n - j = m →
      (foldFrom pol P le j v ↔ altQuantFrom pol P j v) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hj0 hm
      by_cases hjn : j < n
      · have hrec : foldFrom pol P le (j + 1) v ↔ altQuantFrom pol P (j + 1) v :=
          ih (n - (j + 1)) (by omega) (j + 1) (by omega) rfl
        have hmid : altQuantFrom pol P (j + 1) v =
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, hjn⟩ (v ⟨j, hjn⟩)) := by
          rw [Function.update_eq_self]
        by_cases hp : pol j = true
        · rw [foldFrom_ex hjn hp v, altQuantFrom_ex hjn hp v, hrec, hmid]
          exact hsplit ⟨j, hjn⟩ hj0 _
        · have hp' : pol j = false := by simpa using hp
          rw [foldFrom_all hjn hp' v, altQuantFrom_all hjn hp' v, hrec, hmid]
          exact hsplit' ⟨j, hjn⟩ hj0 _
      · rw [foldFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
  exact key _ j hj rfl

/-! ### One step of the enumeration

The three rules a program's step obligation splits into, by comparison with the
**carry level** – the last coordinate the enumeration increments. -/

/-- The contribution of a level to its accumulator depends only on the
coordinates up to that level, so above the carry it does not change. -/
theorem levelEx_congr {v v' : Fin n → A} {j : ℕ} (hj : j < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≤ j → v i = v' i) :
    ((∃ a : A, WMLt le a (v ⟨j, hj⟩) ∧
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a)) ↔
      ∃ a : A, WMLt le a (v' ⟨j, hj⟩) ∧
        altQuantFrom pol P (j + 1) (Function.update v' ⟨j, hj⟩ a)) := by
  have hupd : ∀ a : A, altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a) =
      altQuantFrom pol P (j + 1) (Function.update v' ⟨j, hj⟩ a) := by
    intro a
    refine altQuantFrom_congr_val _ _ fun i hi => ?_
    by_cases hij : i = ⟨j, hj⟩
    · rw [hij]
      simp
    · simp only [Function.update_apply, if_neg hij]
      exact hagree i (by have := i.isLt; omega)
  rw [hagree ⟨j, hj⟩ le_rfl]
  exact exists_congr fun a => and_congr Iff.rfl (iff_of_eq (hupd a))

/-- The universal reading of `DescriptiveComplexity.levelEx_congr`. -/
theorem levelAll_congr {v v' : Fin n → A} {j : ℕ} (hj : j < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≤ j → v i = v' i) :
    ((∀ a : A, WMLt le a (v ⟨j, hj⟩) →
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a)) ↔
      ∀ a : A, WMLt le a (v' ⟨j, hj⟩) →
        altQuantFrom pol P (j + 1) (Function.update v' ⟨j, hj⟩ a)) := by
  have hupd : ∀ a : A, altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a) =
      altQuantFrom pol P (j + 1) (Function.update v' ⟨j, hj⟩ a) := by
    intro a
    refine altQuantFrom_congr_val _ _ fun i hi => ?_
    by_cases hij : i = ⟨j, hj⟩
    · rw [hij]
      simp
    · simp only [Function.update_apply, if_neg hij]
      exact hagree i (by have := i.isLt; omega)
  rw [hagree ⟨j, hj⟩ le_rfl]
  exact forall_congr' fun a => imp_congr Iff.rfl (iff_of_eq (hupd a))

/-- **Above the carry the accumulator only changes through the deeper one**: the
level's own contribution is untouched, because the coordinates up to it are. -/
theorem foldFrom_above {v v' : Fin n → A} {j : ℕ} (hj : j < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≤ j → v i = v' i) :
    (foldFrom pol P le j v' ↔
      (if pol j = true then
          (∃ a : A, WMLt le a (v ⟨j, hj⟩) ∧
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a)) ∨
            foldFrom pol P le (j + 1) v'
        else
          (∀ a : A, WMLt le a (v ⟨j, hj⟩) →
            altQuantFrom pol P (j + 1) (Function.update v ⟨j, hj⟩ a)) ∧
            foldFrom pol P le (j + 1) v')) := by
  by_cases hp : pol j = true
  · rw [if_pos hp, foldFrom_ex hj hp v']
    exact or_congr (levelEx_congr hj hagree).symm Iff.rfl
  · have hp' : pol j = false := by simpa using hp
    rw [if_neg hp, foldFrom_all hj hp' v']
    exact and_congr (levelAll_congr hj hagree).symm Iff.rfl

/-- **At the carry level the accumulator absorbs the subtree just completed.**
The new accumulator is the old one – which, every deeper coordinate having been
maximal, was the whole subtree up to and including the old value – combined with
the accumulator one level deeper, which by
`DescriptiveComplexity.foldFrom_bot` is the new leaf. This is the fold, and the
only place the successor is used. -/
theorem foldFrom_carry {v v' : Fin n → A} {c : ℕ} (h : IsLinOrd le) (hc : c < n)
    (hagree : ∀ i : Fin n, (i : ℕ) < c → v i = v' i)
    (htop : ∀ i : Fin n, c < (i : ℕ) → ∀ a : A, le a (v i))
    (hsucc : ∀ a : A, WMLt le a (v' ⟨c, hc⟩) ↔ le a (v ⟨c, hc⟩)) :
    (foldFrom pol P le c v' ↔
      (if pol c = true then foldFrom pol P le c v ∨ foldFrom pol P le (c + 1) v'
        else foldFrom pol P le c v ∧ foldFrom pol P le (c + 1) v')) := by
  -- The old accumulator at the carry level is the subtree over the values `≤ v c`.
  have hupd : ∀ a : A, altQuantFrom pol P (c + 1) (Function.update v' ⟨c, hc⟩ a) =
      altQuantFrom pol P (c + 1) (Function.update v ⟨c, hc⟩ a) := by
    intro a
    refine altQuantFrom_congr_val _ _ fun i hi => ?_
    by_cases hic : i = ⟨c, hc⟩
    · rw [hic]
      simp
    · have hne' : (i : ℕ) ≠ c := fun hcon => hic (Fin.ext hcon)
      simp only [Function.update_apply, if_neg hic]
      exact (hagree i (by omega)).symm
  have hmid : altQuantFrom pol P (c + 1) v =
      altQuantFrom pol P (c + 1) (Function.update v ⟨c, hc⟩ (v ⟨c, hc⟩)) := by
    rw [Function.update_eq_self]
  have hdeep : foldFrom pol P le (c + 1) v ↔ altQuantFrom pol P (c + 1) v :=
    foldFrom_top (j₀ := c + 1) h (fun i hi a => htop i (by omega) a) le_rfl
  have hle_iff : ∀ (a : A) (Nn : A → Prop),
      (le a (v ⟨c, hc⟩) ∧ Nn a) ↔ ((WMLt le a (v ⟨c, hc⟩) ∧ Nn a) ∨ (a = v ⟨c, hc⟩ ∧ Nn a)) := by
    intro a Nn
    constructor
    · rintro ⟨hla, hna⟩
      rcases eq_or_ne a (v ⟨c, hc⟩) with rfl | hne
      · exact Or.inr ⟨rfl, hna⟩
      · exact Or.inl ⟨⟨hla, fun hcon => hne (h.2.2.1 a _ hla hcon)⟩, hna⟩
    · rintro (⟨hlt, hna⟩ | ⟨rfl, hna⟩)
      · exact ⟨hlt.1, hna⟩
      · exact ⟨h.1 _, hna⟩
  by_cases hp : pol c = true
  · rw [if_pos hp, foldFrom_ex hc hp v', foldFrom_ex hc hp v, hdeep, hmid]
    refine or_congr ?_ Iff.rfl
    have h1 : (∃ a : A, WMLt le a (v' ⟨c, hc⟩) ∧
          altQuantFrom pol P (c + 1) (Function.update v' ⟨c, hc⟩ a)) ↔
        ∃ a : A, le a (v ⟨c, hc⟩) ∧
          altQuantFrom pol P (c + 1) (Function.update v ⟨c, hc⟩ a) :=
      exists_congr fun a => and_congr (hsucc a) (iff_of_eq (hupd a))
    refine h1.trans ?_
    refine (exists_congr fun a => hle_iff a
      (fun b => altQuantFrom pol P (c + 1) (Function.update v ⟨c, hc⟩ b))).trans ?_
    rw [exists_or]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨a, ha, hna⟩
      exact ha ▸ hna
    · intro hn
      exact ⟨_, rfl, hn⟩
  · have hp' : pol c = false := by simpa using hp
    rw [if_neg hp, foldFrom_all hc hp' v', foldFrom_all hc hp' v, hdeep, hmid]
    refine and_congr ?_ Iff.rfl
    refine (forall_congr' fun a => imp_congr (hsucc a) (iff_of_eq (hupd a))).trans ?_
    constructor
    · intro hall
      refine ⟨fun a hlt => hall a hlt.1, hall _ (h.1 _)⟩
    · rintro ⟨hlt, hat⟩ a hla
      rcases eq_or_ne a (v ⟨c, hc⟩) with rfl | hne
      · exact hat
      · exact hlt a ⟨hla, fun hcon => hne (h.2.2.1 a _ hla hcon)⟩

/-- **Below the carry the accumulators reset to the new leaf**, by
`DescriptiveComplexity.foldFrom_bot`: every coordinate below the carry is minimal
in the incremented valuation. -/
theorem foldFrom_below {v' : Fin n → A} {c j : ℕ}
    (hbot : ∀ i : Fin n, c < (i : ℕ) → ∀ a : A, le (v' i) a) (hj : c < j) :
    foldFrom pol P le j v' ↔ P v' :=
  foldFrom_bot (j₀ := c + 1) (fun i hi a => hbot i (by omega) a) (by omega)

end Fold

end DescriptiveComplexity
