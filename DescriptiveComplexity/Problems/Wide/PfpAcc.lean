/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Fold

/-!
# What the control carries: contributions, not fold values

A design correction, found by writing the update rule down. The sweep's
control cannot carry the *fold values* `DescriptiveComplexity.foldFrom j v`:
at a step whose carry is `c`, the new value at a level `j < c` is the level's
own contribution combined with the deeper value – and the contribution is not
recoverable from the two old values (`x = C ∨ y` does not determine `C`). What
is closed under the update is the family of **contributions** themselves:

* `DescriptiveComplexity.Pfp.accCVal j v` – the completed-subtree contribution
  at level `j`: the disjunction (existential polarity) or conjunction
  (universal) over the values strictly below the current coordinate;
* `DescriptiveComplexity.Pfp.foldFrom_eq_accCVal` – the fold value at a level
  is the contribution combined with the deeper fold value, so any fold value
  is a finite Boolean **chain** of the contributions and the current leaf
  (`DescriptiveComplexity.foldFrom_last`), which a rule's guard can spell out;
* the three update rules along an increment with carry `c`:
  `DescriptiveComplexity.Pfp.accCVal_congr_above` (levels before the carry are
  untouched), `DescriptiveComplexity.Pfp.accCVal_carry` (the carry level
  absorbs the completed subtree, which is the deeper *chain* at the old
  valuation), and `DescriptiveComplexity.Pfp.accCVal_reset` (levels after the
  carry reset to the polarity's unit).

So the machine's payload holds one bit per level – the contribution – plus the
last leaf, and every verdict it ever needs is a chain of those bits.
-/

namespace DescriptiveComplexity

namespace Pfp

section Acc

variable {A : Type} {n : ℕ} (pol : ℕ → Bool) (P : (Fin n → A) → Prop) (le : A → A → Prop)

open Classical in
/-- **The completed-subtree contribution at a level**: what the enumeration has
finished below the current coordinate – a disjunction of subtrees under an
existential polarity, a conjunction under a universal one. Past the last level
it is the polarity's unit. -/
noncomputable def accCVal (j : ℕ) (v : Fin n → A) : Prop :=
  if h : j < n then
    (if pol j = true then
      ∃ a : A, WMLt le a (v ⟨j, h⟩) ∧ altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a)
    else
      ∀ a : A, WMLt le a (v ⟨j, h⟩) → altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a))
  else (pol j = false)

variable {pol P le}

theorem accCVal_of_lt {j : ℕ} (h : j < n) (hp : pol j = true) (v : Fin n → A) :
    accCVal pol P le j v ↔
      ∃ a : A, WMLt le a (v ⟨j, h⟩) ∧
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a) := by
  rw [accCVal, dif_pos h, if_pos hp]

theorem accCVal_of_lt_all {j : ℕ} (h : j < n) (hp : pol j = false) (v : Fin n → A) :
    accCVal pol P le j v ↔
      ∀ a : A, WMLt le a (v ⟨j, h⟩) →
        altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a) := by
  rw [accCVal, dif_pos h, if_neg (by simp [hp])]

/-- **The fold value is the contribution combined with the deeper value** –
`DescriptiveComplexity.foldFrom_ex` / `foldFrom_all` read through the
contribution. Iterated down to `DescriptiveComplexity.foldFrom_last`, any fold
value is a finite Boolean chain of the contributions and the leaf. -/
theorem foldFrom_eq_accCVal {j : ℕ} (h : j < n) (v : Fin n → A) :
    foldFrom pol P le j v ↔
      (if pol j = true then accCVal pol P le j v ∨ foldFrom pol P le (j + 1) v
        else accCVal pol P le j v ∧ foldFrom pol P le (j + 1) v) := by
  by_cases hp : pol j = true
  · rw [if_pos hp, foldFrom_ex h hp, accCVal_of_lt h hp]
  · have hp' : pol j = false := by simpa using hp
    rw [if_neg hp, foldFrom_all h hp', accCVal_of_lt_all h hp']

/-! ### The three update rules along an increment -/

/-- **Levels before the carry are untouched**: their coordinate and everything
above it agree across the step. -/
theorem accCVal_congr_above {v v' : Fin n → A} {j : ℕ} (h : j < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≤ j → v i = v' i) :
    accCVal pol P le j v' ↔ accCVal pol P le j v := by
  by_cases hp : pol j = true
  · rw [accCVal_of_lt h hp, accCVal_of_lt h hp]
    exact (levelEx_congr h hagree).symm
  · have hp' : pol j = false := by simpa using hp
    rw [accCVal_of_lt_all h hp', accCVal_of_lt_all h hp']
    exact (levelAll_congr h hagree).symm

/-- **Levels after the carry reset to the polarity's unit**: nothing lies
strictly below a minimal coordinate. -/
theorem accCVal_reset {v' : Fin n → A} {j : ℕ} (h : j < n)
    (hbot : ∀ a : A, le (v' ⟨j, h⟩) a) :
    accCVal pol P le j v' ↔ (pol j = false) := by
  have hno : ∀ a : A, ¬WMLt le a (v' ⟨j, h⟩) := fun a hlt => hlt.2 (hbot a)
  by_cases hp : pol j = true
  · rw [accCVal_of_lt h hp]
    exact iff_of_false (fun hc => hc.elim fun a hab => hno a hab.1) (by simp [hp])
  · have hp' : pol j = false := by simpa using hp
    rw [accCVal_of_lt_all h hp']
    exact iff_of_true (fun a hlt => absurd hlt (hno a)) hp'

/-- **The carry level absorbs the completed subtree**: the new contribution is
the old one together with the deeper fold value at the *old* valuation – which
the machine has as a chain of its stored bits and the old leaf. -/
theorem accCVal_carry (h : IsLinOrd le) {v v' : Fin n → A} {c : ℕ} (hc : c < n)
    (hagree : ∀ i : Fin n, (i : ℕ) < c → v i = v' i)
    (htop : ∀ i : Fin n, c < (i : ℕ) → ∀ a : A, le a (v i))
    (hsucc : ∀ a : A, WMLt le a (v' ⟨c, hc⟩) ↔ le a (v ⟨c, hc⟩)) :
    accCVal pol P le c v' ↔
      (if pol c = true then accCVal pol P le c v ∨ foldFrom pol P le (c + 1) v
        else accCVal pol P le c v ∧ foldFrom pol P le (c + 1) v) := by
  -- updating `v'` at the carry is updating `v` there: only earlier coordinates matter
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
      (le a (v ⟨c, hc⟩) ∧ Nn a) ↔
        ((WMLt le a (v ⟨c, hc⟩) ∧ Nn a) ∨ (a = v ⟨c, hc⟩ ∧ Nn a)) := by
    intro a Nn
    constructor
    · rintro ⟨hla, hna⟩
      rcases eq_or_ne a (v ⟨c, hc⟩) with rfl | hne
      · exact Or.inr ⟨rfl, hna⟩
      · exact Or.inl ⟨⟨hla, fun hc' => hne (h.2.2.1 a _ hla hc')⟩, hna⟩
    · rintro (⟨hlt, hna⟩ | ⟨rfl, hna⟩)
      · exact ⟨hlt.1, hna⟩
      · exact ⟨h.1 _, hna⟩
  by_cases hp : pol c = true
  · rw [if_pos hp, accCVal_of_lt hc hp, accCVal_of_lt hc hp, hdeep, hmid]
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
    rw [if_neg hp, accCVal_of_lt_all hc hp', accCVal_of_lt_all hc hp', hdeep, hmid]
    refine (forall_congr' fun a => imp_congr (hsucc a) (iff_of_eq (hupd a))).trans ?_
    constructor
    · intro hall
      refine ⟨fun a hlt => hall a hlt.1, hall _ (h.1 _)⟩
    · rintro ⟨hlt, hat⟩ a hla
      rcases eq_or_ne a (v ⟨c, hc⟩) with rfl | hne
      · exact hat
      · exact hlt a ⟨hla, fun hc' => hne (h.2.2.1 a _ hla hc')⟩

end Acc

/-! ### The vector the control carries, and its update

What the machine holds is one **bit per level** – the contribution – plus the
value of the last leaf. Two operations turn that into everything it needs: a
fold value is the *chain* of the stored bits from a level down, closed by the
leaf (`DescriptiveComplexity.Pfp.chainFrom`, correct by
`chainFrom_iff_foldFrom`), and one round of the enumeration rewrites the
vector by the three rules above (`accCVal_step`: untouched before the carry,
absorbing at it, reset after it). A rule's `dstSt` spells out the first and
its guard the second; nothing else about the fold ever reaches the
program. -/

section Vector

variable {A : Type} {n : ℕ} {pol : ℕ → Bool} {P : (Fin n → A) → Prop} {le : A → A → Prop}

/-- The chain, with an explicit fuel so that the recursion is structural. -/
def chainAux (pol : ℕ → Bool) (acc : ℕ → Prop) (leaf : Prop) (n : ℕ) : ℕ → ℕ → Prop
  | 0, _ => leaf
  | r + 1, j =>
    if j < n then
      (if pol j = true then acc j ∨ chainAux pol acc leaf n r (j + 1)
        else acc j ∧ chainAux pol acc leaf n r (j + 1))
    else leaf

/-- **A fold value as the machine holds it**: the chain of the stored
contributions from a level down, closed by the last leaf. -/
def chainFrom (pol : ℕ → Bool) (acc : ℕ → Prop) (leaf : Prop) (n j : ℕ) : Prop :=
  chainAux pol acc leaf n (n - j) j

variable {acc acc' : ℕ → Prop} {leaf : Prop}

theorem chainFrom_of_le {j : ℕ} (h : n ≤ j) : chainFrom pol acc leaf n j = leaf := by
  rw [chainFrom, show n - j = 0 from Nat.sub_eq_zero_of_le h]
  rfl

theorem chainFrom_succ {j : ℕ} (h : j < n) :
    chainFrom pol acc leaf n j =
      (if pol j = true then acc j ∨ chainFrom pol acc leaf n (j + 1)
        else acc j ∧ chainFrom pol acc leaf n (j + 1)) := by
  rw [chainFrom, show n - j = (n - (j + 1)) + 1 by omega, chainAux, if_pos h]
  rfl

/-- **The chain is the fold value**: a control whose bits are the
contributions and whose leaf bit is the matrix at the current valuation reads
off every accumulator of the sweep. -/
theorem chainFrom_iff_foldFrom {v : Fin n → A}
    (hacc : ∀ i : ℕ, i < n → (acc i ↔ accCVal pol P le i v))
    (hleaf : leaf ↔ P v) (j : ℕ) :
    chainFrom pol acc leaf n j ↔ foldFrom pol P le j v := by
  have key : ∀ (r j : ℕ), n - j ≤ r →
      (chainFrom pol acc leaf n j ↔ foldFrom pol P le j v) := by
    intro r
    induction r with
    | zero =>
      intro j hr
      rw [chainFrom_of_le (by omega), foldFrom_of_le (by omega)]
      exact hleaf
    | succ r ih =>
      intro j hr
      by_cases hjn : j < n
      · rw [chainFrom_succ hjn, foldFrom_eq_accCVal hjn]
        by_cases hp : pol j = true
        · rw [if_pos hp, if_pos hp]
          exact or_congr (hacc j hjn) (ih (j + 1) (by omega))
        · rw [if_neg hp, if_neg hp]
          exact and_congr (hacc j hjn) (ih (j + 1) (by omega))
      · rw [chainFrom_of_le (by omega), foldFrom_of_le (by omega)]
        exact hleaf
  exact key _ j le_rfl

/-- **One round of the enumeration rewrites the vector**: the levels before
the carry keep their bit, the carry level absorbs the chain below it at the
old valuation, and the levels after it reset to the polarity's unit. This is
the whole content of the `dstSt` a landing rule carries. -/
theorem accCVal_step (h : IsLinOrd le) {v v' : Fin n → A} {c : ℕ} (hc : c < n)
    (hagree : ∀ i : Fin n, (i : ℕ) < c → v i = v' i)
    (htop : ∀ i : Fin n, c < (i : ℕ) → ∀ a : A, le a (v i))
    (hbot : ∀ i : Fin n, c < (i : ℕ) → ∀ a : A, le (v' i) a)
    (hsucc : ∀ a : A, WMLt le a (v' ⟨c, hc⟩) ↔ le a (v ⟨c, hc⟩))
    (hacc : ∀ i : ℕ, i < n → (acc i ↔ accCVal pol P le i v))
    (hleaf : leaf ↔ P v)
    (hnew : ∀ i : ℕ, i < n → (acc' i ↔
      (if i < c then acc i
        else if i = c then
          (if pol c = true then acc c ∨ chainFrom pol acc leaf n (c + 1)
            else acc c ∧ chainFrom pol acc leaf n (c + 1))
        else (pol i = false)))) (i : ℕ) (hi : i < n) :
    acc' i ↔ accCVal pol P le i v' := by
  rw [hnew i hi]
  rcases lt_trichotomy i c with hic | rfl | hic
  · rw [if_pos hic, hacc i hi]
    exact (accCVal_congr_above (lt_trans hic hc)
      (fun k hk => hagree k (by omega))).symm
  · rw [if_neg (lt_irrefl i), if_pos rfl,
      accCVal_carry (P := P) h hc hagree htop hsucc]
    by_cases hp : pol i = true
    · rw [if_pos hp, if_pos hp, hacc i hi]
      exact or_congr Iff.rfl (chainFrom_iff_foldFrom hacc hleaf (i + 1))
    · rw [if_neg hp, if_neg hp, hacc i hi]
      exact and_congr Iff.rfl (chainFrom_iff_foldFrom hacc hleaf (i + 1))
  · rw [if_neg (by omega), if_neg (by omega)]
    exact (accCVal_reset (P := P) hi (fun a => hbot ⟨i, hi⟩ hic a)).symm

/-- **At the first valuation every accumulator is the polarity's unit**:
nothing lies below a minimal coordinate, so a cleared register starts the
sweep. -/
theorem accCVal_bot {v : Fin n → A}
    (hbot : ∀ (i : Fin n) (a : A), le (v i) a) (i : ℕ) :
    accCVal pol P le i v ↔ (pol i = false) := by
  by_cases hin : i < n
  · exact accCVal_reset (P := P) hin fun a => hbot ⟨i, hin⟩ a
  · rw [accCVal, dif_neg hin]

end Vector

end Pfp

end DescriptiveComplexity
