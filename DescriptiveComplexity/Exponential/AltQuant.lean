/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Complexity

/-!
# A sentence as an alternating prefix, played one variable at a time

The first of the two normal forms that let a *machine* evaluate a fixed
first-order sentence with a finite control. A machine simulating an
`DescriptiveComplexity.SOGameSpec` has to decide the specification's four
sentences, and the only shape its control can have is a finite set of phases
carrying a tuple of elements. This file supplies the shape:

> every sentence is an **alternating quantifier prefix** over a
> quantifier-free matrix, and the prefix is a walk through the indices
> `0, 1, …, n - 1`, choosing the value of one variable at each step.

`DescriptiveComplexity.altQuantFrom` is that walk. Its state is exactly the
state of the machine that plays it: an index `j` – the phase – and a valuation
`Fin n → A` – the tuple – of which only the coordinates below `j` matter.
Each step **updates one coordinate**, existentially or universally as the
polarity `pol j` says, and at `j = n` the matrix is read off.

`DescriptiveComplexity.exists_altQuant` produces the data (the length `n`, the
polarities and the matrix) for an arbitrary sentence, by
`FirstOrder.Language.BoundedFormula.toPrenex` followed by an induction on
`FirstOrder.Language.BoundedFormula.IsPrenex`.

## Why the valuation is total, and updated in place

A prenex prefix is usually peeled with `Fin.snoc`, the valuation growing one
coordinate at a time; the matrix then sits at a level that changes during the
induction and the arithmetic `(k + 1) + m = k + (m + 1)` has to be transported
along a cast at every step. Here the total length `n` is *fixed by the
induction hypothesis* and it is the number `k` of variables already bound that
grows, so the matrix never moves, no cast appears, and – this is the point –
the resulting predicate is literally the transition system a machine runs:
one phase index, one tuple, one coordinate written per step.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### The prefix as a walk -/

section Walk

variable {A : Type*}

/-- The walk of `DescriptiveComplexity.altQuantFrom`, with an explicit fuel so
that the recursion is structural. The fuel is the number of variables left to
choose. -/
def altQuantAux {n : ℕ} (pol : ℕ → Bool) (P : (Fin n → A) → Prop) :
    ℕ → ℕ → (Fin n → A) → Prop
  | 0, _, v => P v
  | r + 1, j, v =>
      if h : j < n then
        (if pol j = true then ∃ a : A, altQuantAux pol P r (j + 1) (Function.update v ⟨j, h⟩ a)
          else ∀ a : A, altQuantAux pol P r (j + 1) (Function.update v ⟨j, h⟩ a))
      else P v

/-- **An alternating quantifier prefix, from the `j`-th variable on**: the
variables `j, j + 1, …, n - 1` are chosen in turn, the `i`-th by the player
`pol i` names, and the predicate `P` is then read off the resulting valuation.

Only the coordinates *below* `j` of the valuation matter
(`DescriptiveComplexity.altQuantFrom_congr_val`), so a machine playing
the prefix may carry an arbitrary tuple and overwrite it as it goes. -/
def altQuantFrom {n : ℕ} (pol : ℕ → Bool) (P : (Fin n → A) → Prop) (j : ℕ)
    (v : Fin n → A) : Prop :=
  altQuantAux pol P (n - j) j v

variable {n : ℕ} {pol : ℕ → Bool} {P : (Fin n → A) → Prop}

/-- Past the last variable, the prefix is the matrix. -/
theorem altQuantFrom_of_le {j : ℕ} (h : n ≤ j) (v : Fin n → A) :
    altQuantFrom pol P j v = P v := by
  rw [altQuantFrom, show n - j = 0 from Nat.sub_eq_zero_of_le h]
  rfl

/-- The prefix at its end is the matrix. -/
theorem altQuantFrom_last (v : Fin n → A) : altQuantFrom pol P n v = P v :=
  altQuantFrom_of_le le_rfl v

private theorem altQuantAux_succ {r j : ℕ} (h : j < n) (v : Fin n → A) :
    altQuantAux pol P (r + 1) j v =
      (if pol j = true then ∃ a : A, altQuantAux pol P r (j + 1) (Function.update v ⟨j, h⟩ a)
        else ∀ a : A, altQuantAux pol P r (j + 1) (Function.update v ⟨j, h⟩ a)) := by
  rw [altQuantAux, dif_pos h]

/-- **One existential step of the prefix**: the `j`-th variable is chosen by
the existential player. -/
theorem altQuantFrom_ex {j : ℕ} (h : j < n) (hp : pol j = true) (v : Fin n → A) :
    altQuantFrom pol P j v ↔
      ∃ a : A, altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a) := by
  rw [altQuantFrom, show n - j = (n - (j + 1)) + 1 by omega, altQuantAux_succ h, if_pos hp]
  rfl

/-- **One universal step of the prefix**: the `j`-th variable is chosen by the
universal player. -/
theorem altQuantFrom_all {j : ℕ} (h : j < n) (hp : pol j = false) (v : Fin n → A) :
    altQuantFrom pol P j v ↔
      ∀ a : A, altQuantFrom pol P (j + 1) (Function.update v ⟨j, h⟩ a) := by
  rw [altQuantFrom, show n - j = (n - (j + 1)) + 1 by omega, altQuantAux_succ h,
    if_neg (by simp [hp])]
  rfl

private theorem altQuantAux_congr_pol {pol' : ℕ → Bool} :
    ∀ (r j : ℕ), (∀ i, j ≤ i → pol i = pol' i) → ∀ v : Fin n → A,
      altQuantAux pol P r j v = altQuantAux pol' P r j v := by
  intro r
  induction r with
  | zero => intro _ _ _; rfl
  | succ r ih =>
    intro j hagree v
    by_cases h : j < n
    · rw [altQuantAux_succ h, altQuantAux_succ h, hagree j le_rfl]
      have hnext : ∀ i, j + 1 ≤ i → pol i = pol' i := fun i hi => hagree i (by omega)
      simp only [ih (j + 1) hnext]
    · rw [altQuantAux, altQuantAux, dif_neg h, dif_neg h]

/-- **The prefix only reads the polarities of the variables it still has to
choose.** -/
theorem altQuantFrom_congr_pol {pol' : ℕ → Bool} {j : ℕ}
    (hagree : ∀ i, j ≤ i → pol i = pol' i) (v : Fin n → A) :
    altQuantFrom pol P j v = altQuantFrom pol' P j v :=
  altQuantAux_congr_pol _ j hagree v

private theorem altQuantAux_congr_val : ∀ (r j : ℕ), n ≤ j + r → ∀ v v' : Fin n → A,
    (∀ i : Fin n, (i : ℕ) < j → v i = v' i) →
      altQuantAux pol P r j v = altQuantAux pol P r j v' := by
  intro r
  induction r with
  | zero =>
    intro j hj v v' hagree
    exact congrArg P (funext fun i => hagree i (by have := i.isLt; omega))
  | succ r ih =>
    intro j hj v v' hagree
    by_cases h : j < n
    · rw [altQuantAux_succ h, altQuantAux_succ h]
      have hstep : ∀ a : A, altQuantAux pol P r (j + 1) (Function.update v ⟨j, h⟩ a) =
          altQuantAux pol P r (j + 1) (Function.update v' ⟨j, h⟩ a) := by
        refine fun a => ih (j + 1) (by omega) _ _ fun i hi => ?_
        by_cases hij : (i : ℕ) = j
        · rw [show i = (⟨j, h⟩ : Fin n) from Fin.ext hij, Function.update_self,
            Function.update_self]
        · rw [Function.update_of_ne (fun hc => hij (congrArg Fin.val hc)),
            Function.update_of_ne (fun hc => hij (congrArg Fin.val hc)), hagree i (by omega)]
      simp only [hstep]
    · rw [altQuantAux, altQuantAux, dif_neg h, dif_neg h]
      exact congrArg P (funext fun i => hagree i (by have := i.isLt; omega))

/-- **The prefix only reads the coordinates already chosen**: a machine playing
it may carry an arbitrary tuple and overwrite it as it goes. -/
theorem altQuantFrom_congr_val {j : ℕ} (v v' : Fin n → A)
    (hagree : ∀ i : Fin n, (i : ℕ) < j → v i = v' i) :
    altQuantFrom pol P j v = altQuantFrom pol P j v' :=
  altQuantAux_congr_val _ j (by omega) v v' hagree

/-- Extending a restricted valuation by one element is updating the unrestricted
one at the next coordinate: the step the prefix takes, read on `Fin.snoc`. -/
theorem snoc_castLE_update {k n : ℕ} (hk : k < n) (hkn : k + 1 ≤ n) {v : Fin n → A}
    {xs : Fin k → A} (hagree : ∀ i, xs i = v (Fin.castLE hk.le i)) (a : A) (i : Fin (k + 1)) :
    (Fin.snoc xs a : Fin (k + 1) → A) i = Function.update v ⟨k, hk⟩ a (Fin.castLE hkn i) := by
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    have hlast : Fin.castLE hkn (Fin.last k) = (⟨k, hk⟩ : Fin n) := by ext; rfl
    rw [hlast, Function.update_self]
  · intro j
    rw [Fin.snoc_castSucc, hagree j]
    have hcast : Fin.castLE hkn j.castSucc = Fin.castLE hk.le j := by ext; rfl
    rw [hcast, Function.update_of_ne]
    exact fun hcon => absurd (congrArg Fin.val hcon) (by simpa using j.isLt.ne)

end Walk

/-! ### Every sentence is an alternating prefix -/

section Normal

variable {M : Language.{0, 0}}

open BoundedFormula in
/-- **A prenex formula is an alternating prefix over its matrix**, stated for a
formula with `k` variables already bound: the matrix has `n ≥ k` variables, the
first `k` of them being the ones already bound, and the prefix chooses the
remaining `n - k`.

The total length `n` comes from the induction hypothesis and never changes, so
the matrix is never transported along an arithmetic identity; what grows is the
number of bound variables. -/
theorem exists_altQuant_of_isPrenex :
    ∀ {k : ℕ} {ψ : M.BoundedFormula Empty k}, ψ.IsPrenex →
      ∃ (n : ℕ) (hkn : k ≤ n) (pol : ℕ → Bool) (mat : M.BoundedFormula Empty n), mat.IsQF ∧
        ∀ (A : Type) [M.Structure A] (v : Fin n → A) (xs : Fin k → A),
          (∀ i, xs i = v (Fin.castLE hkn i)) →
          (ψ.Realize default xs ↔ altQuantFrom pol (fun w => mat.Realize default w) k v) := by
  intro k ψ h
  induction h with
  | @of_isQF k ψ hqf =>
    refine ⟨k, le_rfl, fun _ => true, ψ, hqf, fun A _ v xs hagree => ?_⟩
    rw [altQuantFrom_last, show xs = v from funext fun i => by rw [hagree i]; simp]
  | @all k χ _ ih =>
    obtain ⟨n, hkn, pol, mat, hqf, hiff⟩ := ih
    have hk : k < n := hkn
    refine ⟨n, hk.le, Function.update pol k false, mat, hqf, fun A _ v xs hagree => ?_⟩
    rw [realize_all, altQuantFrom_all hk (by simp)]
    refine forall_congr' fun a => ?_
    rw [← altQuantFrom_congr_pol (pol := pol) fun i hi =>
      (Function.update_of_ne (by omega : i ≠ k) _ _).symm]
    exact hiff A _ _ (snoc_castLE_update hk hkn hagree a)
  | @ex k χ _ ih =>
    obtain ⟨n, hkn, pol, mat, hqf, hiff⟩ := ih
    have hk : k < n := hkn
    refine ⟨n, hk.le, Function.update pol k true, mat, hqf, fun A _ v xs hagree => ?_⟩
    rw [realize_ex, altQuantFrom_ex hk (by simp)]
    refine exists_congr fun a => ?_
    rw [← altQuantFrom_congr_pol (pol := pol) fun i hi =>
      (Function.update_of_ne (by omega : i ≠ k) _ _).symm]
    exact hiff A _ _ (snoc_castLE_update hk hkn hagree a)

/-- **Every sentence is an alternating quantifier prefix over a
quantifier-free matrix**, the prefix played one variable at a time.

This is the shape a machine can run: the phase is the index of the variable
being chosen, the tuple is the valuation, and the matrix is read off at the
end. The initial valuation is arbitrary – the prefix overwrites every
coordinate it reads. -/
theorem exists_altQuant (φ : M.Sentence) :
    ∃ (n : ℕ) (pol : ℕ → Bool) (mat : M.BoundedFormula Empty n), mat.IsQF ∧
      ∀ (A : Type) [M.Structure A] [Nonempty A] (v : Fin n → A),
        φ.Realize A ↔ altQuantFrom pol (fun w => mat.Realize default w) 0 v := by
  obtain ⟨n, hkn, pol, mat, hqf, hiff⟩ :=
    exists_altQuant_of_isPrenex (BoundedFormula.toPrenex_isPrenex φ)
  refine ⟨n, pol, mat, hqf, fun A _ _ v => ?_⟩
  refine Iff.trans ?_ (hiff A v default fun i => Fin.elim0 i)
  exact (BoundedFormula.realize_toPrenex φ).symm

end Normal

end DescriptiveComplexity
