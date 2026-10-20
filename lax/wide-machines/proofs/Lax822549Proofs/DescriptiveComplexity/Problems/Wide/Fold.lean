/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Increment
import Lax822549Proofs.DescriptiveComplexity.Exponential.AltQuant
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

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

namespace Lax822549Proofs.DescriptiveComplexity

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

/-- **At the last valuation the accumulator is the whole prefix**: every leaf has
been seen, so the sweep has finished computing the value of the subtree. This is
the half that reads the answer off the machine when it reaches the end of its
tape. -/
theorem foldFrom_top {v : Fin n → A} {j₀ : ℕ} (h : Lax904597.Machines.IsLinOrd le)
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

end Fold

end Lax822549Proofs.DescriptiveComplexity


