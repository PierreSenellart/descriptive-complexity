/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.Formulas
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

/-!
# The rows of a product sweep

The semantic half of the closure under products
(`DescriptiveComplexity.Counting.Digits.ProdSweep`). A product
`I · Πū. f(ū)` of numbers given by their digits is an iterated multiplication,
and a multiplication is an iterated addition; both iterations are one sweep,
along the pairs `(ū, j̄)` of a tuple and a position, the tuples increasing and,
for each tuple, the positions *decreasing* (`DescriptiveComplexity.Digits.prodIx`).

The row of `(ū, j̄)` holds (`DescriptiveComplexity.Digits.pval`)
`P · ⌊f(ū) / 2 ^ r⌋`, where `P` is the product before `ū` and `r` the rank of
`j̄`: Horner's scheme for `P · f(ū)`, read from the most significant digit of
`f(ū)` down. It is the double of the previous row, plus `P` when the digit of
rank `r` of `f(ū)` is `1` (`DescriptiveComplexity.Digits.prodPhi_eq`); and `P`
is itself a row, the last one of the previous tuple.
-/

namespace Lax366625Proofs.DescriptiveComplexity

namespace Digits

variable {A : Type} {m ℓ : ℕ}

/-- The tuple of an index of a product sweep. -/
def ut (i : Fin (m + ℓ) → A) : Fin m → A :=
  fun k => i (Fin.castAdd ℓ k)

/-- The position of an index of a product sweep. -/
def jt (i : Fin (m + ℓ) → A) : Fin ℓ → A :=
  fun k => i (Fin.natAdd m k)

theorem ut_append (u : Fin m → A) (j : Fin ℓ → A) : ut (Fin.append u j) = u :=
  funext fun k => Fin.append_left u j k

theorem jt_append (u : Fin m → A) (j : Fin ℓ → A) : jt (Fin.append u j) = j :=
  funext fun k => Fin.append_right u j k

theorem append_ut_jt (i : Fin (m + ℓ) → A) : Fin.append (ut i) (jt i) = i :=
  Fin.append_castAdd_natAdd

/-- A digit of a quotient by a power of two: Horner's step. -/
theorem div_two_pow_step (x r : ℕ) :
    x / 2 ^ r = 2 * (x / 2 ^ (r + 1)) + if x.testBit r = true then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ r = y
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h] <;> omega

variable [LinearOrder A]

/-- The indices of a product sweep, in the order of the sweep: the tuples
increasing, and for each tuple the positions decreasing. -/
def prodIx : (Fin (m + ℓ) → A) ≃ Lex (Fin m → A) ×ₗ (Lex (Fin ℓ → A))ᵒᵈ where
  toFun i := toLex (toLex (ut i), OrderDual.toDual (toLex (jt i)))
  invFun c := Fin.append (ofLex (ofLex c).1) (ofLex (OrderDual.ofDual (ofLex c).2))
  left_inv i := append_ut_jt i
  right_inv c := by
    change toLex (toLex (ut (Fin.append _ _)), OrderDual.toDual (toLex (jt (Fin.append _ _)))) = c
    rw [ut_append, jt_append]
    rfl

theorem prodIx_lt (i₀ i : Fin (m + ℓ) → A) :
    prodIx i₀ < prodIx i ↔ toLex (ut i₀) < toLex (ut i) ∨
      (toLex (ut i₀) = toLex (ut i) ∧ toLex (jt i) < toLex (jt i₀)) :=
  prodLex_lt_iff

theorem prodIx_bot (i : Fin (m + ℓ) → A) :
    (∀ c, prodIx i ≤ c) ↔
      (∀ c : Lex (Fin m → A), toLex (ut i) ≤ c) ∧ ∀ c : Lex (Fin ℓ → A), c ≤ toLex (jt i) :=
  prodLex_isBot_iff.trans (and_congr Iff.rfl
    ⟨fun h c => h (OrderDual.toDual c), fun h c => h (OrderDual.ofDual c)⟩)

theorem prodIx_cov [Nonempty A] (i₀ i : Fin (m + ℓ) → A) :
    prodIx i₀ ⋖ prodIx i ↔
      (toLex (ut i₀) = toLex (ut i) ∧ toLex (jt i) ⋖ toLex (jt i₀)) ∨
        (toLex (ut i₀) ⋖ toLex (ut i) ∧ (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) ∧
          ∀ c : Lex (Fin ℓ → A), c ≤ toLex (jt i)) :=
  prodLex_covBy_iff.trans (or_congr (and_congr Iff.rfl toDual_covBy_toDual_iff)
    (and_congr Iff.rfl (and_congr
      ⟨fun h c => h (OrderDual.toDual c), fun h c => h (OrderDual.ofDual c)⟩
      ⟨fun h c => h (OrderDual.toDual c), fun h c => h (OrderDual.ofDual c)⟩)))

/-- **The value of a row**: the product before the tuple, times the digits of
the factor of the tuple from the position up. -/
noncomputable def pval (Iw : ℕ) (f : Lex (Fin m → A) → ℕ) (i : Fin (m + ℓ) → A) : ℕ :=
  Iw * prodBefore f (toLex (ut i)) *
    (f (toLex (ut i)) % 2 ^ Nat.card (Lex (Fin ℓ → A)) / 2 ^ Lax895169.BitPredicate.orank (toLex (jt i)))

/-- **The condition defining a row** from the rows before it: the double of
the previous row of the same tuple, plus – when the digit of the factor at the
position is `1` – the product before the tuple, which is the initial number at
the first tuple and the last row of the previous tuple otherwise. -/
def prodPhi (Iw : ℕ) (f : Lex (Fin m → A) → ℕ) (i : Fin (m + ℓ) → A)
    (R : (Fin (m + ℓ) → A) → (Fin ℓ → A) → Prop) (p : Fin ℓ → A) : Prop :=
  AddSet
    (DblSet fun p' => ∃ j' : Fin ℓ → A, toLex (jt i) ⋖ toLex j' ∧ R (Fin.append (ut i) j') p')
    (fun p' => tupBits (f (toLex (ut i))) (jt i) ∧
      (((∀ c : Lex (Fin m → A), toLex (ut i) ≤ c) ∧ tupBits Iw p') ∨
        ∃ i₀ : Fin (m + ℓ) → A, toLex (ut i₀) ⋖ toLex (ut i) ∧
          (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) ∧ R i₀ p')) p

variable [Finite A] [Nonempty A]

open Classical in
/-- **A row is determined by the rows before it.** -/
theorem prodPhi_eq (Iw : ℕ) (f : Lex (Fin m → A) → ℕ) (i : Fin (m + ℓ) → A)
    (R : (Fin (m + ℓ) → A) → (Fin ℓ → A) → Prop)
    (hR : ∀ i₀, prodIx i₀ < prodIx i → R i₀ = tupBits (pval Iw f i₀)) :
    prodPhi Iw f i R = tupBits (pval Iw f i) := by
  set c := Nat.card (Lex (Fin ℓ → A)) with hc
  set Pre := Iw * prodBefore f (toLex (ut i)) with hPre
  set x := f (toLex (ut i)) % 2 ^ c with hx
  set r := Lax895169.BitPredicate.orank (toLex (jt i)) with hr
  have hrc : r < c := orank_lt_card _
  -- the product before the tuple
  have htop : (fun p' : Fin ℓ → A => ((∀ c : Lex (Fin m → A), toLex (ut i) ≤ c) ∧ tupBits Iw p') ∨
      ∃ i₀ : Fin (m + ℓ) → A, toLex (ut i₀) ⋖ toLex (ut i) ∧
        (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) ∧ R i₀ p') = tupBits Pre := by
    funext p'
    refine propext ?_
    by_cases hb : ∀ c : Lex (Fin m → A), toLex (ut i) ≤ c
    · rw [hPre, prodBefore_bot f hb, mul_one]
      exact ⟨fun h => h.elim (fun h' => h'.2)
        fun ⟨i₀, h₀, _⟩ => absurd h₀.lt (not_lt.mpr (hb _)), fun h => Or.inl ⟨hb, h⟩⟩
    · have hrow : ∀ i₀ : Fin (m + ℓ) → A, toLex (ut i₀) ⋖ toLex (ut i) →
          (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) → R i₀ = tupBits Pre := by
        intro i₀ h₀ hj₀
        rw [hR i₀ ((prodIx_lt i₀ i).mpr (Or.inl h₀.lt))]
        refine tupBits_congr ?_
        rw [pval, orank_eq_zero hj₀, pow_zero, Nat.div_one, hPre, prodBefore_covBy f h₀,
          ← mul_assoc, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      constructor
      · rintro (⟨h, -⟩ | ⟨i₀, h₀, hj₀, hp⟩)
        · exact absurd h hb
        · rwa [hrow i₀ h₀ hj₀] at hp
      · intro h
        obtain ⟨u₀, hu₀⟩ := exists_covBy_of_not_min hb
        obtain ⟨j₀, hj₀⟩ := Finite.exists_min (id : Lex (Fin ℓ → A) → Lex (Fin ℓ → A))
        have h₀ : toLex (ut (Fin.append (ofLex u₀) (ofLex j₀))) ⋖ toLex (ut i) := by
          rw [ut_append]
          exact hu₀
        have hj₀' : ∀ c : Lex (Fin ℓ → A), toLex (jt (Fin.append (ofLex u₀) (ofLex j₀))) ≤ c := by
          rw [jt_append]
          exact hj₀
        exact Or.inr ⟨_, h₀, hj₀', by rwa [hrow _ h₀ hj₀']⟩
  -- the previous row of the same tuple
  have hprev : (fun p' : Fin ℓ → A => ∃ j' : Fin ℓ → A, toLex (jt i) ⋖ toLex j' ∧
      R (Fin.append (ut i) j') p') = tupBits (Pre * (x / 2 ^ (r + 1))) := by
    have hrow : ∀ j' : Fin ℓ → A, toLex (jt i) ⋖ toLex j' →
        R (Fin.append (ut i) j') = tupBits (Pre * (x / 2 ^ (r + 1))) := by
      intro j' hj'
      rw [hR _ ((prodIx_lt _ i).mpr (Or.inr ⟨by rw [ut_append], by rw [jt_append]; exact hj'.lt⟩)),
        pval, ut_append, jt_append, orank_covBy hj']
    funext p'
    refine propext ?_
    by_cases ht : ∀ a : Lex (Fin ℓ → A), a ≤ toLex (jt i)
    · have hr1 : r + 1 = c := by
        have := orank_isTop ht
        omega
      rw [hr1, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos c)), mul_zero]
      exact iff_of_false (fun ⟨j', hj', _⟩ => absurd hj'.lt (not_lt.mpr (ht _))) (bitsOf_zero _)
    · obtain ⟨j', hlt, hnb⟩ := exists_gt_of_not_max ht
      have hj' : toLex (jt i) ⋖ toLex (ofLex j') := ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
      constructor
      · rintro ⟨j'', hj'', hp⟩
        rwa [hrow j'' hj''] at hp
      · intro h
        exact ⟨ofLex j', hj', by rwa [hrow _ hj']⟩
  have hbit : tupBits (f (toLex (ut i))) (jt i) ↔ x.testBit r = true := by
    rw [hx, Nat.testBit_mod_two_pow, decide_eq_true hrc, Bool.true_and]
    rfl
  have hscal : (fun p' : Fin ℓ → A => tupBits (f (toLex (ut i))) (jt i) ∧
      (((∀ c : Lex (Fin m → A), toLex (ut i) ≤ c) ∧ tupBits Iw p') ∨
        ∃ i₀ : Fin (m + ℓ) → A, toLex (ut i₀) ⋖ toLex (ut i) ∧
          (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) ∧ R i₀ p')) =
      tupBits (if x.testBit r = true then Pre else 0) := by
    funext p'
    refine propext ?_
    rw [congrFun htop p', hbit]
    exact (bitsOf_ite _ Pre (toLex p')).symm
  funext p
  unfold prodPhi
  rw [hprev, hscal, dblSet_tupBits, addSet_tupBits, pval]
  refine congrFun (congrArg tupBits ?_) p
  rw [← hPre, ← hx, ← hr, div_two_pow_step x r, mul_add, mul_left_comm]
  split_ifs <;> simp

end Digits

end Lax366625Proofs.DescriptiveComplexity


