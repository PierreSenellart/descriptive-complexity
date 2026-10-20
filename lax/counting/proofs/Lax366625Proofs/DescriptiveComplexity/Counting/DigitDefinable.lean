/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting
import Lax366625Proofs.DescriptiveComplexity.FixedPoint
import Lax366625Proofs.DescriptiveComplexity.OrderWalk
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (DigitDefinable DigitLFPDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

/-!
# Functions defined by their binary digits

A function from ordered structures to numbers is **digit-definable**
(`DescriptiveComplexity.DigitDefinable`) when its binary digits are relations
of a least fixed point: there are rules
(`DescriptiveComplexity.DigitLFPDef`) and finitely many of their relation
variables, `bit 0`, …, `bit (c - 1)`, all of the same arity `ℓ`, such that the
value is `∑ 2 ^ rank(τ, x̄)` over the pairs of a `τ < c` and a tuple `x̄` in the
relation `bit τ`. The pairs are the *positions* of the digits, ranked by `τ`
first and then lexicographically (`DescriptiveComplexity.orank`): the digit of
weight `2 ^ r` is `1` exactly when the position of rank `r` is in its relation.

Several relations are needed, and not only tuples of one: a structure with one
element has a single tuple of each length, and a function may take any value on
it.

This is the normal form through which QFO(LFP) is shown to capture FP
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], proof of Theorem 4.4):
a function computable in polynomial time has polynomially many digits, each
computable in polynomial time, hence, by the Immerman–Vardi theorem, definable
by a least fixed point over the ordered structure.

Both directions hold for the library's FP
(`DescriptiveComplexity.Problems.CircuitNumber`): digit-definable problems are
in FP (`DescriptiveComplexity.DigitDefinable.mem_FP`), and every problem of FP
is digit-definable (`DescriptiveComplexity.FPDefinable.digitDefinable`, in
`DescriptiveComplexity.Counting.Digits.NormalForm`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Classical in
/-- **A sum of place values, read along an enumeration of the digits.** Marked
elements `Out`, compared by `Below`, each contributing two to the number of
marked elements strictly below it when it carries a digit `Bit`: if the marked
elements are enumerated by a finite linear order, in order, the sum is the one
over that order, with ranks as exponents. -/
theorem finsum_digits_eq {X P : Type} [LinearOrder P] [Finite P] (Out Bit : X → Prop)
    (Below : X → X → Prop) (φ : P → X) (hφ : Function.Injective φ)
    (hout : ∀ x, Out x ↔ ∃ q, x = φ q) (hbelow : ∀ q' q, Below (φ q') (φ q) ↔ q' ≤ q) :
    (∑ᶠ x : X, if Out x ∧ Bit x then
        2 ^ Nat.card {y : X // Out y ∧ y ≠ x ∧ Below y x} else 0) =
      ∑ᶠ q : P, if Bit (φ q) then 2 ^ Lax895169.BitPredicate.orank q else 0 := by
  have hrank : ∀ q : P, Nat.card {y : X // Out y ∧ y ≠ φ q ∧ Below y (φ q)} = Lax895169.BitPredicate.orank q := by
    intro q
    rw [Lax895169.BitPredicate.orank, ← Nat.card_coe_set_eq]
    symm
    refine Nat.card_eq_of_bijective
      (fun q' => ⟨φ q'.1, (hout _).mpr ⟨q'.1, rfl⟩, fun h => ne_of_lt q'.2 (hφ h),
        (hbelow _ _).mpr (le_of_lt q'.2)⟩) ⟨?_, ?_⟩
    · intro y y' h
      exact Subtype.ext (hφ (congrArg Subtype.val h))
    · rintro ⟨y, ho, hne, hb⟩
      obtain ⟨q', rfl⟩ := (hout y).mp ho
      exact ⟨⟨q', lt_of_le_of_ne ((hbelow _ _).mp hb) fun h => hne (congrArg φ h)⟩, rfl⟩
  have hsupp : ∀ x ∈ Function.support (fun x : X => if Out x ∧ Bit x then
      2 ^ Nat.card {y : X // Out y ∧ y ≠ x ∧ Below y x} else 0),
      x ∈ Set.univ ↔ x ∈ Set.range φ := by
    intro x hx
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    have h : Out x ∧ Bit x := by
      by_contra h
      exact hx (if_neg h)
    obtain ⟨q, hq⟩ := (hout x).mp h.1
    exact ⟨q, hq.symm⟩
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ hsupp, finsum_mem_range hφ]
  refine finsum_congr fun q => ?_
  rw [hrank q]
  exact if_congr (and_iff_right ((hout _).mpr ⟨q, rfl⟩)) rfl rfl

/-- **Marked elements enumerated by a linear order are linearly ordered**:
the four clauses of a linear order among the marked elements. -/
theorem enum_linear {X P : Type} [LinearOrder P] (Out : X → Prop) (Below : X → X → Prop)
    (φ : P → X) (hout : ∀ x, Out x ↔ ∃ q, x = φ q)
    (hbelow : ∀ q' q, Below (φ q') (φ q) ↔ q' ≤ q) :
    (∀ p, Out p → Below p p) ∧
      (∀ p q r, Out p → Out q → Out r → Below p q → Below q r → Below p r) ∧
      (∀ p q, Out p → Out q → Below p q → Below q p → p = q) ∧
      ∀ p q, Out p → Out q → Below p q ∨ Below q p := by
  refine ⟨fun p hp => ?_, fun p q r hp hq hr hpq hqr => ?_, fun p q hp hq hpq hqp => ?_,
    fun p q hp hq => ?_⟩
  · obtain ⟨a, rfl⟩ := (hout p).mp hp
    exact (hbelow a a).mpr le_rfl
  · obtain ⟨a, rfl⟩ := (hout p).mp hp
    obtain ⟨b, rfl⟩ := (hout q).mp hq
    obtain ⟨c, rfl⟩ := (hout r).mp hr
    exact (hbelow a c).mpr (((hbelow a b).mp hpq).trans ((hbelow b c).mp hqr))
  · obtain ⟨a, rfl⟩ := (hout p).mp hp
    obtain ⟨b, rfl⟩ := (hout q).mp hq
    exact congrArg φ (le_antisymm ((hbelow a b).mp hpq) ((hbelow b a).mp hqp))
  · obtain ⟨a, rfl⟩ := (hout p).mp hp
    obtain ⟨b, rfl⟩ := (hout q).mp hq
    exact (le_total a b).imp (hbelow a b).mpr (hbelow b a).mpr

namespace DigitLFPDef

variable {L : Language.{0, 0}} (d : Lax366625.QuantitativeLogic.DigitLFPDef L) (A : Type) [L.Structure A] [LinearOrder A]

end DigitLFPDef

end Lax366625Proofs.DescriptiveComplexity


