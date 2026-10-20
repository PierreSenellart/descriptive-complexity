/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.Tower
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

/-!
# Arithmetic on numbers given by formulas

A number is given by a formula `ν` with a distinguished block of `ℓ` variables,
the *position*: under a valuation of the other variables, `ν` holds of the
positions of the digits `1`, a position being an `ℓ`-tuple of elements and
the positions being ordered lexicographically. This file builds, from such
formulas, the formulas of

* the sum (`DescriptiveComplexity.Digits.addF`), by carry lookahead;
* the double (`DescriptiveComplexity.Digits.dblF`), a shift by one position;
* the number one (`DescriptiveComplexity.Digits.oneF`);

and identifies what they hold of (`DescriptiveComplexity.Digits.AddSet`,
`DescriptiveComplexity.Digits.DblSet`) with the digits of the sum and of the
double (`DescriptiveComplexity.Digits.addSet_tupBits`,
`DescriptiveComplexity.Digits.dblSet_tupBits`). The numbers are read modulo
`2 ^ (n ^ ℓ)`, `n` being the size of the structure, and the operations are
exact modulo that.

The vocabulary `N` of the formulas is arbitrary; it receives the ordered
vocabulary through a map `ι`, along which the order formulas of
`DescriptiveComplexity.OrderWalk` are read.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

/-! ### Sets of positions -/

section Sem

variable {A : Type} [LinearOrder A] {ℓ : ℕ}

/-- The positions of the digits `1` of a number, the positions being the
`ℓ`-tuples in lexicographic order. -/
def tupBits (n : ℕ) (p : Fin ℓ → A) : Prop :=
  bitsOf n (toLex p)

/-- The sum of two sets of positions, by carry lookahead. -/
def AddSet (X Y : (Fin ℓ → A) → Prop) (p : Fin ℓ → A) : Prop :=
  Xor (Xor (X p) (Y p))
    (∃ q : Fin ℓ → A, toLex q < toLex p ∧ X q ∧ Y q ∧
      ∀ r : Fin ℓ → A, toLex q < toLex r → toLex r < toLex p → X r ∨ Y r)

/-- The double of a set of positions: its shift by one position. -/
def DblSet (X : (Fin ℓ → A) → Prop) (p : Fin ℓ → A) : Prop :=
  ∃ q : Fin ℓ → A, toLex q ⋖ toLex p ∧ X q

variable [Finite A]

theorem addSet_tupBits (m n : ℕ) :
    AddSet (tupBits m) (tupBits n) = (tupBits (m + n) : (Fin ℓ → A) → Prop) := by
  funext p
  refine propext ((bitsOf_add m n (toLex p)).trans ?_).symm
  refine iff_of_eq (congrArg _ (propext ?_))
  constructor
  · rintro ⟨q, hq, hm, hn, hall⟩
    exact ⟨ofLex q, hq, hm, hn, fun r => hall (toLex r)⟩
  · rintro ⟨q, hq, hm, hn, hall⟩
    exact ⟨toLex q, hq, hm, hn, fun r => hall (ofLex r)⟩

theorem dblSet_tupBits (n : ℕ) :
    DblSet (tupBits n) = (tupBits (2 * n) : (Fin ℓ → A) → Prop) := by
  funext p
  refine propext ((bitsOf_two_mul n (toLex p)).trans ?_).symm
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨ofLex q, hq, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨toLex q, hq, h⟩

theorem tupBits_one (p : Fin ℓ → A) :
    tupBits 1 p ↔ ∀ c : Lex (Fin ℓ → A), toLex p ≤ c :=
  bitsOf_one (toLex p)

theorem tupBits_congr {m n : ℕ}
    (h : m % 2 ^ Nat.card (Lex (Fin ℓ → A)) = n % 2 ^ Nat.card (Lex (Fin ℓ → A))) :
    (tupBits m : (Fin ℓ → A) → Prop) = tupBits n :=
  funext fun p => congrFun (bitsOf_congr h) (toLex p)

end Sem

/-! ### The formulas -/

section Formulas

variable {K N : Language.{0, 0}} (ι : K.sum Language.order →ᴸ N) {ℓ : ℕ} {γ : Type}

/-- The exclusive or of two formulas. -/
def xorF (φ ψ : N.Formula γ) : N.Formula γ :=
  (φ ⊓ ∼ψ) ⊔ (ψ ⊓ ∼φ)

/-- A number formula, read at the position bound by one more quantifier
block. -/
def atQ (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula ((γ ⊕ Fin ℓ) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) ν

/-- A number formula, read at the position bound by a second quantifier
block. -/
def atR (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (((γ ⊕ Fin ℓ) ⊕ Fin ℓ) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr) ν

/-- The carry into a position: some lower position generates it, and every
position in between propagates it. -/
noncomputable def carryF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin ℓ)
    (((ι.onFormula (lexSelLtF Sum.inr (Sum.inl ∘ Sum.inr)) ⊓ atQ ν₁) ⊓ atQ ν₂) ⊓
      Formula.iAlls (Fin ℓ)
        ((ι.onFormula (lexSelLtF (Sum.inl ∘ Sum.inr) Sum.inr) ⊓
            ι.onFormula (lexSelLtF Sum.inr (Sum.inl ∘ Sum.inl ∘ Sum.inr))).imp
          (atR ν₁ ⊔ atR ν₂)))

/-- **The sum of two numbers.** -/
noncomputable def addF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  xorF (xorF ν₁ ν₂) (carryF ι ν₁ ν₂)

/-- **The double of a number.** -/
noncomputable def dblF (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin ℓ) (ι.onFormula (succTupF Sum.inr (Sum.inl ∘ Sum.inr)) ⊓ atQ ν)

variable {A : Type} [K.Structure A] [LinearOrder A] [N.Structure A] [ι.IsExpansionOn A]

omit [K.Structure A] [LinearOrder A] in
theorem realize_xorF (φ ψ : N.Formula γ) (v : γ → A) :
    (xorF φ ψ).Realize v ↔ Xor (φ.Realize v) (ψ.Realize v) := by
  rw [xorF, Formula.realize_sup, Formula.realize_inf, Formula.realize_inf,
    Formula.realize_not, Formula.realize_not]
  rfl

/-- An order formula, read in the vocabulary `N`. -/
theorem realize_lift {δ : Type} (φ : (K.sum Language.order).Formula δ) (v : δ → A) :
    (ι.onFormula φ).Realize v ↔ φ.Realize v :=
  LHom.realize_onFormula ι φ

omit [K.Structure A] [LinearOrder A] [ι.IsExpansionOn A] in
theorem realize_atQ (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p q : Fin ℓ → A) :
    (atQ ν).Realize (Sum.elim (Sum.elim g p) q) ↔ ν.Realize (Sum.elim g q) := by
  rw [atQ, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl

omit [K.Structure A] [LinearOrder A] [ι.IsExpansionOn A] in
theorem realize_atR (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p q r : Fin ℓ → A) :
    (atR ν).Realize (Sum.elim (Sum.elim (Sum.elim g p) q) r) ↔ ν.Realize (Sum.elim g r) := by
  rw [atR, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl

theorem realize_carryF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (carryF ι ν₁ ν₂).Realize (Sum.elim g p) ↔
      ∃ q : Fin ℓ → A, toLex q < toLex p ∧ ν₁.Realize (Sum.elim g q) ∧
        ν₂.Realize (Sum.elim g q) ∧ ∀ r : Fin ℓ → A, toLex q < toLex r → toLex r < toLex p →
          ν₁.Realize (Sum.elim g r) ∨ ν₂.Realize (Sum.elim g r) := by
  rw [carryF, Formula.realize_iExs]
  refine exists_congr fun q => ?_
  rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, realize_lift,
    realize_lexSelLtF, realize_atQ, realize_atQ, Formula.realize_iAlls, and_assoc, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun r => ?_)))
  rw [Formula.realize_imp, Formula.realize_inf, realize_lift, realize_lift,
    realize_lexSelLtF, realize_lexSelLtF, Formula.realize_sup, realize_atR, realize_atR]
  exact and_imp

theorem realize_addF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (addF ι ν₁ ν₂).Realize (Sum.elim g p) ↔
      AddSet (fun p' => ν₁.Realize (Sum.elim g p')) (fun p' => ν₂.Realize (Sum.elim g p')) p := by
  rw [addF, realize_xorF, realize_xorF, realize_carryF]
  rfl

theorem realize_dblF (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (dblF ι ν).Realize (Sum.elim g p) ↔ DblSet (fun p' => ν.Realize (Sum.elim g p')) p := by
  rw [dblF, Formula.realize_iExs]
  refine exists_congr fun q => ?_
  rw [Formula.realize_inf, realize_lift, realize_succTupF, realize_atQ, tupSucc_iff_covBy]
  rfl

end Formulas

/-! ### A quantifier block before the position -/

section ExMid

variable {N : Language.{0, 0}} {γ : Type} {ℓ m : ℕ}

/-- Existential quantification over a block of variables that is not the last
one: the position stays last. -/
noncomputable def exMid (ξ : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin m)
    (Formula.relabel (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)) ξ)

theorem realize_exMid {A : Type} [N.Structure A] (ξ : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ))
    (g : γ → A) (p : Fin ℓ → A) :
    (exMid ξ).Realize (Sum.elim g p) ↔
      ∃ u : Fin m → A, ξ.Realize (Sum.elim (Sum.elim g u) p) := by
  rw [exMid, Formula.realize_iExs]
  refine exists_congr fun u => ?_
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with (x | x) | x <;> rfl

/-- A formula that does not mention a block of variables. -/
def weaken (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.map Sum.inl id) ν

theorem realize_weaken {A : Type} [N.Structure A] (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A)
    (u : Fin m → A) (p : Fin ℓ → A) :
    (weaken ν).Realize (Sum.elim (Sum.elim g u) p) ↔ ν.Realize (Sum.elim g p) := by
  rw [weaken, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl

end ExMid

end Digits

end Lax366625Proofs.DescriptiveComplexity


