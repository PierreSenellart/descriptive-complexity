/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.Term
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.Bounds
import Lax366625Proofs.DescriptiveComplexity.Counting.DigitDefinable
import Lax366625Proofs.DescriptiveComplexity.FixedPointInflationaryLFP
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.NatCard
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

namespace Lax366625Proofs.DescriptiveComplexity.FPDefinable
end Lax366625Proofs.DescriptiveComplexity.FPDefinable

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (DigitDefinable FPDefinable QLFPDef QTerm)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The normal form of FP: every problem of FP is digit-definable

`DescriptiveComplexity.FPDefinable.digitDefinable`: a counting problem defined
in QFO(LFP) – a quantitative term, with sums and products over the universe,
read at a least fixed point (`DescriptiveComplexity.FPDefinable`) – has its
binary digits defined by a least fixed point
(`DescriptiveComplexity.DigitDefinable`). This is the half of the theorem that
QFO(LFP) captures FP
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4) saying
that a term is evaluated in polynomial time, read through the Immerman–Vardi
theorem; it is proved here inside the logic, with no machine.

## The construction

* The least fixed point of the definition is an inflationary induction
  (`DescriptiveComplexity.LFPDef.toStepDef`); above it, a tower of strata
  computes the digits of the term modulo `2 ^ (n ^ ℓ)`, for any `ℓ`
  (`DescriptiveComplexity.Digits.dig_term`).
* On a structure with `n ≥ 2` elements the value is below `2 ^ (n ^ ℓ)` for a
  suitable `ℓ` (`DescriptiveComplexity.QTerm.exists_bound`), so these are its
  digits. On a one-element structure the tuples are too few, and the digits are
  given directly by formulas (`DescriptiveComplexity.QTerm.exists_formulas`).
  One last first-order stratum puts the two cases together, in `M + 1` groups
  of digits (`DescriptiveComplexity.Digits.finalF`).
* The tower is one inflationary induction, whose limit is a least fixed point
  of rules (`DescriptiveComplexity.IFPLfp.homAssign_lfpAssign_trRules`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

/-- The rank of an element of `Fin c` is its value. -/
theorem orank_fin {c : ℕ} (i : Fin c) : Lax895169.BitPredicate.orank i = (i : ℕ) := by
  rw [Lax895169.BitPredicate.orank, show {y : Fin c | y < i} = ↑(Finset.Iio i) from (Finset.coe_Iio i).symm,
    Set.ncard_coe_finset, Fin.card_Iio]

theorem card_lex_tuple (A : Type) [Finite A] (ℓ : ℕ) :
    Nat.card (Lex (Fin ℓ → A)) = Nat.card A ^ ℓ := by
  rw [show Nat.card (Lex (Fin ℓ → A)) = Nat.card (Fin ℓ → A) from rfl, Nat.card_fun,
    Nat.card_fin]

/-- The digit at a position, a group and a tuple. -/
theorem bitsOf_pos {A : Type} [LinearOrder A] [Finite A] {c ℓ : ℕ} (V : ℕ) (τ : Fin c)
    (x : Fin ℓ → A) :
    bitsOf V (toLex (τ, toLex x) : Fin c ×ₗ Lex (Fin ℓ → A)) ↔
      V.testBit (τ * Nat.card (Lex (Fin ℓ → A)) + Lax895169.BitPredicate.orank (toLex x)) = true := by
  rw [bitsOf, orank_prodLex, orank_fin]

variable {L : Language.{0, 0}}

/-- The least fixed point of a definition in QFO(LFP), as an inflationary
induction: the base of the tower. -/
noncomputable def baseStep (d : Lax366625.QuantitativeLogic.QLFPDef L) : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order) :=
  LFPDef.toStepDef ⟨d.B, d.k, d.rules, ⊤⟩

/-- The output term of a definition, over the base of the tower. -/
def baseOut (d : Lax366625.QuantitativeLogic.QLFPDef L) :
    Lax366625.QuantitativeLogic.QTerm ((L.sum Language.order).sum (baseStep d).B.lang) Empty :=
  d.out

theorem value_eq (d : Lax366625.QuantitativeLogic.QLFPDef L) (A : Type) [L.Structure A] [LinearOrder A] (v : Empty → A) :
    d.value A = @Lax366625.QuantitativeLogic.QTerm.eval _ A (ctxStr (baseStep d) A) Empty (baseOut d) v := by
  have h : (baseStep d).inflLimit A = Lax535992.LeastFixedPoint.lfpAssign d.rules :=
    inflLimit_toStepDef ⟨d.B, d.k, d.rules, ⊤⟩ A
  have hv : v = default := Subsingleton.elim _ _
  subst hv
  exact congrArg (fun ρ : d.B.Assignment A =>
    @Lax366625.QuantitativeLogic.QTerm.eval _ A (d.B.structure₁ (L := L.sum Language.order) ρ) Empty d.out default) h.symm

section Final

variable {d : Lax366625.QuantitativeLogic.QLFPDef L} {e : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order)} {ℓ M : ℕ}

/-- “The structure has one element.” -/
noncomputable def singleF : ((L.sum Language.order).sum e.B.lang).Formula (Fin ℓ) :=
  Formula.iAlls (Fin 2) (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

open Classical in
/-- **The digits of one group**: on a one-element structure, the digit of the
value whose rank is the number of the group; otherwise the digits computed by
the tower, all in the first group. -/
noncomputable def finalF (x : (baseStep d).Ext e) (jD : e.B.lang.Relations (0 + ℓ))
    (χ : ℕ → ((L.sum Language.order).sum (baseStep d).B.lang).Formula Empty)
    (τ : Fin (M + 1)) : ((L.sum Language.order).sum e.B.lang).Formula (Fin ℓ) :=
  (singleF ⊓ Formula.relabel Empty.elim
      ((LHom.sumMap (LHom.id (L.sum Language.order))
        (SOBlock.homLHom x.emb x.arity_emb)).onFormula
          (listSup (((List.range (M + 1)).filter fun N => N.testBit τ).map χ)))) ⊔
    (∼singleF ⊓
      if (τ : ℕ) = 0 then ctxAt jD fun k => Fin.cast (Nat.zero_add ℓ) k else ⊥)

theorem realize_singleF (A : Type) [L.Structure A] [LinearOrder A] (v : Fin ℓ → A) :
    (@Formula.Realize _ A (ctxStr e A) _ singleF v) ↔ Subsingleton A := by
  let := e.B.structure (e.inflLimit A)
  rw [singleF, Formula.realize_iAlls]
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    have := h ![a, b]
    rwa [Formula.realize_equal] at this
  · intro h i
    rw [Formula.realize_equal]
    exact Subsingleton.elim _ _

theorem realize_finalF (x : (baseStep d).Ext e) {jD : e.B.lang.Relations (0 + ℓ)}
    (hjD : e.Computes jD (digRel ℓ (termFam (baseStep d) (baseOut d) Empty.elim)))
    {χ : ℕ → ((L.sum Language.order).sum (baseStep d).B.lang).Formula Empty}
    (hℓ : ∀ (A : Type) [((L.sum Language.order).sum (baseStep d).B.lang).Structure A]
      [Finite A], 2 ≤ Nat.card A → ∀ v : Empty → A,
        (baseOut d).eval v < 2 ^ (Nat.card A ^ ℓ))
    (hχ : ∀ (A : Type) [((L.sum Language.order).sum (baseStep d).B.lang).Structure A]
      [Subsingleton A] [Nonempty A] (v : Empty → A),
        (baseOut d).eval v ≤ M ∧ ∀ N, (χ N).Realize v ↔ (baseOut d).eval v = N)
    (τ : Fin (M + 1)) (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (v : Fin ℓ → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (finalF x jD χ τ) v) ↔
      bitsOf (d.value A) (toLex (τ, toLex v) : Fin (M + 1) ×ₗ Lex (Fin ℓ → A)) := by
  classical
  have hsingle := realize_singleF (e := e) A v
  have hdig := realize_ctxAt hjD A (fun k => Fin.cast (Nat.zero_add ℓ) k) v
  have hχ' : ∀ φ : ((L.sum Language.order).sum (baseStep d).B.lang).Formula Empty,
      (@Formula.Realize _ A (ctxStr e A) _
        (Formula.relabel Empty.elim ((LHom.sumMap (LHom.id (L.sum Language.order))
          (SOBlock.homLHom x.emb x.arity_emb)).onFormula φ)) v) ↔
        @Formula.Realize _ A (ctxStr (baseStep d) A) _ φ default := by
    intro φ
    have h := SOBlock.realize_homFormula (L := L.sum Language.order) x.emb x.arity_emb
      (e.inflLimit A) φ (v ∘ Empty.elim)
    rw [x.limit A] at h
    let := e.B.structure (e.inflLimit A)
    exact Formula.realize_relabel.trans
      (h.trans (iff_of_eq (congrArg _ (Subsingleton.elim _ _))))
  rw [bitsOf_pos]
  let := e.B.structure (e.inflLimit A)
  refine Formula.realize_sup.trans ?_
  by_cases hs : Subsingleton A
  · -- one element: the digits of the value, one per group
    obtain ⟨hle, hval⟩ := @hχ A (ctxStr (baseStep d) A) hs _ default
    rw [← value_eq d A default] at hle hval
    have hcard : Nat.card (Lex (Fin ℓ → A)) = 1 :=
      @Nat.card_of_subsingleton _ (toLex v) (inferInstanceAs (Subsingleton (Fin ℓ → A)))
    have hrank : Lax895169.BitPredicate.orank (toLex v) = 0 :=
      orank_eq_zero fun a => le_of_eq
        (@Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin ℓ → A))) _ _)
    rw [hcard, hrank, mul_one, add_zero]
    constructor
    · rintro (h | h)
      · have h2 := (hχ' _).mp (Formula.realize_inf.mp h).2
        obtain ⟨φ, hφ, hr⟩ :=
          (@realize_listSup _ _ _ (ctxStr (baseStep d) A) _ _).mp h2
        obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hφ
        rw [(hval N).mp hr]
        exact (List.mem_filter.mp hN).2
      · exact absurd (hsingle.mpr hs) (Formula.realize_not.mp (Formula.realize_inf.mp h).1)
    · intro h
      refine Or.inl (Formula.realize_inf.mpr ⟨hsingle.mpr hs, (hχ' _).mpr ?_⟩)
      exact (@realize_listSup _ _ _ (ctxStr (baseStep d) A) _ _).mpr
        ⟨_, List.mem_map.mpr ⟨d.value A,
          List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le hle), h⟩, rfl⟩,
          (hval _).mpr rfl⟩
  · -- at least two elements: the digits computed by the tower, in the first group
    have hn : 2 ≤ Nat.card A := by
      exact Finite.one_lt_card_iff_nontrivial.mpr (not_subsingleton_iff_nontrivial.mp hs)
    have hV := @hℓ A (ctxStr (baseStep d) A) _ hn default
    rw [← value_eq d A default, ← card_lex_tuple A ℓ] at hV
    have hdig' : (@Formula.Realize _ A (ctxStr e A) _
        (ctxAt jD fun k => Fin.cast (Nat.zero_add ℓ) k) v) ↔ tupBits (d.value A) v := by
      refine hdig.trans (iff_of_eq ?_)
      have h1 : (fun k : Fin ℓ => v (Fin.cast (Nat.zero_add ℓ) (Fin.natAdd 0 k))) = v :=
        funext fun k => congrArg v (Fin.ext (Nat.zero_add _))
      simp only [digRel, termFam, h1]
      rw [← value_eq d A]
    constructor
    · rintro (h | h)
      · exact absurd (hsingle.mp (Formula.realize_inf.mp h).1) hs
      · have h2 := (Formula.realize_inf.mp h).2
        by_cases hτ : (τ : ℕ) = 0
        · rw [if_pos hτ] at h2
          rw [hτ, zero_mul, zero_add]
          exact hdig'.mp h2
        · rw [if_neg hτ] at h2
          exact h2.elim
    · intro h
      refine Or.inr (Formula.realize_inf.mpr ⟨Formula.realize_not.mpr fun h' => hs (hsingle.mp h'),
        ?_⟩)
      by_cases hτ : (τ : ℕ) = 0
      · rw [if_pos hτ]
        rw [hτ, zero_mul, zero_add] at h
        exact hdig'.mpr h
      · exfalso
        have hge : Nat.card (Lex (Fin ℓ → A)) ≤
            τ * Nat.card (Lex (Fin ℓ → A)) + Lax895169.BitPredicate.orank (toLex v) :=
          (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hτ)).trans (Nat.le_add_right _ _)
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hV (Nat.pow_le_pow_right (by norm_num) hge))
        rw [this] at h
        exact Bool.false_ne_true h

end Final

end Digits

open Digits in
/-- **Every problem of FP is digit-definable**: the normal form of the
capture theorem for QFO(LFP), proved inside the logic. -/
theorem FPDefinable.digitDefinable {L : Language.{0, 0}} [L.IsRelational]
    {C : Lax366625.CountingProblems.CountingProblem L} (h : Lax366625.QuantitativeLogic.FPDefinable C) : Lax366625.QuantitativeLogic.DigitDefinable C := by
  classical
  obtain ⟨d, hd⟩ := h
  obtain ⟨ℓ, hℓ⟩ := (baseOut d).exists_bound
  obtain ⟨M, χ, hχ⟩ := (baseOut d).exists_formulas
  obtain ⟨e₁, x₁, jD, hjD⟩ :=
    dig_term ℓ (baseOut d) Empty.elim (baseStep d) (StepDef.Ext.refl _)
  obtain ⟨e₂, -, j, hjinj, hj⟩ := exists_ext_of_family e₁ (J := Fin (M + 1))
    (finalF x₁ jD χ)
    (fun τ A _ _ v => bitsOf (d.value A) (toLex (τ, toLex v) : Fin (M + 1) ×ₗ Lex (Fin ℓ → A)))
    (fun τ A _ _ _ _ v => realize_finalF x₁ hjD hℓ hχ τ A v)
  refine ⟨⟨IFPLfp.trBlock e₂, IFPLfp.kk e₂, IFPLfp.trRules e₂, M + 1, Nat.succ_pos M, ℓ,
    fun τ => IFPLfp.rIx e₂ (j τ).1, fun τ τ' hτ => hjinj (Sum.inl.inj hτ),
    fun τ => (j τ).2⟩, fun A _ _ _ _ => ?_⟩
  -- the digits of the definition are those of the value
  have hholds : ∀ q : Fin (M + 1) ×ₗ Lex (Fin ℓ → A),
      Lax366625.QuantitativeLogic.DigitLFPDef.Holds (L := L) ⟨IFPLfp.trBlock e₂, IFPLfp.kk e₂, IFPLfp.trRules e₂, M + 1,
        Nat.succ_pos M, ℓ, fun τ => IFPLfp.rIx e₂ (j τ).1,
        fun τ τ' hτ => hjinj (Sum.inl.inj hτ), fun τ => (j τ).2⟩ A q ↔
        bitsOf (d.value A) q := by
    rintro ⟨τ, v⟩
    refine Iff.trans ?_ (hj τ A v)
    change SOBlock.homAssign (IFPLfp.rIx e₂) (IFPLfp.trArity_rIx e₂)
      (Lax535992.LeastFixedPoint.lfpAssign (IFPLfp.trRules e₂)) (j τ).1 (fun k => v (Fin.cast (j τ).2 k)) ↔ _
    rw [IFPLfp.homAssign_lfpAssign_trRules]
  -- the value has fewer digits than there are positions
  have hlt : d.value A < 2 ^ Nat.card (Fin (M + 1) ×ₗ Lex (Fin ℓ → A)) := by
    have hcard : Nat.card (Fin (M + 1) ×ₗ Lex (Fin ℓ → A)) =
        (M + 1) * Nat.card (Lex (Fin ℓ → A)) := by
      rw [show Nat.card (Fin (M + 1) ×ₗ Lex (Fin ℓ → A)) =
        Nat.card (Fin (M + 1) × Lex (Fin ℓ → A)) from rfl, Nat.card_prod, Nat.card_fin]
    rw [hcard]
    by_cases hs : Subsingleton A
    · have hle := (@hχ A (ctxStr (baseStep d) A) hs _ default).1
      rw [← value_eq d A default] at hle
      have hone : Nat.card (Lex (Fin ℓ → A)) = 1 := by
        rw [card_lex_tuple, @Nat.card_of_subsingleton _ (Classical.arbitrary A) hs, one_pow]
      rw [hone, mul_one]
      exact lt_of_le_of_lt hle ((Nat.lt_succ_self M).trans Nat.lt_two_pow_self)
    · have hn : 2 ≤ Nat.card A := by
        exact Finite.one_lt_card_iff_nontrivial.mpr (not_subsingleton_iff_nontrivial.mp hs)
      have hV := @hℓ A (ctxStr (baseStep d) A) _ hn default
      rw [← value_eq d A default, ← card_lex_tuple A ℓ] at hV
      exact lt_of_lt_of_le hV (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos M)))
  rw [hd A, Lax366625.QuantitativeLogic.DigitLFPDef.value]
  refine (finsum_bitsOf hlt).symm.trans (finsum_congr fun q => ?_)
  exact if_congr (hholds q).symm rfl rfl

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.FPDefinable

export Lax366625Proofs.DescriptiveComplexity.FPDefinable (digitDefinable)

end Lax366625.QuantitativeLogic.FPDefinable

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

end Lax366625Proofs.DescriptiveComplexity


