/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.WeightedFacts
import DescriptiveComplexity.Counting.QuantitativeBinders
import DescriptiveComplexity.Problems.CircuitNumber.Membership

/-!
# The weights of a weighted instance, as quantitative terms

A weight of a fact of a weighted instance
(`DescriptiveComplexity.Counting.WeightedWorlds`) is written in binary in the
instance. It is the value of a term of quantitative first-order logic:

* `DescriptiveComplexity.wNum`: the number written by the bits of a fact,
  `Σi. [bit i] · Πj. ([j below i] + 1)`;
* `DescriptiveComplexity.fullPresT`, `DescriptiveComplexity.fullAbsT`: the
  weight of presence and the weight of absence of a fact, whatever its status
  (`DescriptiveComplexity.fullPresWeight`,
  `DescriptiveComplexity.fullAbsWeight`);
* `DescriptiveComplexity.linGuardT`: `1` when the positions are linearly
  ordered, `0` otherwise.

These are the leaves of a term computing the weighted count of a safe query:
see `DescriptiveComplexity.Examples.ProbabilisticQueries`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- The vocabulary of weighted instances, with the order of the definitions. -/
abbrev wOrd (L : Language.{0, 0}) : Language.{0, 0} := (weightedLang L).sum Language.order

section Terms

variable {δ : Type} {n : ℕ}

/-- “`j` is a position strictly below `i`”, in the order of the instance. -/
noncomputable def posLtF (j i : δ) : (wOrd L).Formula δ :=
  Relations.formula₂ (Sum.inl WeightedRel.le : (wOrd L).Relations 2) (Term.var j) (Term.var i) ⊓
    ∼(Term.equal (Term.var j) (Term.var i))

/-- **The number written by the bits of a fact**: `S(x̄, ·)` read in binary. -/
noncomputable def wNum (S : WeightedRel L (n + 1)) (e : Fin n → δ) : QTerm (wOrd L) δ :=
  QTerm.sumOver fun up i =>
    .mul (.ind (bitAtom (L' := wOrd L) (n := n) (Sum.inl S) (fun m => up (e m)) i))
      (QTerm.prodOver fun up' j => .add (.ind (posLtF j (up' i))) (.const 1))

/-- “The fact is certain.” -/
def certA (R : L.Relations n) (e : Fin n → δ) : (wOrd L).Formula δ :=
  factAtom (Sum.inl (WeightedRel.cert R) : (wOrd L).Relations n) e

/-- “The fact is uncertain.” -/
def uncA (R : L.Relations n) (e : Fin n → δ) : (wOrd L).Formula δ :=
  factAtom (Sum.inl (WeightedRel.unc R) : (wOrd L).Relations n) e

/-- **The weight of presence of a fact**, as a term. -/
noncomputable def fullPresT (R : L.Relations n) (e : Fin n → δ) : QTerm (wOrd L) δ :=
  QTerm.cond (certA R e) (.const 1) (QTerm.cond (uncA R e) (wNum (.pres R) e) (.const 0))

/-- **The weight of absence of a fact**, as a term. -/
noncomputable def fullAbsT (R : L.Relations n) (e : Fin n → δ) : QTerm (wOrd L) δ :=
  QTerm.cond (certA R e) (.const 0) (QTerm.cond (uncA R e) (wNum (.abs R) e) (.const 1))

/-- `1` when the positions of the instance are linearly ordered, `0`
otherwise. -/
noncomputable def linGuardT : QTerm (wOrd L) δ :=
  .ind (Formula.relabel (fun e : Empty => e.elim)
    (linOrdSentence (Sum.inl WeightedRel.le : (wOrd L).Relations 2)))

variable {A : Type} [(weightedLang L).Structure A] [LinearOrder A]

open Classical in
theorem eval_wNum [Finite A] (S : WeightedRel L (n + 1)) (e : Fin n → δ) (v : δ → A) :
    (wNum S e).eval v = binNum (WLe L A) (fun _ => True) (bitsOf S fun m => v (e m)) := by
  have hbit : ∀ a : A,
      (bitAtom (L' := wOrd L) (n := n) (Sum.inl S) (fun m => (Sum.inl (e m) : δ ⊕ Fin 1))
        (Sum.inr 0)).Realize (Sum.elim v fun _ => a) ↔ bitsOf S (fun m => v (e m)) a :=
    fun a => (realize_bitAtom (L' := wOrd L) (Sum.inl S) _ _ _).trans Iff.rfl
  have hlt : ∀ a b : A, (posLtF (L := L) (Sum.inr 0 : (δ ⊕ Fin 1) ⊕ Fin 1)
      (Sum.inl (Sum.inr 0))).Realize (Sum.elim (Sum.elim v fun _ => a) fun _ => b) ↔
      WLe L A b a ∧ b ≠ a := fun a b =>
    Formula.realize_inf.trans (and_congr Formula.realize_rel₂
      (Formula.realize_not.trans (not_congr Formula.realize_equal)))
  have hprod : ∀ a : A, ∏ᶠ b : A, ((if WLe L A b a ∧ b ≠ a then 1 else 0) + 1) =
      2 ^ bitRank (WLe L A) (fun _ => True) a := by
    intro a
    rw [finprod_boole_add_one, bitRank, ← Nat.card_coe_set_eq]
    exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun b =>
      ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩))
  rw [wNum, QTerm.eval_sumOver, binNum, finsum_mem_def]
  refine finsum_congr fun a => ?_
  rw [QTerm.eval_mul, QTerm.eval_ind, QTerm.eval_prodOver]
  simp only [QTerm.eval_add, QTerm.eval_ind, QTerm.eval_const, hlt, hbit, hprod,
    Set.indicator_apply, Set.mem_ofPred_eq, true_and]
  split_ifs <;> simp

open Classical in
theorem eval_fullPresT [Finite A] (R : L.Relations n) (e : Fin n → δ) (v : δ → A) :
    (fullPresT R e).eval v = fullPresWeight (⟨⟨n, R⟩, fun m => v (e m)⟩ : Fact L A) := by
  rw [fullPresT, QTerm.eval_cond, QTerm.eval_cond, eval_wNum, fullPresWeight]
  exact if_congr (realize_factAtom _ _ _) rfl (if_congr (realize_factAtom _ _ _) rfl rfl)

open Classical in
theorem eval_fullAbsT [Finite A] (R : L.Relations n) (e : Fin n → δ) (v : δ → A) :
    (fullAbsT R e).eval v = fullAbsWeight (⟨⟨n, R⟩, fun m => v (e m)⟩ : Fact L A) := by
  rw [fullAbsT, QTerm.eval_cond, QTerm.eval_cond, eval_wNum, fullAbsWeight]
  exact if_congr (realize_factAtom _ _ _) rfl (if_congr (realize_factAtom _ _ _) rfl rfl)

open Classical in
theorem eval_linGuardT (v : δ → A) :
    (linGuardT (L := L) : QTerm (wOrd L) δ).eval v = if IsLinOrd (WLe L A) then 1 else 0 := by
  rw [linGuardT, QTerm.eval_ind]
  refine if_congr (Formula.realize_relabel.trans ?_) rfl rfl
  refine (iff_of_eq (congrArg _ (Subsingleton.elim _ default))).trans ?_
  exact (realize_linOrdSentence (L' := wOrd L) (Sum.inl WeightedRel.le)).trans Iff.rfl

end Terms

end DescriptiveComplexity
