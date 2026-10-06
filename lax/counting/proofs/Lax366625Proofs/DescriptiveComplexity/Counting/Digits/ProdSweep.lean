/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.ProdSem
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.SumSweep
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

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Closure under products over the tuples of the structure

`DescriptiveComplexity.Digits.Dig.prod`: if the digits of a family `I` of
numbers with parameters `w̄`, and of a family `F` with parameters `w̄` and `ū`,
can be added to a tower, so can the digits of `I(w̄) · Πū. F(w̄, ū)`. With one
tuple `ū` only, this is closure under multiplication
(`DescriptiveComplexity.Digits.Dig.mul`).

The semantics is `DescriptiveComplexity.Counting.Digits.ProdSem`: one sweep
along the pairs of a tuple and a position. What is here is the formula of a
row (`DescriptiveComplexity.Digits.prodTheta`), the order of the sweep as
formulas (`DescriptiveComplexity.Digits.prodBotF`,
`DescriptiveComplexity.Digits.prodCovF`), and the reading of the answer off the
last row.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

variable {K : Language.{0, 0}}

/-! ### The order of the sweep -/

section Order

variable {e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)} {m ℓ : ℕ}

variable (e m ℓ) in
/-- “The index is the first one”: the least tuple, at the greatest
position. -/
noncomputable def prodBotF : ((K.sum Language.order).sum e.B.lang).Formula (Fin (m + ℓ)) :=
  LHom.sumInl.onFormula (minTupF (Fin.castAdd ℓ) ⊓ maxTupF (Fin.natAdd m))

variable (e m ℓ) in
/-- “The second index follows the first”: the same tuple at the position just
below, or the next tuple at the greatest position, from the least one. -/
noncomputable def prodCovF :
    ((K.sum Language.order).sum e.B.lang).Formula (Fin (m + ℓ) ⊕ Fin (m + ℓ)) :=
  LHom.sumInl.onFormula
    ((eqTupF (L := K) (fun k => Sum.inr (Fin.castAdd ℓ k)) (fun k => Sum.inl (Fin.castAdd ℓ k)) ⊓
        succTupF (fun k => Sum.inr (Fin.natAdd m k)) (fun k => Sum.inl (Fin.natAdd m k))) ⊔
      ((succTupF (fun k => Sum.inl (Fin.castAdd ℓ k)) (fun k => Sum.inr (Fin.castAdd ℓ k)) ⊓
          minTupF (fun k => Sum.inl (Fin.natAdd m k))) ⊓
        maxTupF (fun k => Sum.inr (Fin.natAdd m k))))

variable {A : Type} [K.Structure A] [LinearOrder A]

theorem realize_prodBotF (i : Fin (m + ℓ) → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (prodBotF e m ℓ) i) ↔ ∀ c, prodIx i ≤ c := by
  let := e.B.structure (e.inflLimit A)
  refine (LHom.realize_onFormula
    (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) _).trans
    (Iff.trans ?_ (prodIx_bot i).symm)
  exact Formula.realize_inf.trans (and_congr
    ((realize_minTupF (L := K) (v := i) (Fin.castAdd ℓ)).trans (tup_isBot_iff (t := ut i)).symm)
    ((realize_maxTupF (L := K) (v := i) (Fin.natAdd m)).trans (tup_isTop_iff (t := jt i)).symm))

theorem realize_prodCovF [Nonempty A] (i₀ i : Fin (m + ℓ) → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (prodCovF e m ℓ) (Sum.elim i₀ i)) ↔
      prodIx i₀ ⋖ prodIx i := by
  let := e.B.structure (e.inflLimit A)
  refine (LHom.realize_onFormula
    (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) _).trans
    (Iff.trans ?_ (prodIx_cov i₀ i).symm)
  refine Formula.realize_sup.trans (or_congr ?_ ?_)
  · refine Formula.realize_inf.trans (and_congr ?_ ?_)
    · exact (realize_eqTupF (L := K) (v := Sum.elim i₀ i)).trans
        ⟨fun h => congrArg toLex h, fun h => h⟩
    · exact (realize_succTupF (L := K) (v := Sum.elim i₀ i) _ _).trans
        (tupSucc_iff_covBy (t := jt i) (t' := jt i₀))
  · refine Formula.realize_inf.trans (and_congr (Formula.realize_inf.trans (and_congr ?_ ?_)) ?_)
      |>.trans and_assoc
    · exact (realize_succTupF (L := K) (v := Sum.elim i₀ i) _ _).trans
        (tupSucc_iff_covBy (t := ut i₀) (t' := ut i))
    · exact (realize_minTupF (L := K) (v := Sum.elim i₀ i) _).trans
        (tup_isBot_iff (t := jt i₀)).symm
    · exact (realize_maxTupF (L := K) (v := Sum.elim i₀ i) _).trans
        (tup_isTop_iff (t := jt i)).symm

end Order

/-! ### The rows -/

/-- The rows of the product sweep, as a family of numbers with the index as
further parameters. -/
noncomputable def prodFam {a m : ℕ} (ℓ : ℕ) (I : Fam K a) (F : Fam K (a + m)) :
    Fam K (a + (m + ℓ)) :=
  fun A _ _ x => pval (I A fun k => x (Fin.castAdd (m + ℓ) k))
    (fun u' : Lex (Fin m → A) =>
      F A (Fin.append (fun k => x (Fin.castAdd (m + ℓ) k)) (ofLex u')))
    fun k => x (Fin.natAdd a k)

section Theta

variable {e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)} {a m ℓ : ℕ}

/-- The product before the tuple of the index: the initial number at the
least tuple, the last row of the previous tuple otherwise. -/
noncomputable def prodTopF (jI : e.B.lang.Relations (a + ℓ)) :
    (((K.sum Language.order).sum e.B.lang).sum (sweepBlock a (m + ℓ) ℓ).lang).Formula
      ((Fin a ⊕ Fin (m + ℓ)) ⊕ Fin ℓ) :=
  ((sweepHom e a (m + ℓ) ℓ).onFormula
        (minTupF fun k => Sum.inl (Sum.inr (Fin.castAdd ℓ k))) ⊓
      LHom.sumInl.onFormula (numAt jI Sum.inl)) ⊔
    exMid (m := m + ℓ)
      (((sweepHom e a (m + ℓ) ℓ).onFormula
            (succTupF (fun k => Sum.inl (Sum.inr (Fin.castAdd ℓ k)))
              fun k => Sum.inl (Sum.inl (Sum.inr (Fin.castAdd ℓ k)))) ⊓
          (sweepHom e a (m + ℓ) ℓ).onFormula
            (minTupF fun k => Sum.inl (Sum.inr (Fin.natAdd m k)))) ⊓
        rowAt (fun k => Sum.inl (Sum.inl (Sum.inl k))) (fun k => Sum.inl (Sum.inr k)) Sum.inr)

variable (e a m ℓ) in
/-- The previous row of the same tuple: the row of the position just above. -/
noncomputable def prodPrevF :
    (((K.sum Language.order).sum e.B.lang).sum (sweepBlock a (m + ℓ) ℓ).lang).Formula
      ((Fin a ⊕ Fin (m + ℓ)) ⊕ Fin ℓ) :=
  exMid (m := ℓ)
    ((sweepHom e a (m + ℓ) ℓ).onFormula
        (succTupF (fun k => Sum.inl (Sum.inl (Sum.inr (Fin.natAdd m k))))
          fun k => Sum.inl (Sum.inr k)) ⊓
      rowAt (fun k => Sum.inl (Sum.inl (Sum.inl k)))
        (Fin.append (fun k => Sum.inl (Sum.inl (Sum.inr (Fin.castAdd ℓ k))))
          fun k => Sum.inl (Sum.inr k)) Sum.inr)

/-- **The row of an index**: the double of the previous row of the tuple,
plus the product before the tuple when the digit of the factor is `1`. -/
noncomputable def prodTheta (jI : e.B.lang.Relations (a + ℓ))
    (jF : e.B.lang.Relations (a + m + ℓ)) :
    (((K.sum Language.order).sum e.B.lang).sum (sweepBlock a (m + ℓ) ℓ).lang).Formula
      ((Fin a ⊕ Fin (m + ℓ)) ⊕ Fin ℓ) :=
  addF (sweepHom e a (m + ℓ) ℓ) (dblF (sweepHom e a (m + ℓ) ℓ) (prodPrevF e a m ℓ))
    (Formula.relabel Sum.inl (LHom.sumInl.onFormula
        (ctxAt jF (Fin.append (Fin.append Sum.inl fun k => Sum.inr (Fin.castAdd ℓ k))
          fun k => Sum.inr (Fin.natAdd m k)))) ⊓
      prodTopF jI)

theorem realize_prodTheta {jI : e.B.lang.Relations (a + ℓ)}
    {jF : e.B.lang.Relations (a + m + ℓ)} {I : Fam K a} {F : Fam K (a + m)}
    (hjI : e.Computes jI (digRel ℓ I)) (hjF : e.Computes jF (digRel ℓ F)) (A : Type)
    [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ρ : (sweepBlock a (m + ℓ) ℓ).Assignment A) (w : Fin a → A) (i : Fin (m + ℓ) → A)
    (p : Fin ℓ → A) :
    (@Formula.Realize _ A
        (@Lax535992.InflationaryFixedPoint.SOBlock.structure₁ ((K.sum Language.order).sum e.B.lang) (sweepBlock a (m + ℓ) ℓ) A
          (ctxStr e A) ρ) _ (prodTheta jI jF) (Sum.elim (Sum.elim w i) p)) ↔
      prodPhi (I A w) (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u'))) i
        (fun i₀ p' => ρ true (j3 w i₀ p')) p := by
  have hI : ∀ p' : Fin ℓ → A,
      (@Formula.Realize _ A (ctxStr e A) _ (numAt jI Sum.inl) (Sum.elim (Sum.elim w i) p')) ↔
        tupBits (I A w) p' := fun p' => realize_numAt hjI A Sum.inl (Sum.elim w i) p'
  have hbit : (@Formula.Realize _ A (ctxStr e A) _
      (ctxAt jF (Fin.append (Fin.append Sum.inl fun k => Sum.inr (Fin.castAdd ℓ k))
        fun k => Sum.inr (Fin.natAdd m k))) (Sum.elim w i)) ↔
      tupBits (F A (Fin.append w (ut i))) (jt i) := by
    refine (realize_ctxAt hjF A _ _).trans (iff_of_eq ?_)
    have hx : (fun k => Sum.elim w i
        (Fin.append (Fin.append Sum.inl fun k => Sum.inr (Fin.castAdd ℓ k))
          (fun k => Sum.inr (Fin.natAdd m k)) k)) = j3 w (ut i) (jt i) :=
      (comp_append _ _ _).trans (congrArg (fun f => Fin.append f _) (comp_append _ _ _))
    rw [hx]
    simp only [digRel, j3, Fin.append_left, Fin.append_right]
  have hrow₁ := fun (i₀ : Fin (m + ℓ) → A) (p' : Fin ℓ → A) =>
    @realize_rowAt ((K.sum Language.order).sum e.B.lang) a (m + ℓ) ℓ _ A (ctxStr e A) ρ
      (fun k => Sum.inl (Sum.inl (Sum.inl k))) (fun k => Sum.inl (Sum.inr k)) Sum.inr
      (Sum.elim (Sum.elim (Sum.elim w i) i₀) p')
  have hrow₂ : ∀ (j' p' : Fin ℓ → A),
      (@Formula.Realize _ A
        (@Lax535992.InflationaryFixedPoint.SOBlock.structure₁ ((K.sum Language.order).sum e.B.lang) (sweepBlock a (m + ℓ) ℓ) A
          (ctxStr e A) ρ) _
        (rowAt (fun k => Sum.inl (Sum.inl (Sum.inl k)))
          (Fin.append (fun k => Sum.inl (Sum.inl (Sum.inr (Fin.castAdd ℓ k))))
            fun k => Sum.inl (Sum.inr k)) Sum.inr)
        (Sum.elim (Sum.elim (Sum.elim w i) j') p')) ↔
        ρ true (j3 w (Fin.append (ut i) j') p') := by
    intro j' p'
    refine (@realize_rowAt ((K.sum Language.order).sum e.B.lang) a (m + ℓ) ℓ _ A (ctxStr e A) ρ
      _ _ _ _).trans (iff_of_eq (congrArg (fun x => ρ true (j3 w x p')) ?_))
    exact comp_append _ _ _
  let := e.B.structure (e.inflLimit A)
  let := (sweepBlock a (m + ℓ) ℓ).structure ρ
  have : (sweepHom e a (m + ℓ) ℓ).IsExpansionOn A := isExpansionOn_comp _ _ A
  have hl : ∀ {α : Type} (φ : ((K.sum Language.order).sum e.B.lang).Formula α) (v : α → A),
      ((LHom.sumInl : (K.sum Language.order).sum e.B.lang →ᴸ
        ((K.sum Language.order).sum e.B.lang).sum (sweepBlock a (m + ℓ) ℓ).lang).onFormula
          φ).Realize v ↔ φ.Realize v :=
    fun φ v => LHom.realize_onFormula _ φ
  -- the product before the tuple
  have htop : ∀ p' : Fin ℓ → A, (prodTopF (m := m) jI).Realize (Sum.elim (Sum.elim w i) p') ↔
      (((∀ c : Lex (Fin m → A), toLex (ut i) ≤ c) ∧ tupBits (I A w) p') ∨
        ∃ i₀ : Fin (m + ℓ) → A, toLex (ut i₀) ⋖ toLex (ut i) ∧
          (∀ c : Lex (Fin ℓ → A), toLex (jt i₀) ≤ c) ∧ ρ true (j3 w i₀ p')) := by
    intro p'
    refine Formula.realize_sup.trans (or_congr ?_ ?_)
    · refine Formula.realize_inf.trans (and_congr ?_ ((hl _ _).trans (hI p')))
      exact (realize_lift (sweepHom e a (m + ℓ) ℓ) _ _).trans
        ((realize_minTupF (L := K) (v := Sum.elim (Sum.elim w i) p') _).trans
          (tup_isBot_iff (t := ut i)).symm)
    · refine (realize_exMid _ (Sum.elim w i) p').trans (exists_congr fun i₀ => ?_)
      refine (Formula.realize_inf.trans (and_congr
        (Formula.realize_inf.trans (and_congr ?_ ?_)) (hrow₁ i₀ p'))).trans and_assoc
      · exact (realize_lift (sweepHom e a (m + ℓ) ℓ) _ _).trans
          ((realize_succTupF (L := K) (v := Sum.elim (Sum.elim (Sum.elim w i) i₀) p') _ _).trans
            (tupSucc_iff_covBy (t := ut i₀) (t' := ut i)))
      · exact (realize_lift (sweepHom e a (m + ℓ) ℓ) _ _).trans
          ((realize_minTupF (L := K) (v := Sum.elim (Sum.elim (Sum.elim w i) i₀) p') _).trans
            (tup_isBot_iff (t := jt i₀)).symm)
  -- the previous row of the tuple
  have hprev : ∀ p' : Fin ℓ → A, (prodPrevF e a m ℓ).Realize (Sum.elim (Sum.elim w i) p') ↔
      ∃ j' : Fin ℓ → A, toLex (jt i) ⋖ toLex j' ∧ ρ true (j3 w (Fin.append (ut i) j') p') := by
    intro p'
    refine (realize_exMid _ (Sum.elim w i) p').trans (exists_congr fun j' => ?_)
    refine Formula.realize_inf.trans (and_congr ?_ (hrow₂ j' p'))
    exact (realize_lift (sweepHom e a (m + ℓ) ℓ) _ _).trans
      ((realize_succTupF (L := K) (v := Sum.elim (Sum.elim (Sum.elim w i) j') p') _ _).trans
        (tupSucc_iff_covBy (t := jt i) (t' := j')))
  refine (realize_addF (sweepHom e a (m + ℓ) ℓ) _ _ (Sum.elim w i) p).trans
    (iff_of_eq (congrArg₂ (fun X Y => AddSet X Y p)
      (funext fun p' => propext ?_) (funext fun p' => propext ?_)))
  · exact (realize_dblF (sweepHom e a (m + ℓ) ℓ) _ (Sum.elim w i) p').trans
      (iff_of_eq (congrArg (fun X => DblSet X p') (funext fun p'' => propext (hprev p''))))
  · exact Formula.realize_inf.trans (and_congr
      (Formula.realize_relabel.trans ((hl _ _).trans hbit)) (htop p'))

end Theta

/-! ### Closure -/

section Closure

variable {e₀ : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)} {ℓ : ℕ}

/-- **Closure under products over tuples**, with an initial factor. -/
theorem Dig.prod {a m : ℕ} {I : Fam K a} {F : Fam K (a + m)} (hI : Dig e₀ ℓ I)
    (hF : Dig e₀ ℓ F) :
    Dig e₀ ℓ (fun A _ _ w => I A w * ∏ᶠ u : Fin m → A, F A (Fin.append w u)) := by
  intro e x
  obtain ⟨e₁, y₁, jI, hjI⟩ := hI e x
  obtain ⟨e₂, y₂, jF, hjF⟩ := hF e₁ (x.trans y₁)
  have hjI' := hjI.ext y₂
  obtain ⟨e₃, y₃, jR, hjR⟩ := exists_ext_of_sweep e₂ (prodBotF e₂ m ℓ) (prodCovF e₂ m ℓ)
    (prodTheta (y₂.sym jI) jF) (digRel ℓ (prodFam ℓ I F)) (fun A _ _ _ _ w i p => by
      have key := @inflLimit_sweep _ a (m + ℓ) ℓ A (ctxStr e₂ A)
        (Lex (Fin m → A) ×ₗ (Lex (Fin ℓ → A))ᵒᵈ) _ _ prodIx
        (prodBotF e₂ m ℓ) (prodCovF e₂ m ℓ) (prodTheta (y₂.sym jI) jF)
        realize_prodBotF realize_prodCovF
        (fun w c R p => prodPhi (I A w) (fun u' => F A (Fin.append w (ofLex u')))
          (prodIx.symm c) (fun i₀ => R (prodIx i₀)) p)
        (fun w c => tupBits (pval (I A w) (fun u' => F A (Fin.append w (ofLex u')))
          (prodIx.symm c)))
        (by
          intro w c R hR
          refine prodPhi_eq _ _ _ _ fun i₀ h => ?_
          rw [Equiv.apply_symm_apply] at h
          rw [hR (prodIx i₀) h, Equiv.symm_apply_apply])
        (fun ρ w i p => by
          simp only [Equiv.symm_apply_apply]
          exact realize_prodTheta hjI' hjF A ρ w i p)
        w i p
      rw [Equiv.symm_apply_apply] at key
      refine key.trans (iff_of_eq ?_)
      simp only [digRel, prodFam, j3, Fin.append_left, Fin.append_right])
  obtain ⟨e₄, y₄, j, hj⟩ := exists_ext_of_num e₃
    (Formula.iExs (Fin (m + ℓ))
      (LHom.sumInl.onFormula (maxTupF (fun k => Sum.inr (Fin.castAdd ℓ k)) ⊓
          minTupF fun k => Sum.inr (Fin.natAdd m k)) ⊓
        ctxAt jR (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
          fun k => Sum.inl (Sum.inr k))))
    (fun A _ _ w => I A w * ∏ᶠ u : Fin m → A, F A (Fin.append w u))
    (fun A _ _ _ _ w p => by
      have hrow : ∀ i : Fin (m + ℓ) → A,
          (@Formula.Realize _ A (ctxStr e₃ A) _
            (ctxAt jR (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
              fun k => Sum.inl (Sum.inr k))) (Sum.elim (Sum.elim w p) i)) ↔
            tupBits (pval (I A w) (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u')))
              i) p := by
        intro i
        refine (realize_ctxAt hjR A _ _).trans (iff_of_eq ?_)
        have hx : (fun k => Sum.elim (Sum.elim w p) i
            (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
              (fun k => Sum.inl (Sum.inr k)) k)) = j3 w i p :=
          (comp_append _ _ _).trans
            (congrArg (fun f => Fin.append f _) (comp_append _ _ _))
        rw [hx]
        simp only [digRel, prodFam, j3, Fin.append_left, Fin.append_right]
      have hval : ∀ i : Fin (m + ℓ) → A, (∀ c : Lex (Fin m → A), c ≤ toLex (ut i)) →
          (∀ c : Lex (Fin ℓ → A), toLex (jt i) ≤ c) →
          (tupBits (pval (I A w) (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u')))
              i) : (Fin ℓ → A) → Prop) =
            tupBits (I A w * ∏ᶠ u : Fin m → A, F A (Fin.append w u)) := by
        intro i hu hj
        refine tupBits_congr ?_
        have hprod : prodBefore (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u')))
            (toLex (ut i)) * F A (Fin.append w (ofLex (toLex (ut i)))) =
              ∏ᶠ u : Fin m → A, F A (Fin.append w u) :=
          prodBefore_top_mul (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u'))) hu
        rw [pval, orank_eq_zero hj, pow_zero, Nat.div_one, Nat.mul_mod, Nat.mod_mod,
          ← Nat.mul_mod, mul_assoc, hprod]
      let := e₃.B.structure (e₃.inflLimit A)
      refine Formula.realize_iExs.trans ?_
      have hend : ∀ i : Fin (m + ℓ) → A,
          ((LHom.sumInl : K.sum Language.order →ᴸ
            (K.sum Language.order).sum e₃.B.lang).onFormula
              (maxTupF (fun k => Sum.inr (Fin.castAdd ℓ k)) ⊓
                minTupF fun k => Sum.inr (Fin.natAdd m k))).Realize
              (Sum.elim (Sum.elim w p) i) ↔
            (∀ c : Lex (Fin m → A), c ≤ toLex (ut i)) ∧
              ∀ c : Lex (Fin ℓ → A), toLex (jt i) ≤ c := fun i =>
        (LHom.realize_onFormula _ _).trans (Formula.realize_inf.trans (and_congr
          ((realize_maxTupF (L := K) (v := Sum.elim (Sum.elim w p) i) _).trans
            (tup_isTop_iff (t := ut i)).symm)
          ((realize_minTupF (L := K) (v := Sum.elim (Sum.elim w p) i) _).trans
            (tup_isBot_iff (t := jt i)).symm)))
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨h1, h2⟩ := Formula.realize_inf.mp hi
        obtain ⟨hu, hj⟩ := (hend i).mp h1
        have := (hrow i).mp h2
        rwa [hval i hu hj] at this
      · intro h
        obtain ⟨u, hu⟩ := Finite.exists_max (id : Lex (Fin m → A) → Lex (Fin m → A))
        obtain ⟨j₀, hj₀⟩ := Finite.exists_min (id : Lex (Fin ℓ → A) → Lex (Fin ℓ → A))
        have hu' : ∀ c : Lex (Fin m → A), c ≤ toLex (ut (Fin.append (ofLex u) (ofLex j₀))) := by
          rw [ut_append]
          exact hu
        have hj' : ∀ c : Lex (Fin ℓ → A), toLex (jt (Fin.append (ofLex u) (ofLex j₀))) ≤ c := by
          rw [jt_append]
          exact hj₀
        refine ⟨_, Formula.realize_inf.mpr ⟨(hend _).mpr ⟨hu', hj'⟩, (hrow _).mpr ?_⟩⟩
        rw [hval _ hu' hj']
        exact h)
  exact ⟨e₄, ((y₁.trans y₂).trans y₃).trans y₄, j, hj⟩

/-- **Closure under multiplication**: a product over the one tuple of length
zero. -/
theorem Dig.mul {a : ℕ} {F G : Fam K a} (hF : Dig e₀ ℓ F) (hG : Dig e₀ ℓ G) :
    Dig e₀ ℓ (fun A _ _ w => F A w * G A w) := by
  refine Dig.congr (fun A _ _ w => ?_) (Dig.prod (m := 0) (F := G) hF hG)
  rw [finprod_unique]
  exact congrArg (fun x => F A w * G A x) (funext fun k => Fin.append_left w default k)

end Closure

end Digits

end Lax366625Proofs.DescriptiveComplexity


