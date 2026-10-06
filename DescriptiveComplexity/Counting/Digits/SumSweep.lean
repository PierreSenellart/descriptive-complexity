/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Digits.Closure

/-!
# Closure under sums over the tuples of the structure

`DescriptiveComplexity.Digits.Dig.sum`: if the digits of a family `F` of
numbers, with parameters `w̄` and `ū`, can be added to a tower, so can the
digits of `Σū. F(w̄, ū)`.

The sum is an iterated addition, computed by a sweep
(`DescriptiveComplexity.Digits.sweep`) along the tuples `ū` in lexicographic
order: the row of `ū` holds the digits of the sum of `F` up to `ū`
(`DescriptiveComplexity.Digits.sumFam`), and is the sum, by carry lookahead,
of the row before it and of `F(w̄, ū)`
(`DescriptiveComplexity.Digits.sumTheta`). The answer is the row of the last
tuple.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

variable {K : Language.{0, 0}}

/-! ### Variables in two blocks -/

/-- The arguments of a relation about parameters and an index, as the
variables of a formula. -/
def u2 {a m : ℕ} : Fin (a + m) → Fin a ⊕ Fin m :=
  fun k => Fin.addCases Sum.inl Sum.inr k

theorem elim_comp_u2 {A : Type} {a m : ℕ} (w : Fin a → A) (u : Fin m → A) :
    (fun k => Sum.elim w u (u2 k)) = Fin.append w u := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp [u2]

/-! ### The lexicographic order on tuples, as sweep data -/

section LexData

variable {e : StepDef (K.sum Language.order)} {m : ℕ}

variable (e m) in
/-- “The tuple is the least one.” -/
noncomputable def lexBotF : ((K.sum Language.order).sum e.B.lang).Formula (Fin m) :=
  LHom.sumInl.onFormula (minTupF id)

variable (e m) in
/-- “The second tuple covers the first.” -/
noncomputable def lexCovF : ((K.sum Language.order).sum e.B.lang).Formula (Fin m ⊕ Fin m) :=
  LHom.sumInl.onFormula (succTupF Sum.inl Sum.inr)

variable {A : Type} [K.Structure A] [LinearOrder A]

theorem realize_lexBotF (i : Fin m → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (lexBotF e m) i) ↔
      ∀ c : Lex (Fin m → A), toLex i ≤ c := by
  let := e.B.structure (e.inflLimit A)
  exact (LHom.realize_onFormula
    (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) _).trans
    ((realize_minTupF (L := K) (v := i) id).trans (tup_isBot_iff (t := i)).symm)

theorem realize_lexCovF (i₀ i : Fin m → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (lexCovF e m) (Sum.elim i₀ i)) ↔
      toLex i₀ ⋖ toLex i := by
  let := e.B.structure (e.inflLimit A)
  exact (LHom.realize_onFormula
    (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) _).trans
    ((realize_succTupF (L := K) (v := Sum.elim i₀ i) Sum.inl Sum.inr).trans
      (tupSucc_iff_covBy (t := i₀) (t' := i)))

end LexData

/-! ### The rows: partial sums -/

/-- The sum of a family up to a tuple, in lexicographic order: a family with
that tuple as further parameters. -/
noncomputable def sumFam {a m : ℕ} (F : Fam K (a + m)) : Fam K (a + m) :=
  fun A _ _ x => sumUpTo
    (fun u' : Lex (Fin m → A) => F A (Fin.append (fun k => x (Fin.castAdd m k)) (ofLex u')))
    (toLex fun k => x (Fin.natAdd a k))

section Theta

variable {e : StepDef (K.sum Language.order)} {a m ℓ : ℕ}

/-- The ordered vocabulary, read in the vocabulary of a sweep over a tower. -/
abbrev sweepHom (e : StepDef (K.sum Language.order)) (a q ℓ : ℕ) :
    K.sum Language.order →ᴸ ((K.sum Language.order).sum e.B.lang).sum (sweepBlock a q ℓ).lang :=
  (LHom.sumInl : (K.sum Language.order).sum e.B.lang →ᴸ
    ((K.sum Language.order).sum e.B.lang).sum (sweepBlock a q ℓ).lang).comp LHom.sumInl

/-- **The row of a tuple**: the digits of the family at the least tuple, and
otherwise the sum of the row before and of the digits of the family. -/
noncomputable def sumTheta (jF : e.B.lang.Relations (a + m + ℓ)) :
    (((K.sum Language.order).sum e.B.lang).sum (sweepBlock a m ℓ).lang).Formula
      ((Fin a ⊕ Fin m) ⊕ Fin ℓ) :=
  ((sweepHom e a m ℓ).onFormula (minTupF (Sum.inl ∘ Sum.inr)) ⊓
      LHom.sumInl.onFormula (numAt jF u2)) ⊔
    exMid (m := m)
      ((sweepHom e a m ℓ).onFormula
          (succTupF (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl ∘ Sum.inr)) ⊓
        addF (sweepHom e a m ℓ)
          (rowAt (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) Sum.inr)
          (weaken (LHom.sumInl.onFormula (numAt jF u2))))

theorem realize_sumTheta {jF : e.B.lang.Relations (a + m + ℓ)} {F : Fam K (a + m)}
    (hjF : e.Computes jF (digRel ℓ F)) (A : Type) [K.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] (ρ : (sweepBlock a m ℓ).Assignment A) (w : Fin a → A) (i : Fin m → A)
    (p : Fin ℓ → A) :
    (@Formula.Realize _ A
        (@SOBlock.structure₁ ((K.sum Language.order).sum e.B.lang) (sweepBlock a m ℓ) A
          (ctxStr e A) ρ) _ (sumTheta jF) (Sum.elim (Sum.elim w i) p)) ↔
      ((∀ c : Lex (Fin m → A), toLex i ≤ c) ∧ tupBits (F A (Fin.append w i)) p) ∨
        ∃ u₀ : Fin m → A, toLex u₀ ⋖ toLex i ∧
          AddSet (fun p' => ρ true (j3 w u₀ p')) (tupBits (F A (Fin.append w i))) p := by
  have hF : ∀ p' : Fin ℓ → A,
      (@Formula.Realize _ A (ctxStr e A) _ (numAt jF u2) (Sum.elim (Sum.elim w i) p')) ↔
        tupBits (F A (Fin.append w i)) p' := fun p' =>
    (realize_numAt hjF A u2 (Sum.elim w i) p').trans
      (iff_of_eq (congrArg (fun x => tupBits (F A x) p') (elim_comp_u2 w i)))
  have hrow := fun (u₀ : Fin m → A) (p' : Fin ℓ → A) =>
    @realize_rowAt ((K.sum Language.order).sum e.B.lang) a m ℓ _ A (ctxStr e A) ρ
      (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) Sum.inr
      (Sum.elim (Sum.elim (Sum.elim w i) u₀) p')
  let := e.B.structure (e.inflLimit A)
  let := (sweepBlock a m ℓ).structure ρ
  have : (sweepHom e a m ℓ).IsExpansionOn A := isExpansionOn_comp _ _ A
  have hl : ∀ {α : Type} (φ : ((K.sum Language.order).sum e.B.lang).Formula α) (v : α → A),
      ((LHom.sumInl : (K.sum Language.order).sum e.B.lang →ᴸ
        ((K.sum Language.order).sum e.B.lang).sum (sweepBlock a m ℓ).lang).onFormula φ).Realize
          v ↔ φ.Realize v :=
    fun φ v => LHom.realize_onFormula _ φ
  refine Formula.realize_sup.trans (or_congr ?_ ?_)
  · refine Formula.realize_inf.trans (and_congr ?_ ((hl _ _).trans (hF p)))
    exact (realize_lift (sweepHom e a m ℓ) _ _).trans
      ((realize_minTupF (L := K) (v := Sum.elim (Sum.elim w i) p) (Sum.inl ∘ Sum.inr)).trans
        (tup_isBot_iff (t := i)).symm)
  · refine (realize_exMid _ (Sum.elim w i) p).trans (exists_congr fun u₀ => ?_)
    refine Formula.realize_inf.trans (and_congr ?_ ?_)
    · exact (realize_lift (sweepHom e a m ℓ) _ _).trans
        ((realize_succTupF (L := K) (v := Sum.elim (Sum.elim (Sum.elim w i) u₀) p)
          (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl ∘ Sum.inr)).trans
          (tupSucc_iff_covBy (t := u₀) (t' := i)))
    · refine (realize_addF (sweepHom e a m ℓ) _ _ (Sum.elim (Sum.elim w i) u₀) p).trans
        (iff_of_eq (congrArg₂ (fun X Y => AddSet X Y p)
          (funext fun p' => propext (hrow u₀ p'))
          (funext fun p' => propext ?_)))
      exact (realize_weaken _ (Sum.elim w i) u₀ p').trans ((hl _ _).trans (hF p'))

end Theta

/-! ### Closure -/

section Closure

variable {e₀ : StepDef (K.sum Language.order)} {ℓ : ℕ}

/-- **Closure under sums over tuples.** -/
theorem Dig.sum {a m : ℕ} {F : Fam K (a + m)} (hF : Dig e₀ ℓ F) :
    Dig e₀ ℓ (fun A _ _ w => ∑ᶠ u : Fin m → A, F A (Fin.append w u)) := by
  intro e x
  obtain ⟨e₁, y₁, jF, hjF⟩ := hF e x
  obtain ⟨e₂, y₂, jR, hjR⟩ := exists_ext_of_sweep e₁ (lexBotF e₁ m) (lexCovF e₁ m)
    (sumTheta jF) (digRel ℓ (sumFam F)) (fun A _ _ _ _ w i p => by
      have key := @inflLimit_sweep _ a m ℓ A (ctxStr e₁ A) (Lex (Fin m → A)) _ _ toLex
        (lexBotF e₁ m) (lexCovF e₁ m) (sumTheta jF) realize_lexBotF realize_lexCovF
        (fun w u R p => ((∀ c, u ≤ c) ∧ tupBits (F A (Fin.append w (ofLex u))) p) ∨
          ∃ u₀, u₀ ⋖ u ∧ AddSet (R u₀) (tupBits (F A (Fin.append w (ofLex u)))) p)
        (fun w u => tupBits (sumUpTo (fun u' => F A (Fin.append w (ofLex u'))) u))
        (by
          intro w u R hR
          funext p
          refine propext ?_
          by_cases hb : ∀ c, u ≤ c
          · rw [sumUpTo_bot _ hb]
            exact ⟨fun h => h.elim (fun h' => h'.2)
              fun ⟨u₀, h₀, _⟩ => absurd h₀.lt (not_lt.mpr (hb u₀)), fun h => Or.inl ⟨hb, h⟩⟩
          · have hadd : ∀ u₀, u₀ ⋖ u →
                AddSet (R u₀) (tupBits (F A (Fin.append w (ofLex u)))) =
                  tupBits (sumUpTo (fun u' => F A (Fin.append w (ofLex u'))) u) := by
              intro u₀ h₀
              rw [hR u₀ h₀.lt, addSet_tupBits, sumUpTo_covBy _ h₀]
            obtain ⟨u₀, h₀⟩ := exists_covBy_of_not_min hb
            constructor
            · rintro (⟨h, -⟩ | ⟨u₁, h₁, hs⟩)
              · exact absurd h hb
              · rwa [hadd u₁ h₁] at hs
            · intro h
              exact Or.inr ⟨u₀, h₀, by rwa [hadd u₀ h₀]⟩)
        (fun ρ w i p => (realize_sumTheta hjF A ρ w i p).trans
          (or_congr Iff.rfl ⟨fun ⟨u₀, h⟩ => ⟨toLex u₀, h⟩, fun ⟨u₀, h⟩ => ⟨ofLex u₀, h⟩⟩))
        w i p
      refine key.trans (iff_of_eq ?_)
      simp only [digRel, sumFam, j3, Fin.append_left, Fin.append_right])
  obtain ⟨e₃, y₃, j, hj⟩ := exists_ext_of_num e₂
    (Formula.iExs (Fin m) (LHom.sumInl.onFormula (maxTupF Sum.inr) ⊓
      ctxAt jR (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
        fun k => Sum.inl (Sum.inr k))))
    (fun A _ _ w => ∑ᶠ u : Fin m → A, F A (Fin.append w u))
    (fun A _ _ _ _ w p => by
      have hrow : ∀ u : Fin m → A,
          (@Formula.Realize _ A (ctxStr e₂ A) _
            (ctxAt jR (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
              fun k => Sum.inl (Sum.inr k))) (Sum.elim (Sum.elim w p) u)) ↔
            tupBits (sumUpTo (fun u' : Lex (Fin m → A) => F A (Fin.append w (ofLex u')))
              (toLex u)) p := by
        intro u
        refine (realize_ctxAt hjR A _ _).trans (iff_of_eq ?_)
        have hx : (fun k => Sum.elim (Sum.elim w p) u
            (Fin.append (Fin.append (fun k => Sum.inl (Sum.inl k)) Sum.inr)
              (fun k => Sum.inl (Sum.inr k)) k)) = j3 w u p :=
          (comp_append _ _ _).trans
            (congrArg (fun f => Fin.append f _) (comp_append _ _ _))
        rw [hx]
        simp only [digRel, sumFam, j3, Fin.append_left, Fin.append_right]
      let := e₂.B.structure (e₂.inflLimit A)
      refine Formula.realize_iExs.trans ?_
      have hmax : ∀ u : Fin m → A,
          ((LHom.sumInl : K.sum Language.order →ᴸ
            (K.sum Language.order).sum e₂.B.lang).onFormula (maxTupF Sum.inr)).Realize
              (Sum.elim (Sum.elim w p) u) ↔ ∀ c : Lex (Fin m → A), c ≤ toLex u := fun u =>
        (LHom.realize_onFormula _ _).trans
          ((realize_maxTupF (L := K) (v := Sum.elim (Sum.elim w p) u) Sum.inr).trans
            (tup_isTop_iff (t := u)).symm)
      constructor
      · rintro ⟨u, hu⟩
        obtain ⟨h1, h2⟩ := Formula.realize_inf.mp hu
        have := (hrow u).mp h2
        rwa [sumUpTo_top _ ((hmax u).mp h1)] at this
      · intro h
        obtain ⟨u, hu⟩ := Finite.exists_max (id : Lex (Fin m → A) → Lex (Fin m → A))
        have hu' : ∀ c : Lex (Fin m → A), c ≤ toLex (ofLex u) := hu
        refine ⟨ofLex u, Formula.realize_inf.mpr ⟨(hmax _).mpr hu', (hrow _).mpr ?_⟩⟩
        rw [sumUpTo_top _ hu']
        exact h)
  exact ⟨e₃, (y₁.trans y₂).trans y₃, j, hj⟩

end Closure

end Digits

end DescriptiveComplexity
