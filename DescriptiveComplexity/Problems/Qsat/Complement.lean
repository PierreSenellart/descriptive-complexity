/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Membership

/-!
# The complement of QSAT is in PSPACE

The walk of `DescriptiveComplexity.Problems.Qsat.Membership` does not *search* for
an accepting computation: it is deterministic, and its single run *computes* the
value of the quantified formula. That is what makes the complement of QSAT as
cheap as QSAT itself – the walk is the same, only the accepting condition
changes.

`DescriptiveComplexity.qsSpecCo` therefore reuses
`DescriptiveComplexity.qsSpec`'s transition sentence verbatim and accepts the
returning state at the empty branch carrying the value **false**. One point needs
care: a malformed instance is a no-instance of QSAT, hence a *yes*-instance of
its complement, and the run of the walk says nothing about it – on a malformed
prefix neither the next nor the last variable of a position need exist. So the
source sentence has a second disjunct, which starts a malformed instance
directly in an accepting state.

This is the whole content of `PSPACE = coPSPACE`
(`DescriptiveComplexity.PSpaceCompl`): every SO(TC) definable problem reduces to
QSAT, and complementing a reduction is free.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The complementary specification -/

section Spec

/-- The accepting states of the complementary walk: back at the empty branch,
returning the value `false`. -/
noncomputable def qsFalseS : qsLang₁.Sentence :=
  emptyF (qsVar₁ false) ⊓ (bitF (qsBit₁ false) ⊓ ∼(bitF (qsBit₁ true)))

/-- **The complementary specification**: the depth-first evaluation of the game
tree again – the same transition sentence – accepting when the value computed is
`false`, or when the instance is malformed, in which case the walk starts where
it would have ended. -/
noncomputable def qsSpecCo : SOTCSpec Language.qsat where
  B := qsBlock
  step := qsSpec.step
  src :=
    (wfF (qsIn₁ qsIsVar) (qsIn₁ qsPrefixLt) ⊓
        (emptyF (qsVar₁ false) ⊓ ∼(bitF (qsBit₁ false)))) ⊔
      (∼(wfF (qsIn₁ qsIsVar) (qsIn₁ qsPrefixLt)) ⊓ qsFalseS)
  tgt := qsFalseS

end Spec

/-! ### Reading the specification back -/

section Reading

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A]

theorem qsRealize_sup₁ (ρ : qsBlock.Assignment A) (φ ψ : qsLang₁.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) (φ ⊔ ψ) ↔
      (@Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) φ ∨
        @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) ψ) :=
  letI := qsBlock.structure₁ (L := qsBase) ρ
  Formula.realize_sup

/-- **The complementary walk is the same walk.** -/
theorem qsSpecCo_step_iff (ρ σ : qsBlock.Assignment A) :
    qsSpecCo.Step ρ σ ↔ qsSpec.Step ρ σ :=
  Iff.rfl

theorem qsSpecCo_reach_iff (ρ σ : qsBlock.Assignment A) :
    qsSpecCo.Reach ρ σ ↔ qsSpec.Reach ρ σ :=
  Iff.rfl

theorem realize_qsFalseS (ρ : qsBlock.Assignment A) :
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) qsFalseS ↔
      ((∀ y : A, ¬qsSet ρ y) ∧ (qsUp ρ ∧ ¬qsRes ρ)) := by
  simp only [qsFalseS, qsRealize_inf₁, qsRealize_not₁, realize_emptyS, realize_bitS,
    relMap_qsVar₁, relMap_qsBit₁, Matrix.cons_val_zero, qsSet, qsUp, qsRes]

/-- **The accepting states**: back at the initial position, returning `false`. -/
theorem qsSpecCo_isTgt_iff (ρ : qsBlock.Assignment A) :
    qsSpecCo.IsTgt ρ ↔ ((∀ y : A, ¬qsSet ρ y) ∧ (qsUp ρ ∧ ¬qsRes ρ)) :=
  realize_qsFalseS ρ

omit [LinearOrder A] in
private theorem qsatWf_iff_conj :
    ((∀ x y : A, QPrec x y → IsQVar x ∧ IsQVar y) ∧ (∀ x : A, ¬QPrec x x) ∧
        (∀ x y z : A, QPrec x y → QPrec y z → QPrec x z) ∧
        (∀ x y : A, IsQVar x → IsQVar y → x ≠ y → QPrec x y ∨ QPrec y x)) ↔ QsatWf A :=
  ⟨fun h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩,
    fun h' => ⟨h'.isVar_of_prec, h'.irrefl, h'.trans, h'.total⟩⟩

/-- **The starting states**: the initial position of a well-formed instance, or
– on a malformed one – an accepting state outright. -/
theorem qsSpecCo_isSrc_iff (ρ : qsBlock.Assignment A) :
    qsSpecCo.IsSrc ρ ↔
      ((QsatWf A ∧ ((∀ y : A, ¬qsSet ρ y) ∧ ¬qsUp ρ)) ∨
        (¬QsatWf A ∧ ((∀ y : A, ¬qsSet ρ y) ∧ (qsUp ρ ∧ ¬qsRes ρ)))) := by
  rw [show qsSpecCo.IsSrc ρ =
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) qsSpecCo.src from rfl]
  simp only [qsSpecCo, qsRealize_sup₁, qsRealize_inf₁, qsRealize_not₁, realize_wfS,
    realize_emptyS, realize_bitS, realize_qsFalseS, relMap_qsIn₁, relMap_qsVar₁, relMap_qsBit₁,
    Matrix.cons_val_zero, qsSet, qsUp]
  exact or_congr (and_congr qsatWf_iff_conj Iff.rfl) (and_congr (not_congr qsatWf_iff_conj) Iff.rfl)

end Reading

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
private theorem qsCoReach_eq_of_terminal {a b : qsBlock.Assignment A}
    (hna : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step a c) (hab : qsSpec.Reach a b) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with h | ⟨c, hac, -⟩
  · exact h
  · exact absurd hac (hna c)

/-- **The complementary specification is correct**: its walk accepts an instance
exactly when the instance is *not* a yes-instance of QSAT. -/
theorem not_qsatHolds_iff_accepts : ¬QsatHolds A ↔ qsSpecCo.Accepts A := by
  classical
  constructor
  · intro h
    by_cases hwf : QsatWf A
    · have hnw : ¬QsatWins (fun _ : A => False) (fun _ : A => False) := fun hw => h ⟨hwf, hw⟩
      obtain ⟨τ', -, hreach⟩ := qsSpec_run hwf
        (Set.ncard {y : A | IsQVar y ∧ ¬(fun _ : A => False) y}) (fun _ => False) (fun _ => False)
        qDownClosed_empty le_rfl False
      refine ⟨qsLift (fun _ : A => False) (fun _ : A => False) False False,
        qsLift (fun _ : A => False) τ' True
          (QsatWins (fun _ : A => False) (fun _ : A => False)), ?_, ?_, hreach⟩
      · exact (qsSpecCo_isSrc_iff _).mpr (Or.inl ⟨hwf, fun _ => id, id⟩)
      · exact (qsSpecCo_isTgt_iff _).mpr ⟨fun _ => id, trivial, hnw⟩
    · refine ⟨qsLift (fun _ : A => False) (fun _ : A => False) True False,
        qsLift (fun _ : A => False) (fun _ : A => False) True False, ?_, ?_,
        Relation.ReflTransGen.refl⟩
      · exact (qsSpecCo_isSrc_iff _).mpr (Or.inr ⟨hwf, fun _ => id, trivial, id⟩)
      · exact (qsSpecCo_isTgt_iff _).mpr ⟨fun _ => id, trivial, id⟩
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    rcases (qsSpecCo_isSrc_iff ρ).mp hsrc with ⟨hwf, hempty, hup⟩ | ⟨hwf, -⟩
    · obtain ⟨hempty', hup', hres'⟩ := (qsSpecCo_isTgt_iff σ).mp htgt
      have hρ : ρ = qsLift (fun _ : A => False) (qsVal ρ) False (qsRes ρ) :=
        qsAssignment_ext (fun a => iff_of_false (hempty a) id) (fun _ => Iff.rfl)
          (iff_of_false hup id) Iff.rfl
      obtain ⟨τ', -, hrun⟩ := qsSpec_run hwf
        (Set.ncard {y : A | IsQVar y ∧ ¬(fun _ : A => False) y}) (fun _ => False) (qsVal ρ)
        qDownClosed_empty le_rfl (qsRes ρ)
      rw [← hρ] at hrun
      set π := qsLift (fun _ : A => False) τ' True (QsatWins (fun _ : A => False) (qsVal ρ))
        with hπ
      have hnπ : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step π c :=
        fun c => qsSpec_no_step_of_empty (fun _ => id) trivial
      have hnσ : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step σ c :=
        fun c => qsSpec_no_step_of_empty hempty' hup'
      have hru : Relator.RightUnique (fun ρ' σ' : qsBlock.Assignment A => qsSpec.Step ρ' σ') :=
        @fun _ _ _ h h' => qsSpec_step_unique hwf h h'
      have hσπ : σ = π := by
        rcases Relation.ReflTransGen.total_of_right_unique hru hreach hrun with h | h
        · exact qsCoReach_eq_of_terminal hnσ h
        · exact (qsCoReach_eq_of_terminal hnπ h).symm
      rintro ⟨-, hw⟩
      refine hres' ?_
      rw [hσπ, hπ]
      exact qsatWins_congr hw _ fun _ hy => hy.elim
    · exact fun hh => hwf hh.1

end Correctness

/-- **The complement of QSAT is SO(TC) definable**: the walk that decides QSAT
is deterministic, so reading its answer the other way round decides the
complement. -/
theorem qsatCompl_sotcDefinable : SOTCDefinable QSATᶜ :=
  ⟨qsSpecCo, fun _ _ _ _ _ => not_qsatHolds_iff_accepts⟩

/-- **The complement of QSAT is in PSPACE**, i.e. `QSAT ∈ coPSPACE`. -/
theorem qsatCompl_mem_PSPACE : QSATᶜ ∈ PSPACE :=
  qsatCompl_sotcDefinable

end DescriptiveComplexity
