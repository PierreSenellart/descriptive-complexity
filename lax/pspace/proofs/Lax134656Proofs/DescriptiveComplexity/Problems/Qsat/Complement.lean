/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Problems.Qsat.Membership
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQVar QPrec QsatHolds QsatWf QsatWins)
end Lax134656Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax134656.Qsat (qsIsVar qsPrefixLt qsat)
end FirstOrder.Language

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

namespace Lax134656Proofs.DescriptiveComplexity

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
noncomputable def qsSpecCo : Lax134656.SecondOrderTransitiveClosure.SOTCSpec Lax134656.Qsat.qsat where
  B := qsBlock
  step := qsSpec.step
  src :=
    (wfF (qsIn₁ Lax134656.Qsat.qsIsVar) (qsIn₁ Lax134656.Qsat.qsPrefixLt) ⊓
        (emptyF (qsVar₁ false) ⊓ ∼(bitF (qsBit₁ false)))) ⊔
      (∼(wfF (qsIn₁ Lax134656.Qsat.qsIsVar) (qsIn₁ Lax134656.Qsat.qsPrefixLt)) ⊓ qsFalseS)
  tgt := qsFalseS

end Spec

/-! ### Reading the specification back -/

section Reading

variable {A : Type} [Lax134656.Qsat.qsat.Structure A] [LinearOrder A]

theorem qsRealize_sup₁ (ρ : qsBlock.Assignment A) (φ ψ : qsLang₁.Sentence) :
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) (φ ⊔ ψ) ↔
      (@Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) φ ∨
        @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) ψ) :=
  letI := qsBlock.structure₁ (L := qsBase) ρ
  Formula.realize_sup

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
    ((∀ x y : A, Lax134656.Qsat.QPrec x y → Lax134656.Qsat.IsQVar x ∧ Lax134656.Qsat.IsQVar y) ∧ (∀ x : A, ¬Lax134656.Qsat.QPrec x x) ∧
        (∀ x y z : A, Lax134656.Qsat.QPrec x y → Lax134656.Qsat.QPrec y z → Lax134656.Qsat.QPrec x z) ∧
        (∀ x y : A, Lax134656.Qsat.IsQVar x → Lax134656.Qsat.IsQVar y → x ≠ y → Lax134656.Qsat.QPrec x y ∨ Lax134656.Qsat.QPrec y x)) ↔ Lax134656.Qsat.QsatWf A :=
  ⟨fun h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩,
    fun h' => ⟨h'.isVar_of_prec, h'.irrefl, h'.trans, h'.total⟩⟩

/-- **The starting states**: the initial position of a well-formed instance, or
– on a malformed one – an accepting state outright. -/
theorem qsSpecCo_isSrc_iff (ρ : qsBlock.Assignment A) :
    qsSpecCo.IsSrc ρ ↔
      ((Lax134656.Qsat.QsatWf A ∧ ((∀ y : A, ¬qsSet ρ y) ∧ ¬qsUp ρ)) ∨
        (¬Lax134656.Qsat.QsatWf A ∧ ((∀ y : A, ¬qsSet ρ y) ∧ (qsUp ρ ∧ ¬qsRes ρ)))) := by
  rw [show qsSpecCo.IsSrc ρ =
    @Sentence.Realize _ A (qsBlock.structure₁ (L := qsBase) ρ) qsSpecCo.src from rfl]
  simp only [qsSpecCo, qsRealize_sup₁, qsRealize_inf₁, qsRealize_not₁, realize_wfS,
    realize_emptyS, realize_bitS, realize_qsFalseS, relMap_qsIn₁, relMap_qsVar₁, relMap_qsBit₁,
    Matrix.cons_val_zero, qsSet, qsUp]
  exact or_congr (and_congr qsatWf_iff_conj Iff.rfl) (and_congr (not_congr qsatWf_iff_conj) Iff.rfl)

end Reading

/-! ### Correctness -/

section Correctness

variable {A : Type} [Lax134656.Qsat.qsat.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
private theorem qsCoReach_eq_of_terminal {a b : qsBlock.Assignment A}
    (hna : ∀ c : qsBlock.Assignment A, ¬qsSpec.Step a c) (hab : qsSpec.Reach a b) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with h | ⟨c, hac, -⟩
  · exact h
  · exact absurd hac (hna c)

/-- **The complementary specification is correct**: its walk accepts an instance
exactly when the instance is *not* a yes-instance of QSAT. -/
theorem not_qsatHolds_iff_accepts : ¬Lax134656.Qsat.QsatHolds A ↔ qsSpecCo.Accepts A := by
  classical
  constructor
  · intro h
    by_cases hwf : Lax134656.Qsat.QsatWf A
    · have hnw : ¬Lax134656.Qsat.QsatWins (fun _ : A => False) (fun _ : A => False) := fun hw => h ⟨hwf, hw⟩
      obtain ⟨τ', -, hreach⟩ := qsSpec_run hwf
        (Set.ncard {y : A | IsQVar y ∧ ¬(fun _ : A => False) y}) (fun _ => False) (fun _ => False)
        qDownClosed_empty le_rfl False
      refine ⟨qsLift (fun _ : A => False) (fun _ : A => False) False False,
        qsLift (fun _ : A => False) τ' True
          (Lax134656.Qsat.QsatWins (fun _ : A => False) (fun _ : A => False)), ?_, ?_, hreach⟩
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
      set π := qsLift (fun _ : A => False) τ' True (Lax134656.Qsat.QsatWins (fun _ : A => False) (qsVal ρ))
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
theorem qsatCompl_sotcDefinable : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable QSATᶜ :=
  ⟨qsSpecCo, fun _ _ _ _ _ => not_qsatHolds_iff_accepts⟩

end Lax134656Proofs.DescriptiveComplexity


