/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Sat
import Lax280166Proofs.DescriptiveComplexity.Counting.Class
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
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

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# #SAT: counting the models of a CNF formula

The counting version of `DescriptiveComplexity.SAT`, on the same vocabulary: the
number of *models* of a CNF formula ([Valiant 1979][valiant1979complexity]).

A model is a set of true variables satisfying every clause, and it is a set of
variables *of the formula*: an element that occurs in no clause is not a
variable (`DescriptiveComplexity.SatOccurs`), and a model does not contain it
(`DescriptiveComplexity.SatModel`). Without that convention every clause element and
every unused element of an instance would double the count, where the decision
problem can afford to leave them unconstrained.

`DescriptiveComplexity.SharpSAT` is the bundled counting problem; its support is SAT
(`DescriptiveComplexity.sharpSat_support_iff`), and it belongs to `#P`
(`DescriptiveComplexity.sharpSat_mem_sharpP`), the models being the witnesses of the
`Σ₁` definition of SAT with one conjunct added to the kernel. Its hardness is
in `DescriptiveComplexity.Problems.Sat.CountingHardness`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Models

variable (A : Type) [Lax904597.Sat.sat.Structure A]

variable {A}

/-- A satisfying assignment restricts to a model: only the values at the
variables of the formula matter. -/
theorem satModel_restrict {ν : A → Prop}
    (h : ∀ c : A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x : A, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x)) :
    Lax366625.CountingSat.SatModel A fun x => ν x ∧ Lax366625.CountingSat.SatOccurs A x := by
  refine ⟨fun c hc => ?_, fun x hx => hx.2⟩
  obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := h c hc
  · exact ⟨x, Or.inl ⟨hp, hx, c, hc, Or.inl hp⟩⟩
  · exact ⟨x, Or.inr ⟨hn, fun h' => hx h'.1⟩⟩

/-- A CNF formula is satisfiable exactly when it has a model. -/
theorem satisfiable_iff_exists_satModel : Lax904597.Sat.Satisfiable A ↔ ∃ ν : A → Prop, Lax366625.CountingSat.SatModel A ν :=
  ⟨fun ⟨_, hν⟩ => ⟨_, satModel_restrict hν⟩, fun ⟨ν, hν⟩ => ⟨ν, hν.1⟩⟩

end Models

/-! ### The kernel -/

section Kernel

open Lax904597.SecondOrder.SOBlock

/-- Kernel conjunct: the truth assignment only holds of variables of the
formula, i.e., of elements occurring in a clause. -/
noncomputable def satVarKernel : satSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ kNuSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ kIsClSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            (FirstOrder.Language.Relations.formula₂ kPosSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))) ⊔
              FirstOrder.Language.Relations.formula₂ kNegSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))))))

/-- The first-order kernel of #SAT: the kernel of SAT, and the truth assignment
only holds of variables of the formula. -/
noncomputable def sharpSatKernel : satSOLang.Sentence :=
  satKernel ⊓ satVarKernel

/-- Unary relations, as assignments of the truth-assignment block. -/
def satAssignEquiv (A : Type) : (A → Prop) ≃ satAssignBlock.Assignment A where
  toFun ν := fun _ x => ν (x ⟨0, Nat.one_pos⟩)
  invFun ρ := fun a => ρ satNuSym.1 fun _ => a
  left_inv _ := rfl
  right_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j =>
      congrArg x (@Subsingleton.elim (Fin 1) _ _ _))

/-- Realization of the variable conjunct: the assignment holds only of
variables of the formula. -/
theorem realize_satVarKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) satVarKernel) ↔
      ∀ x : A, (satAssignEquiv A).symm ρ x → Lax366625.CountingSat.SatOccurs A x := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [satVarKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h x hx
    obtain ⟨c, hc, hor⟩ := h (fun _ => x) hx
    exact ⟨c 0, hc, hor⟩
  · intro h x hx
    obtain ⟨c, hc, hor⟩ := h (x 0) hx
    exact ⟨fun _ => c, hc, hor⟩

/-- Realization of the kernel of #SAT: the assignment is a model. -/
theorem realize_sharpSatKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpSatKernel) ↔
      Lax366625.CountingSat.SatModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_satKernel ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpSatKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

end Kernel

/-! ### The counting problem -/

/-- The number of models of a CNF formula is the number of witnesses of the
kernel of #SAT. -/
theorem card_satModel_eq_witnessCount (A : Type) [Lax904597.Sat.sat.Structure A] :
    Nat.card {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} = Lax366625.WitnessCounting.witnessCount satAssignBlock sharpSatKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpSatKernel, Equiv.symm_apply_apply])

/-- **#SAT**: the number of models of a CNF formula. -/
noncomputable def SharpSAT : Lax366625.CountingProblems.CountingProblem Lax904597.Sat.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @Lax366625.CountingSat.SatModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_satModel_eq_witnessCount A, card_satModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpSatKernel e

theorem sharpSat_apply (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpSAT A = Nat.card {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} :=
  rfl

/-- **The support of #SAT is SAT**: on a finite structure, the number of models
is positive exactly when the formula is satisfiable. -/
theorem sharpSat_support_iff (A : Type) [Lax904597.Sat.sat.Structure A] [Finite A] :
    SharpSAT.support A ↔ Lax904597.Sat.SAT A := by
  rw [CountingProblem.support_iff, sharpSat_apply, Nat.card_pos_iff]
  refine Iff.trans ?_ satisfiable_iff_exists_satModel.symm
  exact ⟨fun ⟨⟨ν, hν⟩, _⟩ => ⟨ν, hν⟩, fun ⟨ν, hν⟩ => ⟨⟨⟨ν, hν⟩⟩, inferInstance⟩⟩

end Lax280166Proofs.DescriptiveComplexity


