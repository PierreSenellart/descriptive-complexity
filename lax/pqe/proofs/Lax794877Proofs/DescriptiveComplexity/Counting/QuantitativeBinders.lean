/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.Quantitative
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax794877Proofs.DescriptiveComplexity.QTerm
end Lax794877Proofs.DescriptiveComplexity.QTerm

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (QTerm)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Writing quantitative terms

Helpers for writing a term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`) the way it is read, and for evaluating it.

A quantifier of `DescriptiveComplexity.QTerm` binds a block of variables,
named by position in a sum type. `DescriptiveComplexity.QTerm.sumOver` and
`DescriptiveComplexity.QTerm.prodOver` bind *one* variable and hand it to the
body by name: the body is a function of the bound variable, and of the way the
variables already in scope are read under the binder. So
`sumOver fun up x => f (up y) x` is `Σx. f(y, x)`, and its value is a sum over
the elements (`DescriptiveComplexity.QTerm.eval_sumOver`).

`DescriptiveComplexity.QTerm.cond` is the choice between two terms by a
formula.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

/-- `Σx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → Lax366625.QuantitativeLogic.QTerm L δ) : Lax366625.QuantitativeLogic.QTerm L γ :=
  .sum 1 (f Sum.inl (Sum.inr 0))

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (sumOver)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

/-- `Πx. t`: the body is given the reading of the variables in scope, and the
bound variable. -/
def prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → Lax366625.QuantitativeLogic.QTerm L δ) : Lax366625.QuantitativeLogic.QTerm L γ :=
  .prod 1 (f Sum.inl (Sum.inr 0))

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (prodOver)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

/-- The choice between two terms: `s` where the formula holds, `t` where it
does not. -/
def cond (φ : L.Formula γ) (s t : Lax366625.QuantitativeLogic.QTerm L γ) : Lax366625.QuantitativeLogic.QTerm L γ :=
  .add (.mul (.ind φ) s) (.mul (.ind ∼φ) t)

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (cond)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

theorem eval_sumOver (f : ∀ {δ : Type}, (γ → δ) → δ → Lax366625.QuantitativeLogic.QTerm L δ) (v : γ → A) :
    (sumOver f).eval v =
      ∑ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finsum_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_sumOver)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

theorem eval_prodOver (f : ∀ {δ : Type}, (γ → δ) → δ → Lax366625.QuantitativeLogic.QTerm L δ) (v : γ → A) :
    (prodOver f).eval v =
      ∏ᶠ a : A, (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v fun _ => a) :=
  (finprod_comp_equiv (Equiv.funUnique (Fin 1) A).symm
    (f := fun w : Fin 1 → A =>
      (f (δ := γ ⊕ Fin 1) Sum.inl (Sum.inr 0)).eval (Sum.elim v w))).symm

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_prodOver)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

open Classical in
theorem eval_cond (φ : L.Formula γ) (s t : Lax366625.QuantitativeLogic.QTerm L γ) (v : γ → A) :
    (cond φ s t).eval v = if φ.Realize v then s.eval v else t.eval v := by
  by_cases h : φ.Realize v <;> simp [cond, Lax366625.QuantitativeLogic.QTerm.eval, h]

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_cond)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

open Classical in
theorem eval_ind (φ : L.Formula γ) (v : γ → A) :
    (Lax366625.QuantitativeLogic.QTerm.ind φ : Lax366625.QuantitativeLogic.QTerm L γ).eval v = if φ.Realize v then 1 else 0 :=
  rfl

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_ind)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

theorem eval_mul (s t : Lax366625.QuantitativeLogic.QTerm L γ) (v : γ → A) : (Lax366625.QuantitativeLogic.QTerm.mul s t).eval v = s.eval v * t.eval v :=
  rfl

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_mul)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

theorem eval_add (s t : Lax366625.QuantitativeLogic.QTerm L γ) (v : γ → A) : (Lax366625.QuantitativeLogic.QTerm.add s t).eval v = s.eval v + t.eval v :=
  rfl

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_add)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

theorem eval_const (n : ℕ) (v : γ → A) : (Lax366625.QuantitativeLogic.QTerm.const n : Lax366625.QuantitativeLogic.QTerm L γ).eval v = n :=
  rfl

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_const)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {γ : Type}

variable {A : Type} [L.Structure A]

end QTerm

end Lax794877Proofs.DescriptiveComplexity


