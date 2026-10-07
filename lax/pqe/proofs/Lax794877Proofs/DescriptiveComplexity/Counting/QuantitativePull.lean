/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.Quantitative
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
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

namespace Lax794877Proofs.DescriptiveComplexity.FOInterpretation
end Lax794877Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax794877Proofs.DescriptiveComplexity.QTerm
end Lax794877Proofs.DescriptiveComplexity.QTerm

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (QTerm)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Pulling a quantitative term back through an interpretation

A term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`) over the target vocabulary of an
interpretation `I` becomes a term over its source vocabulary, with the same
value: `DescriptiveComplexity.QTerm.pull` and
`DescriptiveComplexity.QTerm.eval_pull`. A formula is pulled back as formulas
are (`DescriptiveComplexity.FOInterpretation.pull`); a sum or a product over
the `n`-tuples of the interpreted universe, which is `Tag × A ^ d`, becomes a
finite sum or product over the assignments of tags to the `n` variables, of a
sum or product over `n · d` elements of `A`.

This is what closes FP under parsimonious reductions
(`DescriptiveComplexity.Counting.FP`), the least fixed point being pulled back
as for PTIME (`DescriptiveComplexity.lfpAssign_pull`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

/-- The sum of a list of terms. -/
def bigAdd : List (Lax366625.QuantitativeLogic.QTerm L α) → Lax366625.QuantitativeLogic.QTerm L α
  | [] => Lax366625.QuantitativeLogic.QTerm.const 0
  | t :: l => Lax366625.QuantitativeLogic.QTerm.add t (bigAdd l)

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (bigAdd)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

/-- The product of a list of terms. -/
def bigMul : List (Lax366625.QuantitativeLogic.QTerm L α) → Lax366625.QuantitativeLogic.QTerm L α
  | [] => Lax366625.QuantitativeLogic.QTerm.const 1
  | t :: l => Lax366625.QuantitativeLogic.QTerm.mul t (bigMul l)

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (bigMul)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

theorem eval_bigAdd {A : Type} [L.Structure A] (l : List (Lax366625.QuantitativeLogic.QTerm L α)) (v : α → A) :
    (bigAdd l).eval v = (l.map fun t => t.eval v).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [bigAdd, Lax366625.QuantitativeLogic.QTerm.eval, ih, List.map_cons, List.sum_cons]

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_bigAdd)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

theorem eval_bigMul {A : Type} [L.Structure A] (l : List (Lax366625.QuantitativeLogic.QTerm L α)) (v : α → A) :
    (bigMul l).eval v = (l.map fun t => t.eval v).prod := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [bigMul, Lax366625.QuantitativeLogic.QTerm.eval, ih, List.map_cons, List.prod_cons]

end QTerm

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_bigMul)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}} {α : Type}

end QTerm

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

/-- The pullback of a formula with free variables through an interpretation:
each variable becomes `d` variables, its tag being given. -/
noncomputable def FOInterpretation.pullFormula (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {α : Type}
    (φ : L₂.Formula α) (τ : α → Tag) : L₁.Formula (α × Fin d) :=
  (I.pull (φ : L₂.BoundedFormula α 0) (Sum.elim τ Fin.elim0)).relabel
    fun p : (α ⊕ Fin 0) × Fin d =>
      (Sum.elim (fun a => (a, p.2)) (fun z => z.elim0) p.1 : α × Fin d)

end Pull

end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax794877Proofs.DescriptiveComplexity.FOInterpretation (pullFormula)

end Lax904597.Interpretations.FOInterpretation

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

theorem FOInterpretation.realize_pullFormula (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A : Type}
    [L₁.Structure A] {α : Type} (φ : L₂.Formula α) (τ : α → Tag) (w : α × Fin d → A) :
    (I.pullFormula φ τ).Realize w ↔ φ.Realize (M := I.Map A) (I.liftEnv τ w) := by
  rw [FOInterpretation.pullFormula, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula α 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

end Pull

end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax794877Proofs.DescriptiveComplexity.FOInterpretation (realize_pullFormula)

end Lax904597.Interpretations.FOInterpretation

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

/-- The variables of a pulled-back quantifier block: the `d` coordinates of
each of the `n` bound variables, laid out as one block of `n * d`. -/
def blockRelabel {α : Type} {n : ℕ} : (α ⊕ Fin n) × Fin d → (α × Fin d) ⊕ Fin (n * d)
  | (.inl a, j) => .inl (a, j)
  | (.inr i, j) => .inr (finProdFinEquiv (i, j))

/-- **The pullback of a term through an interpretation.** -/
noncomputable def QTerm.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) :
    ∀ {α : Type}, Lax366625.QuantitativeLogic.QTerm L₂ α → (α → Tag) → Lax366625.QuantitativeLogic.QTerm L₁ (α × Fin d)
  | _, .ind φ, τ => .ind (I.pullFormula φ τ)
  | _, .const s, _ => .const s
  | _, .add s t, τ => .add ((pull I s) τ) ((pull I t) τ)
  | _, .mul s t, τ => .mul ((pull I s) τ) ((pull I t) τ)
  | _, .sum n t, τ => QTerm.bigAdd ((allTagAssign Tag n).map fun g =>
      .sum (n * d) (((pull I t) (Sum.elim τ g)).relabel blockRelabel))
  | _, .prod n t, τ => QTerm.bigMul ((allTagAssign Tag n).map fun g =>
      .prod (n * d) (((pull I t) (Sum.elim τ g)).relabel blockRelabel))

end Pull

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (pull)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

/-- The tuples of points of the interpreted universe: an assignment of tags,
and one block of coordinates. -/
def blockEquiv (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (A : Type) (n : ℕ) :
    (Fin n → Tag) × (Fin (n * d) → A) ≃ (Fin n → I.Map A) where
  toFun p := fun i => (p.1 i, fun j => p.2 (finProdFinEquiv (i, j)))
  invFun y := (fun i => (y i).1, fun m => (y (finProdFinEquiv.symm m).1).2
    (finProdFinEquiv.symm m).2)
  left_inv p := Prod.ext rfl (funext fun m => by
    change p.2 (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) = p.2 m
    rw [Prod.mk.eta, Equiv.apply_symm_apply])
  right_inv y := funext fun i => Prod.ext rfl (funext fun j => by
    change (y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1).2
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = (y i).2 j
    rw [Equiv.symm_apply_apply])

omit [L₂.IsRelational] [Finite Tag] in
theorem liftEnv_blockRelabel (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A α : Type} {n : ℕ}
    (τ : α → Tag) (w : α × Fin d → A) (p : (Fin n → Tag) × (Fin (n * d) → A)) :
    I.liftEnv (Sum.elim τ p.1) (Sum.elim w p.2 ∘ blockRelabel) =
      Sum.elim (I.liftEnv τ w) (blockEquiv I A n p) :=
  funext fun x => by cases x <;> rfl

open Classical in
/-- **A pulled-back term has, in the source structure, the value of the term
in the interpreted structure.** -/
theorem QTerm.eval_pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A : Type} [L₁.Structure A]
    [Finite A] {α : Type} (t : Lax366625.QuantitativeLogic.QTerm L₂ α) :
    ∀ (τ : α → Tag) (w : α × Fin d → A),
      (t.pull I τ).eval w = t.eval (A := I.Map A) (I.liftEnv τ w) := by
  let : Fintype Tag := Fintype.ofFinite Tag
  let : Fintype A := Fintype.ofFinite A
  have : Finite (I.Map A) := I.map_finite A
  let : Fintype (I.Map A) := Fintype.ofFinite _
  induction t with
  | ind φ =>
    intro τ w
    have h := I.realize_pullFormula φ τ w
    by_cases hφ : φ.Realize (M := I.Map A) (I.liftEnv τ w) <;> simp [QTerm.pull, Lax366625.QuantitativeLogic.QTerm.eval, h, hφ]
  | const s => intro τ w; rfl
  | add s t hs ht => intro τ w; simp only [QTerm.pull, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | mul s t hs ht => intro τ w; simp only [QTerm.pull, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | sum n t ht =>
    intro τ w
    simp only [QTerm.pull, QTerm.eval_bigAdd, List.map_map, Function.comp_def, Lax366625.QuantitativeLogic.QTerm.eval,
      QTerm.eval_relabel, ht, allTagAssign, finsum_eq_sum_of_fintype]
    rw [Finset.sum_map_toList, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (blockEquiv I A n) _ _ fun p =>
      congrArg t.eval (liftEnv_blockRelabel I τ w p)
  | prod n t ht =>
    intro τ w
    simp only [QTerm.pull, QTerm.eval_bigMul, List.map_map, Function.comp_def, Lax366625.QuantitativeLogic.QTerm.eval,
      QTerm.eval_relabel, ht, allTagAssign, finprod_eq_prod_of_fintype]
    rw [Finset.prod_map_toList, ← Fintype.prod_prod_type']
    exact Fintype.prod_equiv (blockEquiv I A n) _ _ fun p =>
      congrArg t.eval (liftEnv_blockRelabel I τ w p)

end Pull

end Lax794877Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax794877Proofs.DescriptiveComplexity.QTerm (eval_pull)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

end Pull

end Lax794877Proofs.DescriptiveComplexity


