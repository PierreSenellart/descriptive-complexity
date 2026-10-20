/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax794877Proofs.DescriptiveComplexity.Counting.PossibleWorlds
import Lax794877Proofs.DescriptiveComplexity.Numbers.BinCount
import Lax794877Proofs.DescriptiveComplexity.Counting.Probability
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax794877.PossibleWorlds
end Lax794877.PossibleWorlds

namespace Lax794877.WeightedWorlds
end Lax794877.WeightedWorlds

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.PossibleWorlds (worldBlock worldStructure)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.WeightedWorlds (BitLt Fact IsOpen WLe WeightCond WeightedRel absWeight bitsOf holdsEvent instIsRelationalWeightedLang numOf openFactFintype presWeight weightBlock weightedLang worldOf worldOfVal worldProb)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Counting weighted possible worlds

`DescriptiveComplexity.Counting.PossibleWorlds` counts the possible worlds of
an instance with certain and uncertain facts, each uncertain fact being
present with probability `1/2`. Here every uncertain fact carries its own
probability, as two natural **weights**: `a` for its being present and `c` for
its being absent, the probability being `a / (a + c)`. The quantity counted is
the **weighted number of worlds** in which a sentence `φ` of the schema holds,

`W(φ) = ∑ over the worlds satisfying φ of ∏ over the open facts of their weight`,

and the probability of `φ` is `W(φ) / W(⊤)`
(`DescriptiveComplexity.ProbAssignment.funcProb_ofWeights`).

## The instances

`DescriptiveComplexity.weightedLang L`: for each symbol of the schema `L`, of
arity `n`, the certain facts and the uncertain ones, and two relations of
arity `n + 1` holding the bits of the two weights of each fact; and one order
relation on the bit positions, which are all the elements. Weights are in
**binary**: the encoding in which a probability of a database is honestly
written, and the one for which membership is the stronger statement.

## Why this is in `#P`

A weight multiplies a count, and a count cannot be multiplied by a number of
the instance directly. The witness therefore carries, beside the world, one
number per open fact, *below the weight that fact takes in the world*: each
world is then counted once per unit of the product of its weights. “Below” is
first-order, by the highest position at which two binary numbers differ
(`DescriptiveComplexity.numLtFormula`, generic in the arity of the fact), and
the numbers below a weight are as many as the weight
(`DescriptiveComplexity.card_binNum_lt`).

* `DescriptiveComplexity.WeightedWorlds φ` is the witness count of that
  kernel, hence in `#P` for every first-order `φ`
  (`DescriptiveComplexity.weightedWorlds_mem_sharpP`).
* `DescriptiveComplexity.weightedWorlds_eq_weightSum`: on an instance whose
  order is linear, it is the weighted number of worlds. The proof sorts the
  witnesses by world (`DescriptiveComplexity.weightedWorlds_eq_sum`), then
  counts the numbers allowed at each fact
  (`DescriptiveComplexity.card_numCond`).
* On an instance whose order relation is not linear the count is zero
  (`DescriptiveComplexity.weightedWorlds_of_not_isLinOrd`): the kernel asks
  for linearity, such an instance carrying no number.

## The probability

The open facts of an instance are independent Boolean variables, and a world
is a valuation of them (`DescriptiveComplexity.worldOfVal`). So the count is a
weighted count in the sense of `DescriptiveComplexity.Counting.Probability`
(`DescriptiveComplexity.weightedWorlds_eq_weightedCount`), and

`Pr(φ) = WeightedWorlds φ / WeightedWorlds ⊤`

(`DescriptiveComplexity.funcProb_holdsEvent_eq_ratio`): **the probability of
any first-order query over a tuple-independent database is a ratio of two
`#P` numbers**.

-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The vocabulary -/

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

/-- The vocabulary of the kernel. -/
abbrev weightKernelLang (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : Language :=
  (Lax794877.WeightedWorlds.weightedLang L).sum (Lax794877.WeightedWorlds.weightBlock L).lang

section Symbols

variable (p : Σ n, L.Relations n)

/-- The certain facts of a symbol, in the kernel vocabulary. -/
abbrev wkCert : (weightKernelLang L).Relations p.1 := Sum.inl (Lax794877.WeightedWorlds.WeightedRel.cert p.2)

/-- The uncertain facts of a symbol, in the kernel vocabulary. -/
abbrev wkUnc : (weightKernelLang L).Relations p.1 := Sum.inl (Lax794877.WeightedWorlds.WeightedRel.unc p.2)

/-- The bits of the weight of presence, in the kernel vocabulary. -/
abbrev wkPres : (weightKernelLang L).Relations (p.1 + 1) := Sum.inl (Lax794877.WeightedWorlds.WeightedRel.pres p.2)

/-- The bits of the weight of absence, in the kernel vocabulary. -/
abbrev wkAbs : (weightKernelLang L).Relations (p.1 + 1) := Sum.inl (Lax794877.WeightedWorlds.WeightedRel.abs p.2)

/-- The guessed world, in the kernel vocabulary. -/
abbrev wkWorld : (weightKernelLang L).Relations p.1 := Sum.inr ⟨Sum.inl p, rfl⟩

/-- The guessed numbers, in the kernel vocabulary. -/
abbrev wkNum : (weightKernelLang L).Relations (p.1 + 1) := Sum.inr ⟨Sum.inr p, rfl⟩

end Symbols

/-- The order of the positions, in the kernel vocabulary. -/
abbrev wkLe (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] :
    (weightKernelLang L).Relations 2 := Sum.inl Lax794877.WeightedWorlds.WeightedRel.le

/-! ### Atoms about a fact and a position -/

section Atoms

variable {L' : Language.{0, 0}} {α : Type} {n : ℕ}

/-- The atom `S(x̄)`, the tuple being read off the free variables through
`e`. -/
def factAtom (S : L'.Relations n) (e : Fin n → α) : L'.Formula α :=
  Relations.formula S fun m => Term.var (e m)

/-- The atom `S(x̄, i)`: a fact and a position. -/
def bitAtom (S : L'.Relations (n + 1)) (e : Fin n → α) (i : α) : L'.Formula α :=
  Relations.formula S (Fin.snoc (α := fun _ => L'.Term α) (fun m => Term.var (e m)) (Term.var i))

variable {M : Type} [L'.Structure M]

theorem realize_factAtom (S : L'.Relations n) (e : Fin n → α) (v : α → M) :
    (factAtom S e).Realize v ↔ RelMap S fun m => v (e m) :=
  Formula.realize_rel

theorem realize_bitAtom (S : L'.Relations (n + 1)) (e : Fin n → α) (i : α) (v : α → M) :
    (bitAtom S e i).Realize v ↔
      RelMap S (Fin.snoc (α := fun _ => M) (fun m => v (e m)) (v i)) := by
  rw [bitAtom, Formula.realize_rel]
  refine iff_of_eq (congrArg _ (funext fun k => ?_))
  refine Fin.lastCases ?_ (fun m => ?_) k
  · simp
  · simp

end Atoms

/-! ### Comparing two numbers attached to a fact -/

section Compare

variable {L' : Language.{0, 0}} {n : ℕ} (N W : L'.Relations (n + 1)) (Le : L'.Relations 2)

/-- “The number `N(x̄, ·)` is below the number `W(x̄, ·)`”, by the highest
position at which they differ: some position carries `1` in `W` and `0` in
`N`, and the two agree strictly above it. -/
noncomputable def numLtFormula : L'.Formula (Fin n) :=
  Formula.iExs Unit
    (bitAtom W Sum.inl (Sum.inr ()) ⊓ (∼(bitAtom N Sum.inl (Sum.inr ())) ⊓
      Formula.iAlls Unit
        (((Relations.formula₂ Le (Term.var (Sum.inl (Sum.inr ()))) (Term.var (Sum.inr ()))) ⊓
            ∼(Term.equal (Term.var (Sum.inr ())) (Term.var (Sum.inl (Sum.inr ()))))).imp
          ((bitAtom N (fun m => Sum.inl (Sum.inl m)) (Sum.inr ())).iff
            (bitAtom W (fun m => Sum.inl (Sum.inl m)) (Sum.inr ()))))))

/-- “The relation `Le` is a linear order”, as a sentence. -/
noncomputable def linOrdSentence : L'.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
          (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 3)
          ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))).imp
            ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 2))).imp
              (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2))))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 2)
          ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))).imp
            ((FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 0))).imp
              (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 2)
          (FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)) ⊔
            FirstOrder.Language.Relations.formula₂ Le (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- “The number `N(x̄, ·)` is zero”: it has no bit. -/
noncomputable def numZeroFormula : L'.Formula (Fin n) :=
  Formula.iAlls Unit (∼(bitAtom N Sum.inl (Sum.inr ())))

variable {M : Type} [L'.Structure M]

theorem realize_numLtFormula (x : Fin n → M) :
    (numLtFormula N W Le).Realize x ↔
      ∃ i : M, RelMap W (Fin.snoc (α := fun _ => M) x i) ∧
        ¬RelMap N (Fin.snoc (α := fun _ => M) x i) ∧
        ∀ j : M, RelMap Le ![i, j] → j ≠ i →
          (RelMap N (Fin.snoc (α := fun _ => M) x j) ↔
            RelMap W (Fin.snoc (α := fun _ => M) x j)) := by
  rw [numLtFormula, Formula.realize_iExs]
  simp only [Formula.realize_inf, Formula.realize_not, realize_bitAtom, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iff, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    exact ⟨f (), h1, h2, fun j hle hne => h3 (fun _ => j) ⟨hle, hne⟩⟩
  · rintro ⟨i, h1, h2, h3⟩
    exact ⟨fun _ => i, h1, h2, fun g hg => h3 (g ()) hg.1 hg.2⟩

theorem realize_linOrdSentence :
    M ⊨ linOrdSentence Le ↔ Lax904597.Machines.IsLinOrd (fun a b : M => RelMap Le ![a, b]) := by
  rw [linOrdSentence, Lax904597.Machines.IsLinOrd, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, and_assoc]
  refine and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a b c => h ![a, b, c], fun h i => h (i 0) (i 1) (i 2)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩

theorem realize_numZeroFormula (x : Fin n → M) :
    (numZeroFormula N).Realize x ↔ ∀ i : M, ¬RelMap N (Fin.snoc (α := fun _ => M) x i) := by
  rw [numZeroFormula, Formula.realize_iAlls]
  simp only [Formula.realize_not, realize_bitAtom, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h i => h fun _ => i, fun h f => h (f ())⟩

end Compare

/-! ### The kernel -/

section Kernel

variable {A : Type} [(Lax794877.WeightedWorlds.weightedLang L).Structure A]

/-- The condition of the kernel at one fact, as a formula in the fact. -/
noncomputable def weightFormulaAt (p : Σ n, L.Relations n) :
    (weightKernelLang L).Formula (Fin p.1) :=
  (((factAtom (wkCert p) id).imp (factAtom (wkWorld p) id)) ⊓
      ((factAtom (wkWorld p) id).imp (factAtom (wkCert p) id ⊔ factAtom (wkUnc p) id))) ⊓
    ((((factAtom (wkUnc p) id) ⊓ ∼(factAtom (wkCert p) id)).imp
        (((factAtom (wkWorld p) id).imp (numLtFormula (wkNum p) (wkPres p) (wkLe L))) ⊓
          ((∼(factAtom (wkWorld p) id)).imp (numLtFormula (wkNum p) (wkAbs p) (wkLe L))))) ⊓
      ((∼((factAtom (wkUnc p) id) ⊓ ∼(factAtom (wkCert p) id))).imp
        (numZeroFormula (wkNum p))))

theorem realize_weightFormulaAt (σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A) (p : Σ n, L.Relations n)
    (x : Fin p.1 → A) :
    @Formula.Realize (weightKernelLang L) A
        (@sumStructure (Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.weightBlock L).lang A _ ((Lax794877.WeightedWorlds.weightBlock L).structure σ))
        _ (weightFormulaAt p) x ↔ Lax794877.WeightedWorlds.WeightCond σ p x := by
  let := (Lax794877.WeightedWorlds.weightBlock L).structure σ
  rw [weightFormulaAt]
  simp only [Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    Formula.realize_sup, realize_factAtom, realize_numLtFormula, realize_numZeroFormula]
  exact Iff.rfl

/-- Realization of a finite conjunction of formulas. -/
private theorem realize_iInf' {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {α β : Type}
    [Finite β] (f : β → L'.Formula α) (v : α → M) :
    (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

/-- The sentence asking the condition of the kernel at every fact. -/
noncomputable def weightSentence (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] :
    (weightKernelLang L).Sentence :=
  Formula.iInf fun p : Σ n, L.Relations n =>
    Formula.iAlls (Fin p.1) ((weightFormulaAt p).relabel Sum.inr)

theorem realize_weightSentence (σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.weightBlock L).lang A _ ((Lax794877.WeightedWorlds.weightBlock L).structure σ))
        (weightSentence L) ↔ ∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), Lax794877.WeightedWorlds.WeightCond σ p x := by
  have h := realize_weightFormulaAt σ
  let := (Lax794877.WeightedWorlds.weightBlock L).structure σ
  rw [weightSentence, Sentence.Realize, realize_iInf']
  refine forall_congr' fun p => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel]
  exact h p x

/-- Reading a sentence of the schema in the guessed world. -/
def toWeightWorld (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] [L.IsRelational] :
    L →ᴸ weightKernelLang L where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R => wkWorld ⟨n, R⟩

theorem realize_toWeightWorld [L.IsRelational] (σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A)
    (φ : L.Sentence) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.weightBlock L).lang A _ ((Lax794877.WeightedWorlds.weightBlock L).structure σ))
        ((toWeightWorld L).onSentence φ) ↔
      @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)) φ := by
  let s₁ : L.Structure A := Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)
  let s₂ : (weightKernelLang L).Structure A :=
    @sumStructure (Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.weightBlock L).lang A _ ((Lax794877.WeightedWorlds.weightBlock L).structure σ)
  have : @LHom.IsExpansionOn _ _ (toWeightWorld L) A s₁ s₂ :=
    @LHom.IsExpansionOn.mk _ _ _ _ s₁ s₂ (fun f _ => isEmptyElim f) (fun _ _ => rfl)
  exact @LHom.realize_onSentence _ _ A s₁ s₂ (toWeightWorld L) this φ

/-- The kernel: the positions are linearly ordered, the condition holds at
every fact, and the sentence holds in the world. -/
noncomputable def weightKernel [L.IsRelational] (φ : L.Sentence) :
    (weightKernelLang L).Sentence :=
  linOrdSentence (wkLe L) ⊓ (weightSentence L ⊓ (toWeightWorld L).onSentence φ)

theorem realize_weightKernel [L.IsRelational] (σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A)
    (φ : L.Sentence) :
    @Sentence.Realize (weightKernelLang L) A
        (@sumStructure (Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.weightBlock L).lang A _ ((Lax794877.WeightedWorlds.weightBlock L).structure σ))
        (weightKernel φ) ↔
      Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) ∧
        (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), Lax794877.WeightedWorlds.WeightCond σ p x) ∧
          @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)) φ := by
  have h1 := realize_weightSentence σ
  have h2 := realize_toWeightWorld σ φ
  let := (Lax794877.WeightedWorlds.weightBlock L).structure σ
  have h0 : A ⊨ linOrdSentence (wkLe L) ↔ Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) := realize_linOrdSentence (wkLe L)
  rw [weightKernel, Sentence.Realize, Formula.realize_inf, Formula.realize_inf]
  exact and_congr h0 (and_congr h1 h2)

end Kernel

/-! ### The counting problem -/

section Problem

variable [L.IsRelational]

/-- **Counting weighted possible worlds**: the witnesses are the worlds in
which the sentence `φ` holds, each with one number per open fact below the
weight that fact takes in the world. On an instance whose positions are
linearly ordered this is the weighted count of the worlds satisfying `φ`, and
on any other instance it is zero. -/
noncomputable def WeightedWorlds (φ : L.Sentence) : Lax366625.CountingProblems.CountingProblem (Lax794877.WeightedWorlds.weightedLang L) :=
  CountingProblem.ofKernel (Lax794877.WeightedWorlds.weightBlock L) (weightKernel φ)

theorem weightedWorlds_apply (φ : L.Sentence) (A : Type) [(Lax794877.WeightedWorlds.weightedLang L).Structure A] :
    WeightedWorlds φ A =
      Nat.card {σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A //
        Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) ∧
          (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), Lax794877.WeightedWorlds.WeightCond σ p x) ∧
            @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)) φ} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun σ => realize_weightKernel σ φ)

/-- On an instance whose positions are not linearly ordered, the count is
zero: such an instance carries no number. -/
theorem weightedWorlds_of_not_isLinOrd (φ : L.Sentence) (A : Type)
    [(Lax794877.WeightedWorlds.weightedLang L).Structure A] (h : ¬Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A)) : WeightedWorlds φ A = 0 := by
  rw [weightedWorlds_apply]
  have : IsEmpty {σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A //
      Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) ∧
        (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), Lax794877.WeightedWorlds.WeightCond σ p x) ∧
          @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)) φ} := ⟨fun σ => h σ.2.1⟩
  exact Nat.card_of_isEmpty

/-- **Counting the weighted worlds of a first-order sentence is in `#P`**,
whatever the sentence. -/
theorem weightedWorlds_mem_sharpP (φ : L.Sentence) : WeightedWorlds φ ∈ SharpP :=
  sharpPDefinable_ofKernel (Lax794877.WeightedWorlds.weightBlock L) (weightKernel φ)

end Problem

/-! ### The count -/

section Count

variable [L.IsRelational] {A : Type} [(Lax794877.WeightedWorlds.weightedLang L).Structure A]

/-- The family of relations is a possible world of the weighted instance. -/
def IsWeightedWorld (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) : Prop :=
  ∀ q : Lax794877.WeightedWorlds.Fact L A, (RelMap (L := Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2 → ρ q.1 q.2) ∧
    (ρ q.1 q.2 → RelMap (L := Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.WeightedRel.cert q.1.2) q.2 ∨
      RelMap (L := Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.WeightedRel.unc q.1.2) q.2)

/-- What the kernel asks of the number attached to a fact, in a world. -/
def NumCond (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (q : Lax794877.WeightedWorlds.Fact L A) (b : A → Prop) : Prop :=
  (Lax794877.WeightedWorlds.IsOpen q →
      (ρ q.1 q.2 → Lax794877.WeightedWorlds.BitLt (Lax794877.WeightedWorlds.WLe L A) b (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.pres q.1.2) q.2)) ∧
        (¬ρ q.1 q.2 → Lax794877.WeightedWorlds.BitLt (Lax794877.WeightedWorlds.WLe L A) b (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.abs q.1.2) q.2))) ∧
    (¬Lax794877.WeightedWorlds.IsOpen q → ∀ i, ¬b i)

/-- An assignment of the block is a world and a number per fact. -/
def weightAssignEquiv (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] (A : Type) :
    (Lax794877.WeightedWorlds.weightBlock L).Assignment A ≃ (Lax794877.PossibleWorlds.worldBlock L).Assignment A × (Lax794877.WeightedWorlds.Fact L A → A → Prop) where
  toFun σ := (Lax794877.WeightedWorlds.worldOf σ, fun q => Lax794877.WeightedWorlds.numOf σ q.1 q.2)
  invFun r := fun i =>
    match i with
    | Sum.inl p => r.1 p
    | Sum.inr p => fun y => r.2 ⟨p, Fin.init y⟩ (y (Fin.last p.1))
  left_inv σ := by
    funext i
    cases i with
    | inl p => rfl
    | inr p =>
      funext y
      exact congrArg (σ (Sum.inr p)) (Fin.snoc_init_self y)
  right_inv r := by
    refine Prod.ext rfl (funext fun q => funext fun i => ?_)
    obtain ⟨p, x⟩ := q
    change r.2 ⟨p, Fin.init (Fin.snoc (α := fun _ => A) x i)⟩
      (Fin.snoc (α := fun _ => A) x i (Fin.last p.1)) = r.2 ⟨p, x⟩ i
    rw [Fin.init_snoc, Fin.snoc_last]

/-- **The witnesses, sorted by world**: the count is the sum, over the worlds
satisfying the sentence, of the product over the facts of the number of
numbers the kernel allows there. -/
theorem weightedWorlds_eq_sum [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A)) (φ : L.Sentence) :
    WeightedWorlds φ A =
      ∑ᶠ ρ : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ},
        ∏ᶠ q : Lax794877.WeightedWorlds.Fact L A, Nat.card {b : A → Prop // NumCond ρ.1 q b} := by
  classical
  let := Fintype.ofFinite {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ}
  let := Fintype.ofFinite (Lax794877.WeightedWorlds.Fact L A)
  rw [weightedWorlds_apply, finsum_eq_sum_of_fintype]
  have e1 : {σ : (Lax794877.WeightedWorlds.weightBlock L).Assignment A //
        Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) ∧
          (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), Lax794877.WeightedWorlds.WeightCond σ p x) ∧
            @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOf σ)) φ} ≃
      {r : (Lax794877.PossibleWorlds.worldBlock L).Assignment A × (Lax794877.WeightedWorlds.Fact L A → A → Prop) //
        (IsWeightedWorld r.1 ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure r.1) φ) ∧
          ∀ q, NumCond r.1 q (r.2 q)} :=
    Equiv.subtypeEquiv (weightAssignEquiv L A) fun σ =>
      ⟨fun h => ⟨⟨fun q => (h.2.1 q.1 q.2).1, h.2.2⟩, fun q => (h.2.1 q.1 q.2).2⟩,
        fun h => ⟨hlin, fun p x => ⟨h.1.1 ⟨p, x⟩, h.2 ⟨p, x⟩⟩, h.1.2⟩⟩
  have e2 : {r : (Lax794877.PossibleWorlds.worldBlock L).Assignment A × (Lax794877.WeightedWorlds.Fact L A → A → Prop) //
        (IsWeightedWorld r.1 ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure r.1) φ) ∧
          ∀ q, NumCond r.1 q (r.2 q)} ≃
      Σ ρ : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ},
        ∀ q : Lax794877.WeightedWorlds.Fact L A, {b : A → Prop // NumCond ρ.1 q b} :=
    { toFun := fun r => ⟨⟨r.1.1, r.2.1⟩, fun q => ⟨r.1.2 q, r.2.2 q⟩⟩
      invFun := fun s => ⟨(s.1.1, fun q => (s.2 q).1), s.1.2, fun q => (s.2 q).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_sigma]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Nat.card_pi, finprod_eq_prod_of_fintype]

open Classical in
/-- The weight of a fact in a world: the weight of presence of an open fact
the world keeps, the weight of absence of an open fact it drops, and `1` for a
fact that is not open. Weights are read in binary on the order of the
instance. -/
noncomputable def factWeight (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (q : Lax794877.WeightedWorlds.Fact L A) : ℕ :=
  if Lax794877.WeightedWorlds.IsOpen q then
    if ρ q.1 q.2 then Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe L A) (fun _ => True) (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.pres q.1.2) q.2)
    else Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe L A) (fun _ => True) (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.abs q.1.2) q.2)
  else 1

/-- Over a linear order, the first-order comparison of two sets of bits is
the comparison of the numbers they encode. -/
theorem bitLt_iff_binNum_lt [Finite A] {Le : A → A → Prop} (hlin : Lax904597.Machines.IsLinOrd Le)
    (b w : A → Prop) :
    Lax794877.WeightedWorlds.BitLt Le b w ↔ Lax799700.Common.binNum Le (fun _ => True) b < Lax799700.Common.binNum Le (fun _ => True) w := by
  have hcard : ({p : A | True} : Set A).ncard = Nat.card A := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [binNum_lt_iff hlin (Nat.card A) (fun _ => True) hcard b w]
  constructor
  · rintro ⟨i, hw, hb, h⟩
    exact ⟨i, trivial, hb, hw, fun j _ hle hne => h j hle hne⟩
  · rintro ⟨i, -, hb, hw, h⟩
    exact ⟨i, hw, hb, fun j hle hne => h j trivial hle hne⟩

omit [L.IsRelational] in
/-- **The numbers the kernel allows at a fact are as many as its weight.** -/
theorem card_numCond [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A))
    (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (q : Lax794877.WeightedWorlds.Fact L A) :
    Nat.card {b : A → Prop // NumCond ρ q b} = factWeight ρ q := by
  by_cases ho : Lax794877.WeightedWorlds.IsOpen q
  · by_cases hρ : ρ q.1 q.2
    · simp only [factWeight, ho, hρ, ↓reduceIte]
      rw [← card_binNum_lt hlin]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun b =>
        Iff.trans ⟨fun h => (h.1 ho).1 hρ, fun h => ⟨fun _ => ⟨fun _ => h,
          fun h' => absurd hρ h'⟩, fun h' => absurd ho h'⟩⟩ (bitLt_iff_binNum_lt hlin b _))
    · simp only [factWeight, ho, hρ, ↓reduceIte]
      rw [← card_binNum_lt hlin]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun b =>
        Iff.trans ⟨fun h => (h.1 ho).2 hρ, fun h => ⟨fun _ => ⟨fun h' => absurd h' hρ,
          fun _ => h⟩, fun h' => absurd ho h'⟩⟩ (bitLt_iff_binNum_lt hlin b _))
  · simp only [factWeight, ho, ↓reduceIte]
    have e : {b : A → Prop // NumCond ρ q b} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨fun _ => False, fun h => absurd h ho, fun _ _ h => h⟩
        left_inv := fun b => Subtype.ext (funext fun i =>
          propext ⟨False.elim, fun h => b.2.2 ho i h⟩)
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_unit]

/-- **The count is the weighted number of worlds**: on an instance whose
positions are linearly ordered, the count is the sum, over the possible worlds
in which the sentence holds, of the product of the weights of the facts. -/
theorem weightedWorlds_eq_weightSum [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A)) (φ : L.Sentence) :
    WeightedWorlds φ A =
      ∑ᶠ ρ : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
          IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ},
        ∏ᶠ q : Lax794877.WeightedWorlds.Fact L A, factWeight ρ.1 q := by
  rw [weightedWorlds_eq_sum hlin]
  exact finsum_congr fun ρ => finprod_congr fun q => card_numCond hlin ρ.1 q

/-! ### Worlds as valuations of the open facts -/

omit [L.IsRelational] in
theorem isWeightedWorld_worldOfVal (v : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} → Bool) :
    IsWeightedWorld (Lax794877.WeightedWorlds.worldOfVal v) :=
  fun _ => ⟨Or.inl, fun h => h.elim Or.inl fun ⟨ho, _⟩ => Or.inr ho.1⟩

open Classical in
omit [L.IsRelational] in
/-- A world is the world of its valuation. -/
theorem worldOfVal_decide {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A} (hρ : IsWeightedWorld ρ) :
    Lax794877.WeightedWorlds.worldOfVal (fun x : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} => decide (ρ x.1.1 x.1.2)) = ρ := by
  funext p x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨_, h⟩
    · exact (hρ ⟨p, x⟩).1 h
    · exact of_decide_eq_true h
  · by_cases hc : RelMap (L := Lax794877.WeightedWorlds.weightedLang L) (Lax794877.WeightedWorlds.WeightedRel.cert p.2) x
    · exact Or.inl hc
    · exact Or.inr ⟨⟨((hρ ⟨p, x⟩).2 h).resolve_left hc, hc⟩, decide_eq_true h⟩

open Classical in
omit [L.IsRelational] in
/-- A valuation is the valuation of its world. -/
theorem decide_worldOfVal (v : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} → Bool) :
    (fun x : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} => decide (Lax794877.WeightedWorlds.worldOfVal v x.1.1 x.1.2)) = v := by
  funext x
  have h : Lax794877.WeightedWorlds.worldOfVal v x.1.1 x.1.2 ↔ v x = true :=
    ⟨fun h => h.elim (fun hc => absurd hc x.2.2) fun ⟨_, hv⟩ => hv, fun hv => Or.inr ⟨x.2, hv⟩⟩
  cases hv : v x
  · exact decide_eq_false fun hw => by rw [h.mp hw] at hv; exact Bool.noConfusion hv
  · exact decide_eq_true (h.mpr hv)

open Classical in
omit [L.IsRelational] in
/-- The product of the weights of the facts in a world is the weight of its
valuation: the facts that are not open contribute nothing. -/
theorem finprod_factWeight [Finite A] (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) :
    ∏ᶠ q : Lax794877.WeightedWorlds.Fact L A, factWeight ρ q =
      valWeight Lax794877.WeightedWorlds.presWeight Lax794877.WeightedWorlds.absWeight
        fun x : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} => decide (ρ x.1.1 x.1.2) := by
  let := Fintype.ofFinite (Lax794877.WeightedWorlds.Fact L A)
  rw [finprod_eq_prod_of_fintype, valWeight,
    ← Finset.prod_filter_of_ne (p := fun q : Lax794877.WeightedWorlds.Fact L A => Lax794877.WeightedWorlds.IsOpen q) fun q _ hq => by
      by_contra ho
      exact hq (by simp only [factWeight, ho, ↓reduceIte]),
    Finset.prod_subtype (p := fun q : Lax794877.WeightedWorlds.Fact L A => Lax794877.WeightedWorlds.IsOpen q)
      (Finset.univ.filter fun q : Lax794877.WeightedWorlds.Fact L A => Lax794877.WeightedWorlds.IsOpen q) (by simp)]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hρ : ρ x.1.1 x.1.2
  · simp only [factWeight, x.2, hρ, ↓reduceIte, decide_true, Lax794877.WeightedWorlds.presWeight]
  · simp only [factWeight, x.2, hρ, ↓reduceIte, decide_false, Bool.false_eq_true, Lax794877.WeightedWorlds.absWeight]

open Classical in
/-- **The count is a weighted count of valuations**: on an instance whose
positions are linearly ordered, counting the weighted worlds of a sentence is
the weighted count, over the valuations of the open facts, of the event that
the sentence holds. -/
theorem weightedWorlds_eq_weightedCount [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A))
    (φ : L.Sentence) :
    WeightedWorlds φ A = weightedCount Lax794877.WeightedWorlds.presWeight Lax794877.WeightedWorlds.absWeight (Lax794877.WeightedWorlds.holdsEvent (A := A) φ) := by
  let := Fintype.ofFinite {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ}
  let e : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ} ≃
      {v : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q} → Bool // Lax794877.WeightedWorlds.holdsEvent (A := A) φ v = true} :=
    { toFun := fun ρ => ⟨fun x => decide (ρ.1 x.1.1 x.1.2), by
        rw [Lax794877.WeightedWorlds.holdsEvent, worldOfVal_decide ρ.2.1]
        exact decide_eq_true ρ.2.2⟩
      invFun := fun v => ⟨Lax794877.WeightedWorlds.worldOfVal v.1, isWeightedWorld_worldOfVal v.1,
        of_decide_eq_true v.2⟩
      left_inv := fun ρ => Subtype.ext (worldOfVal_decide ρ.2.1)
      right_inv := fun v => Subtype.ext (decide_worldOfVal v.1) }
  rw [weightedWorlds_eq_weightSum hlin, finsum_eq_sum_of_fintype, weightedCount,
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun v => Lax794877.WeightedWorlds.holdsEvent (A := A) φ v = true)
      (Finset.univ.filter fun v => Lax794877.WeightedWorlds.holdsEvent (A := A) φ v = true) (by simp)]
  exact Fintype.sum_equiv e _ _ fun ρ => finprod_factWeight ρ.1

open Classical in
/-- **The probability of a first-order sentence is a ratio of two `#P`
numbers.** Over a weighted instance whose positions are linearly ordered, let
each open fact be present independently, with probability its weight of
presence over the sum of its two weights. Then the probability that `φ` holds
is the count of the weighted worlds of `φ`, divided by the count of all the
weighted worlds; and both counting problems are in `#P`
(`DescriptiveComplexity.weightedWorlds_mem_sharpP`). -/
theorem funcProb_holdsEvent_eq_ratio [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A))
    (hpos : ∀ x : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q}, 0 < Lax794877.WeightedWorlds.presWeight x + Lax794877.WeightedWorlds.absWeight x)
    (φ : L.Sentence) :
    (Lax794877.WeightedWorlds.ProbAssignment.ofWeights Lax794877.WeightedWorlds.presWeight Lax794877.WeightedWorlds.absWeight hpos).funcProb (Lax794877.WeightedWorlds.holdsEvent φ) =
      (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ) := by
  have htop : Lax794877.WeightedWorlds.holdsEvent (A := A) (⊤ : L.Sentence) = fun _ => true :=
    funext fun v => by
      let := Lax794877.PossibleWorlds.worldStructure (Lax794877.WeightedWorlds.worldOfVal v)
      exact decide_eq_true (Formula.realize_top.mpr trivial)
  rw [ProbAssignment.funcProb_ofWeights, weightedWorlds_eq_weightedCount hlin φ,
    weightedWorlds_eq_weightedCount hlin ⊤, htop]

/-- The probability of a first-order sentence is a ratio of two `#P` numbers:
`DescriptiveComplexity.funcProb_holdsEvent_eq_ratio`, for the packaged
probability. -/
theorem worldProb_eq_ratio [Finite A] (hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A)) (φ : L.Sentence)
    (hpos : ∀ x : {q : Lax794877.WeightedWorlds.Fact L A // Lax794877.WeightedWorlds.IsOpen q}, 0 < Lax794877.WeightedWorlds.presWeight x + Lax794877.WeightedWorlds.absWeight x) :
    Lax794877.WeightedWorlds.worldProb φ hpos = (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ) :=
  funcProb_holdsEvent_eq_ratio hlin hpos φ

end Count

end Lax794877Proofs.DescriptiveComplexity


