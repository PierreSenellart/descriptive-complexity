/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.Class
import Lax794877Proofs.DescriptiveComplexity.Numbers.DigitExtract
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

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.PossibleWorlds (IsOpenFact IsWorld worldBlock worldStructure)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Counting possible worlds

The counting problem behind query evaluation over an *incomplete* or
*probabilistic* database, for an arbitrary finite relational schema `L`.

An instance is a structure over two copies of the schema, `L.sum L`: the left
copy holds the **certain** facts and the right copy the **uncertain** ones. A
**possible world** keeps every certain fact and some of the uncertain ones
(`DescriptiveComplexity.IsWorld`); it is a structure over the schema itself
(`DescriptiveComplexity.worldStructure`). For a sentence `φ` of the schema,
`DescriptiveComplexity.PossibleWorlds φ` is the number of possible worlds in
which `φ` holds.

A world is one relation per symbol of the schema, i.e., an assignment of the
block `DescriptiveComplexity.worldBlock`, and both “this is a world” and “`φ`
holds in it” are first-order in the instance expanded by that block. So the
problem is the witness count of a kernel, and is in `#P` for every sentence
whatever (`DescriptiveComplexity.possibleWorlds_mem_sharpP`): the data
complexity of counting the worlds of a first-order query never exceeds `#P`.

The reading in probabilities: a fact that is uncertain and not certain is
*open*, and an instance with `k` open facts has `2 ^ k` worlds
(`DescriptiveComplexity.card_isWorld`). With each open fact present with
probability `1/2`, independently, the probability of `φ` is
`PossibleWorlds φ / 2 ^ k`: the model is a tuple-independent database whose
probabilities are `1/2` and `1`.
Hardness depends on the query, and is the business of
`DescriptiveComplexity.Examples.ProbabilisticQueries`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-! ### Worlds -/

section Worlds

variable {L} [Finite (Σ n, L.Relations n)] {A : Type}

/-- **An instance with `k` open facts has `2 ^ k` possible worlds**: a world
is a choice among them. So, each open fact being present with probability
`1/2` independently of the others, the probability of a sentence is the
number of worlds in which it holds, divided by `2 ^ k`. -/
theorem card_isWorld [(L.sum L).Structure A] [Finite A] :
    Nat.card {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A // Lax794877.PossibleWorlds.IsWorld ρ} =
      2 ^ Nat.card {q : Σ p : Σ n, L.Relations n, Fin p.1 → A // Lax794877.PossibleWorlds.IsOpenFact q} := by
  classical
  rw [← card_subsets_eq_two_pow]
  exact Nat.card_congr
    { toFun := fun ρ => ⟨fun q => ρ.1 q.1 q.2 ∧
          ¬RelMap (L := L.sum L) (M := A) (Sum.inl q.1.2) q.2,
        fun q h => ⟨((ρ.2 q.1 q.2).2 h.1).resolve_left h.2, h.2⟩⟩
      invFun := fun F => ⟨fun p x =>
          RelMap (L := L.sum L) (M := A) (Sum.inl p.2) x ∨ F.1 ⟨p, x⟩,
        fun p x => ⟨Or.inl, fun h => h.elim Or.inl fun hF => Or.inr (F.2 ⟨p, x⟩ hF).1⟩⟩
      left_inv := fun ρ => Subtype.ext (funext fun p => funext fun x => propext
        ⟨fun h => h.elim (ρ.2 p x).1 fun h' => h'.1,
          fun h => (Classical.em _).imp id fun hc => ⟨h, hc⟩⟩)
      right_inv := fun F => Subtype.ext (funext fun q => propext
        ⟨fun h => h.1.resolve_left h.2, fun h => ⟨Or.inr h, (F.2 q h).2⟩⟩) }

end Worlds

/-! ### The kernel -/

section Kernel

variable {L} [Finite (Σ n, L.Relations n)]

/-- The vocabulary of the kernel: the instance, and the guessed world. -/
abbrev worldLang (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : Language :=
  (L.sum L).sum (Lax794877.PossibleWorlds.worldBlock L).lang

/-- The symbol of the guessed world for a relation symbol of the schema. -/
abbrev worldSym (p : Σ n, L.Relations n) : (worldLang L).Relations p.1 :=
  Sum.inr ⟨p, rfl⟩

/-- Reading a sentence of the schema in the guessed world. -/
def toWorld (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] [L.IsRelational] :
    L →ᴸ worldLang L where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R => worldSym ⟨n, R⟩

/-- The sentence saying that the guessed relations form a possible world. -/
noncomputable def worldSentence (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] :
    (worldLang L).Sentence :=
  Formula.iInf fun p : Σ n, L.Relations n =>
    Formula.iAlls (Fin p.1)
      (((((Relations.formula (Sum.inl (Sum.inl p.2) : (worldLang L).Relations p.1)
              fun m => Term.var m).imp
            (Relations.formula (worldSym p) fun m => Term.var m)) ⊓
          ((Relations.formula (worldSym p) fun m => Term.var m).imp
            ((Relations.formula (Sum.inl (Sum.inl p.2) : (worldLang L).Relations p.1)
                fun m => Term.var m) ⊔
              (Relations.formula (Sum.inl (Sum.inr p.2) : (worldLang L).Relations p.1)
                fun m => Term.var m)))) :
        (worldLang L).Formula (Fin p.1)).relabel Sum.inr)

/-- Realization of a finite conjunction of formulas. -/
private theorem realize_iInf' {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {α β : Type}
    [Finite β] (f : β → L'.Formula α) (v : α → M) :
    (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

theorem realize_worldSentence {A : Type} [(L.sum L).Structure A]
    (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) :
    @Sentence.Realize (worldLang L) A
        (@sumStructure (L.sum L) (Lax794877.PossibleWorlds.worldBlock L).lang A _ ((Lax794877.PossibleWorlds.worldBlock L).structure ρ))
        (worldSentence L) ↔ Lax794877.PossibleWorlds.IsWorld ρ := by
  let := (Lax794877.PossibleWorlds.worldBlock L).structure ρ
  rw [worldSentence, Sentence.Realize, realize_iInf', Lax794877.PossibleWorlds.IsWorld]
  refine forall_congr' fun p => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel, Formula.realize_inf, Formula.realize_imp, Formula.realize_imp,
    Formula.realize_sup]
  exact and_congr (imp_congr (Formula.realize_rel.trans Iff.rfl)
      (Formula.realize_rel.trans Iff.rfl))
    (imp_congr (Formula.realize_rel.trans Iff.rfl)
      (or_congr (Formula.realize_rel.trans Iff.rfl) (Formula.realize_rel.trans Iff.rfl)))

/-- A sentence of the schema, read in the guessed world, holds exactly when it
holds in the structure the world is. -/
theorem realize_toWorld [L.IsRelational] {A : Type} [(L.sum L).Structure A]
    (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (φ : L.Sentence) :
    @Sentence.Realize (worldLang L) A
        (@sumStructure (L.sum L) (Lax794877.PossibleWorlds.worldBlock L).lang A _ ((Lax794877.PossibleWorlds.worldBlock L).structure ρ))
        ((toWorld L).onSentence φ) ↔
      @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ := by
  let s₁ : L.Structure A := Lax794877.PossibleWorlds.worldStructure ρ
  let s₂ : (worldLang L).Structure A :=
    @sumStructure (L.sum L) (Lax794877.PossibleWorlds.worldBlock L).lang A _ ((Lax794877.PossibleWorlds.worldBlock L).structure ρ)
  have : @LHom.IsExpansionOn _ _ (toWorld L) A s₁ s₂ :=
    @LHom.IsExpansionOn.mk _ _ _ _ s₁ s₂ (fun f _ => isEmptyElim f) (fun _ _ => rfl)
  exact @LHom.realize_onSentence _ _ A s₁ s₂ (toWorld L) this φ

/-- The kernel of the problem: the guessed relations form a possible world, in
which the sentence holds. -/
noncomputable def worldKernel [L.IsRelational] (φ : L.Sentence) : (worldLang L).Sentence :=
  worldSentence L ⊓ (toWorld L).onSentence φ

theorem realize_worldKernel [L.IsRelational] {A : Type} [(L.sum L).Structure A]
    (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (φ : L.Sentence) :
    @Sentence.Realize (worldLang L) A
        (@sumStructure (L.sum L) (Lax794877.PossibleWorlds.worldBlock L).lang A _ ((Lax794877.PossibleWorlds.worldBlock L).structure ρ))
        (worldKernel φ) ↔
      Lax794877.PossibleWorlds.IsWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ := by
  have h1 := realize_worldSentence ρ
  have h2 := realize_toWorld ρ φ
  let := (Lax794877.PossibleWorlds.worldBlock L).structure ρ
  rw [worldKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

end Kernel

/-! ### The counting problem -/

section Problem

variable {L} [Finite (Σ n, L.Relations n)] [L.IsRelational]

/-- **Counting possible worlds**: the number of possible worlds of the
instance in which the sentence `φ` of the schema holds. -/
noncomputable def PossibleWorlds (φ : L.Sentence) : Lax366625.CountingProblems.CountingProblem (L.sum L) :=
  CountingProblem.ofKernel (Lax794877.PossibleWorlds.worldBlock L) (worldKernel φ)

theorem possibleWorlds_apply (φ : L.Sentence) (A : Type) [(L.sum L).Structure A] :
    PossibleWorlds φ A =
      Nat.card {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
        Lax794877.PossibleWorlds.IsWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun ρ => realize_worldKernel ρ φ)

/-- **Counting the possible worlds of a first-order sentence is in `#P`**,
whatever the sentence. -/
theorem possibleWorlds_mem_sharpP (φ : L.Sentence) : PossibleWorlds φ ∈ SharpP :=
  sharpPDefinable_ofKernel (Lax794877.PossibleWorlds.worldBlock L) (worldKernel φ)

end Problem

end Lax794877Proofs.DescriptiveComplexity


