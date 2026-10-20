/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
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

/-!
# Unary representation of numbers in finite structures

The unary encoding: a number carried by an instance is the *cardinality of a
marked set* – `Set.ncard` is the decoding function, and no order is needed.
This file provides the shared lemma kit so that problem files do not hand-roll
cardinality reasoning:

* `DescriptiveComplexity.ncard_image_equiv` and its predicate form
  `DescriptiveComplexity.ncard_setOf_equiv`: invariance of the decoded number under
  equivalences (this is what feeds `DecisionProblem.iso_invariant` proofs);
* `DescriptiveComplexity.initSeg` and `DescriptiveComplexity.ncard_initSeg`: the canonical encoding
  of `k ≤ n` as the initial segment of `Fin n`;
* `DescriptiveComplexity.ncard_compl_eq` and
  `DescriptiveComplexity.ncard_compl_le_ncard_compl_iff`: complement cardinality
  (`n - k`) and the resulting *reversal* of comparisons, which is what the
  Vertex Cover ↔ Independent Set reductions run on;
* `DescriptiveComplexity.nonempty_embedding_iff_ncard_le`: comparing decoded numbers is
  comparing sizes – the bridge to the second-order rendering of a threshold,
  where the injection witnessing the comparison is guessed as a relation
  variable (used by the `Σ₁` definition of Clique);
* `DescriptiveComplexity.nonempty_embedding_iff_ncard_le₂` and
  `DescriptiveComplexity.ncard_setOf_equiv₂`: the same, for a threshold carried by a
  marked *binary* relation – the arity-2 form of the representation, which is
  what problems counting arcs rather than vertices need;
* `DescriptiveComplexity.ncard_tagged_eq_sum`: cardinality under tag-disjoint union –
  the tagged framework's *addition*;
* `DescriptiveComplexity.ncard_univ_pi`: cardinality of a product of marked sets over
  the coordinates of a tuple – the tagged framework's *multiplication*.

Unary representation keeps numbers polynomial in the instance size; problems
whose numbers must be exponential (SubsetSum and friends) use the binary
representation of `DescriptiveComplexity.Numbers.Binary` instead.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open Set

/-- The decoded number is invariant under equivalences of the universe. -/
theorem ncard_image_equiv {A B : Type} (e : A ≃ B) (s : Set A) :
    (e '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s e.injective

/-- The number encoded by a marked set is invariant under an equivalence of
universes carrying one mark predicate to the other. This is the form the
transport of a threshold along an isomorphism (or along the equivalence
underlying a one-dimensional interpretation) takes in practice. -/
theorem ncard_setOf_equiv {A B : Type} (u : B ≃ A) {KB : B → Prop} {KA : A → Prop}
    (hK : ∀ b, KB b ↔ KA (u b)) : {b | KB b}.ncard = {a | KA a}.ncard := by
  rw [← ncard_image_equiv u {b | KB b}]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hK b).mp hb
  · intro ha
    exact ⟨u.symm a, (hK _).mpr (by simpa using ha), by simp⟩

/-- Pulling a mark predicate back along `u.symm` does not change the number it
encodes: the special case of `DescriptiveComplexity.ncard_setOf_equiv` where the
predicate on the target universe is the transported one. -/
theorem ncard_setOf_symm {A B : Type} (u : B ≃ A) (S : B → Prop) :
    {b | S b}.ncard = {a | S (u.symm a)}.ncard :=
  ncard_setOf_equiv u fun b => by simp

/-- A decoded number never exceeds the size of the universe. -/
theorem ncard_le_card {A : Type} [Finite A] (s : Set A) : s.ncard ≤ Nat.card A := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ s)

/-- Complement cardinality: the marked complement encodes `n - k`. -/
theorem ncard_compl_eq {A : Type} [Finite A] (s : Set A) :
    sᶜ.ncard = Nat.card A - s.ncard :=
  Set.ncard_compl s

/-- Complementation *reverses* the comparison of decoded numbers – the
subtraction `n - k` is monotone decreasing in `k`. This is the arithmetic
content of the Vertex Cover ↔ Independent Set reductions. -/
theorem ncard_compl_le_ncard_compl_iff {A : Type} [Finite A] (s t : Set A) :
    sᶜ.ncard ≤ tᶜ.ncard ↔ t.ncard ≤ s.ncard := by
  rw [ncard_compl_eq, ncard_compl_eq]
  have hs := ncard_le_card s
  have ht := ncard_le_card t
  omega

/-- Comparing a complement with a set, the two sides swap under
complementation: `n - k ≤ l` iff `n - l ≤ k`. -/
theorem ncard_compl_le_iff {A : Type} [Finite A] (s t : Set A) :
    sᶜ.ncard ≤ t.ncard ↔ tᶜ.ncard ≤ s.ncard := by
  rw [ncard_compl_eq, ncard_compl_eq]
  have hs := ncard_le_card s
  have ht := ncard_le_card t
  omega

/-! ### Thresholds on pairs

Problems whose objective counts *arcs* rather than vertices – Feedback Arc Set,
Max Cut – need a threshold that can reach `n²`, which a marked subset of the
universe cannot. The same unary idea one arity up does reach it: the number is
the cardinality of a marked *binary* relation, decoded as the `Set.ncard` of the
corresponding set of pairs. It stays order-free and isomorphism-invariant, and
the whole kit above applies at the type `A × A`; the two lemmas below are just
its curried form. -/

/-- The number encoded by a marked binary relation is invariant under an
equivalence of universes carrying one relation to the other. -/
theorem ncard_setOf_equiv₂ {A B : Type} (u : B ≃ A) {RB : B → B → Prop}
    {RA : A → A → Prop} (hR : ∀ b b', RB b b' ↔ RA (u b) (u b')) :
    {p : B × B | RB p.1 p.2}.ncard = {p : A × A | RA p.1 p.2}.ncard :=
  ncard_setOf_equiv (u.prodCongr u) fun p => hR p.1 p.2

end Lax280166Proofs.DescriptiveComplexity


