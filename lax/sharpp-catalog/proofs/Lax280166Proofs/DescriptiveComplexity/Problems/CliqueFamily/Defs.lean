/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Vocabulary
import Lax280166Proofs.DescriptiveComplexity.Interpretation
import Lax280166Proofs.DescriptiveComplexity.Numbers.Unary
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

namespace Lax280166Proofs.DescriptiveComplexity.CliqueOn
end Lax280166Proofs.DescriptiveComplexity.CliqueOn

namespace Lax280166Proofs.DescriptiveComplexity.CoverOn
end Lax280166Proofs.DescriptiveComplexity.CoverOn

namespace Lax280166Proofs.DescriptiveComplexity.IndepOn
end Lax280166Proofs.DescriptiveComplexity.IndepOn

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (CliqueOn CoverOn HasLargeClique HasLargeIndependentSet HasSmallVertexCover IndepOn MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Clique, Independent Set and Vertex Cover: definitions

The three classical threshold problems on graphs, as decision problems on
*marked graphs*: `FirstOrder.Language.markedGraph`-structures, carrying a
binary adjacency relation and a unary mark. The marked set carries the numeric
threshold `k` of the textbook problems in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary`: the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free.

* `DescriptiveComplexity.Clique`: some clique is at least as large as the marked set;
* `DescriptiveComplexity.IndependentSet`: some independent set is at least as large as
  the marked set;
* `DescriptiveComplexity.VertexCover`: some vertex cover is at most as large as the
  marked set.

The threshold comparisons are comparisons of decoded numbers, and the
cardinality arithmetic they need is the shared kit of
`DescriptiveComplexity.Numbers.Unary`: invariance of a decoded number under an
equivalence of universes (`DescriptiveComplexity.ncard_image_equiv`) for the
isomorphism-invariance proofs, the reversal of a comparison under
complementation (`DescriptiveComplexity.ncard_compl_le_ncard_compl_iff`) for the
Vertex Cover ↔ Independent Set reductions, and the equivalence with the
existence of an injection (`DescriptiveComplexity.nonempty_embedding_iff_ncard_le`,
here `DescriptiveComplexity.cliqueOn_iff_embedding`) for the second-order definition,
which guesses that injection as a relation variable. Since cardinality
thresholds are only meaningful on finite structures, finiteness of the
universe is part of the yes-instances; by `ComplexityClass.mem_congr_finite`
this does not affect any complexity-theoretic statement.

Self-loops are ignored (all three properties are about the underlying
loopless graph), and adjacency is required in both directions on ordered
pairs, so the problems agree with their standard versions on (structures
encoding) simple graphs.

The three predicates are instances of generic properties `DescriptiveComplexity.CliqueOn`
/ `IndepOn` / `CoverOn` of a binary and a unary predicate on a type; the
generic form is shared by the isomorphism-invariance proofs and by the
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Generic threshold properties

The properties underlying the three problems, for an arbitrary binary
predicate `Adjp` (adjacency) and unary predicate `Kp` (marks) on a type. -/

section Generic

variable {A : Type}

/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold conditions can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/

section Embedding

end Embedding

variable {B : Type}

/-- `CliqueOn` transports along an equivalence commuting with the two
predicates. -/
theorem CliqueOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.CliqueFamily.CliqueOn AdjB KB) : Lax799700.CliqueFamily.CliqueOn AdjA KA := by
  obtain ⟨S, hS, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), fun x y hx hy hxy => ?_, ?_⟩
  · have h' := (hadj (u.symm x) (u.symm y)).mp
      (hS _ _ hx hy fun h => hxy (u.symm.injective h))
    simpa using h'
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u S]
    exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.CliqueOn

export Lax280166Proofs.DescriptiveComplexity.CliqueOn (of_equiv)

end Lax799700.CliqueFamily.CliqueOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `IndepOn` transports along an equivalence commuting with the two
predicates. -/
theorem IndepOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.CliqueFamily.IndepOn AdjB KB) : Lax799700.CliqueFamily.IndepOn AdjA KA :=
  CliqueOn.of_equiv u (fun b b' => not_congr (hadj b b')) hK h

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.IndepOn

export Lax280166Proofs.DescriptiveComplexity.IndepOn (of_equiv)

end Lax799700.CliqueFamily.IndepOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `CoverOn` transports along an equivalence commuting with the two
predicates. -/
theorem CoverOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : Lax799700.CliqueFamily.CoverOn AdjB KB) : Lax799700.CliqueFamily.CoverOn AdjA KA := by
  obtain ⟨C, hC, hcard⟩ := h
  refine ⟨fun a => C (u.symm a), fun x y hxy hadjA => ?_, ?_⟩
  · exact hC (u.symm x) (u.symm y) (fun h => hxy (u.symm.injective h))
      ((hadj (u.symm x) (u.symm y)).mpr (by simpa using hadjA))
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u C]
    exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.CoverOn

export Lax280166Proofs.DescriptiveComplexity.CoverOn (of_equiv)

end Lax799700.CliqueFamily.CoverOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

private theorem symm_hadj {AdjB : B → B → Prop} {AdjA : A → A → Prop} (u : B ≃ A)
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (a a' : A) :
    AdjA a a' ↔ AdjB (u.symm a) (u.symm a') := by
  rw [hadj]
  simp

private theorem symm_hK {KB : B → Prop} {KA : A → Prop} (u : B ≃ A)
    (hK : ∀ b, KB b ↔ KA (u b)) (a : A) : KA a ↔ KB (u.symm a) := by
  rw [hK]
  simp

/-- `CliqueOn` transports along an equivalence, iff version. -/
theorem CliqueOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.CliqueFamily.CliqueOn AdjB KB ↔ Lax799700.CliqueFamily.CliqueOn AdjA KA :=
  ⟨CliqueOn.of_equiv u hadj hK,
    CliqueOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.CliqueOn

export Lax280166Proofs.DescriptiveComplexity.CliqueOn (equiv_iff)

end Lax799700.CliqueFamily.CliqueOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `IndepOn` transports along an equivalence, iff version. -/
theorem IndepOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.CliqueFamily.IndepOn AdjB KB ↔ Lax799700.CliqueFamily.IndepOn AdjA KA :=
  ⟨IndepOn.of_equiv u hadj hK,
    IndepOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.IndepOn

export Lax280166Proofs.DescriptiveComplexity.IndepOn (equiv_iff)

end Lax799700.CliqueFamily.IndepOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `CoverOn` transports along an equivalence, iff version. -/
theorem CoverOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    Lax799700.CliqueFamily.CoverOn AdjB KB ↔ Lax799700.CliqueFamily.CoverOn AdjA KA :=
  ⟨CoverOn.of_equiv u hadj hK,
    CoverOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.CliqueFamily.CoverOn

export Lax280166Proofs.DescriptiveComplexity.CoverOn (equiv_iff)

end Lax799700.CliqueFamily.CoverOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### The three problems -/

section Problems

section Shorthands

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

end Shorthands

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

variable {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B]

private theorem mgAdj_map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) (a b : A) :
    Lax799700.CliqueFamily.MGAdj a b ↔ Lax799700.CliqueFamily.MGAdj (e a) (e b) :=
  relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a b

private theorem mgMarked_map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) (a : A) :
    Lax799700.CliqueFamily.MGMarked a ↔ Lax799700.CliqueFamily.MGMarked (e a) :=
  relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a

/-- The clique threshold property is isomorphism-invariant. -/
theorem hasLargeClique_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.CliqueFamily.HasLargeClique A ↔ Lax799700.CliqueFamily.HasLargeClique B :=
  and_congr e.toEquiv.finite_iff
    (CliqueOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

/-- The independent-set threshold property is isomorphism-invariant. -/
theorem hasLargeIndependentSet_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.CliqueFamily.HasLargeIndependentSet A ↔ Lax799700.CliqueFamily.HasLargeIndependentSet B :=
  and_congr e.toEquiv.finite_iff
    (IndepOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

/-- The vertex-cover threshold property is isomorphism-invariant. -/
theorem hasSmallVertexCover_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.CliqueFamily.HasSmallVertexCover A ↔ Lax799700.CliqueFamily.HasSmallVertexCover B :=
  and_congr e.toEquiv.finite_iff
    (CoverOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))

end Iso

/-- CLIQUE, as a problem on marked graphs: is there a clique at least as
large as the marked set? -/
def Clique : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.CliqueFamily.HasLargeClique A inst
  iso_invariant := fun e => hasLargeClique_iso e

/-- INDEPENDENT SET, as a problem on marked graphs: is there an independent
set at least as large as the marked set? -/
def IndependentSet : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.CliqueFamily.HasLargeIndependentSet A inst
  iso_invariant := fun e => hasLargeIndependentSet_iso e

/-- VERTEX COVER, as a problem on marked graphs: is there a vertex cover at
most as large as the marked set? -/
def VertexCover : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.CliqueFamily.HasSmallVertexCover A inst
  iso_invariant := fun e => hasSmallVertexCover_iso e

end Lax280166Proofs.DescriptiveComplexity


