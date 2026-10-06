/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Finite
import Lax604544Proofs.DescriptiveComplexity.Block
import Lax604544Proofs.DescriptiveComplexity.Composition
import Lax604544Proofs.DescriptiveComplexity.Interpretation
import Lax604544Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax604544Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax604544Proofs.DescriptiveComplexity.SecondOrder
import Lax604544Proofs.DescriptiveComplexity.Vocabulary
import Lax604544Proofs.DescriptiveComplexity.SecondOrder
import Lax604544Proofs.DescriptiveComplexity.Block
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
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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

namespace Lax604544Proofs.DescriptiveComplexity.SubgraphIsoOn
end Lax604544Proofs.DescriptiveComplexity.SubgraphIsoOn

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.SubgraphIso
end Lax799700.SubgraphIso

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SigmaSODefinable)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (HasLargeClique MGAdj MGMarked)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.SubgraphIso (HasSubgraphIso SubgraphIsoOn TGHostE TGHostV TGPatE TGPatV)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.SubgraphIso (tgHostE tgHostV tgPatE tgPatV twoGraphs)
end FirstOrder.Language

/-!
# Subgraph Isomorphism is NP-complete

SUBGRAPH ISOMORPHISM: does the *host* graph contain a subgraph isomorphic to
the *pattern* graph? Equivalently – and this is the definition used here,
`DescriptiveComplexity.SubgraphIsoOn` – is there an injective homomorphism of the
pattern into the host? (Not an *induced* subgraph: non-edges of the pattern
are unconstrained, which is the standard reading and the one that makes Clique
a special case.)

## Two graphs in one structure

An instance carries two graphs, so `FirstOrder.Language.twoGraphs` has two
unary marks separating the pattern vertices from the host vertices and two
binary relations for the two adjacency relations. As with the set systems of
`DescriptiveComplexity.Problems.SetFamily`, nothing forces an element of the universe
to be a vertex of either graph: elements outside both marks are junk that no
condition mentions, which is exactly what lets a first-order interpretation
build such a structure inside a tagged power of its input universe. The
guessed map is likewise unconstrained off the pattern.

This vocabulary pattern – several structures side by side in one universe,
separated by marks – is the natural home for the remaining
combinatorial-packing problems (Exact Cover, 3-Dimensional Matching), where
the same trick applies.

## Hardness: a clique is a complete pattern

The reduction is from Clique (`DescriptiveComplexity.clique_fo_reduction_subgraphIso`,
tag `Bool`, dimension 1, quantifier-free): the host is the input graph and the
pattern is the *complete* graph on its marked set, so an injective
homomorphism of the pattern is precisely a clique at least as large as the
marked set. The threshold of Clique is thus consumed by the shape of the
pattern rather than by a counting argument – no `Set.ncard` reasoning appears
in this file beyond the embedding form
`DescriptiveComplexity.cliqueOn_iff_embedding` that Clique already provides.

The problem on *concrete* graphs – two edge sets on `Fin p` and `Fin h` – and
its encoding, faithfulness and decoding are in
`DescriptiveComplexity.Problems.SubgraphIso.Encoding`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### The generic property -/

section Generic

end Generic

/-! ### The problem -/

section Problem

section Shorthands

variable {A : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A]

end Shorthands

end Problem

section Iso

end Iso

/-! ### Clique reduces to Subgraph Isomorphism -/

section Points

end Points

section Characterizations

end Characterizations

section Correctness

end Correctness

/-! ### Membership -/

section SigmaOne

end SigmaOne

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive IsoGuessBlockIx where
/-- The guessed map from the pattern to the host. -/

  | map
  deriving DecidableEq

instance : Fintype _root_.Lax604544Proofs.DescriptiveComplexity.IsoGuessBlockIx :=
  ⟨List.toFinset [.map], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Subgraph
Isomorphism: one binary relation variable, the guessed map. -/
def isoGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax604544Proofs.DescriptiveComplexity.IsoGuessBlockIx
  arity := fun i =>
    match i with
    | .map => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev subgraphSOLang : FirstOrder.Language :=
  (Lax799700.SubgraphIso.twoGraphs).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax604544Proofs.DescriptiveComplexity.isoGuessBlock)

/-- The `patV` symbol over the sum. -/
abbrev sgPatVSym : (_root_.Lax604544Proofs.DescriptiveComplexity.subgraphSOLang).Relations 1 :=
  Sum.inl Lax799700.SubgraphIso.tgPatV

/-- The `hostV` symbol over the sum. -/
abbrev sgHostVSym : (_root_.Lax604544Proofs.DescriptiveComplexity.subgraphSOLang).Relations 1 :=
  Sum.inl Lax799700.SubgraphIso.tgHostV

/-- The `patE` symbol over the sum. -/
abbrev sgPatESym : (_root_.Lax604544Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inl Lax799700.SubgraphIso.tgPatE

/-- The `hostE` symbol over the sum. -/
abbrev sgHostESym : (_root_.Lax604544Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inl Lax799700.SubgraphIso.tgHostE

/-- The `map` relation variable. -/
def sgMapRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax604544Proofs.DescriptiveComplexity.isoGuessBlock).Relations 2 :=
  ⟨.map, rfl⟩

/-- The `map` symbol over the sum. -/
abbrev sgMapSym : (_root_.Lax604544Proofs.DescriptiveComplexity.subgraphSOLang).Relations 2 :=
  Sum.inr _root_.Lax604544Proofs.DescriptiveComplexity.sgMapRel

end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

/-! ### NP-completeness -/

end Lax604544Proofs.DescriptiveComplexity


