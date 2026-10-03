/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax117614Proofs.DescriptiveComplexity.Vocabulary
import Lax117614Proofs.DescriptiveComplexity.Interpretation
import Lax117614Proofs.DescriptiveComplexity.Numbers.Unary
import Lax117614.CrawlInstances
import Lax117614.GraphCrawlingProblem
import Lax117614.WebsiteGraphs
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

/-!
# Steiner Tree: definitions

STEINER TREE ([Karp 1972][karp1972reducibility]) in its *node-weighted* form
with unit weights: given a graph, a set of *terminals* and a threshold `k`, is
there a connected set of vertices containing every terminal and using at most
`k` non-terminals? The vocabulary `FirstOrder.Language.steinerGraph` is that of
graphs with two unary marks – the terminals, and the marked set carrying `k`
in the *unary representation* of `Lax117614Proofs.DescriptiveComplexity.Numbers.Unary`.

Karp's original problem weights *edges* and bounds the total weight; on a tree
the two readings differ by one (`#edges = #vertices - 1`), so the reduction
below would carry over, but the bridge between them needs the fact that a
connected graph has at least `n - 1` edges. Mathlib has it only for trees on a
whole vertex type (`SimpleGraph.IsTree.card_edgeFinset`), so the edge-weighted
version waits for that glue; the node-weighted version is the standard variant
and is what this file formalizes.

## Connectivity, and its first-order certificate

Connectivity (`Lax117614Proofs.DescriptiveComplexity.ConnectedOn`) is stated with
`Relation.ReflTransGen` over the *symmetric* restriction of adjacency to the
chosen set, so it is the usual undirected notion and is not first-order. As
for acyclicity in `Lax117614Proofs.DescriptiveComplexity.Problems.Feedback`, what saves the
membership proof is a certificate: a root of the chosen set together with a
strict partial order in which every other chosen vertex has a chosen neighbor
strictly below it (`Lax117614Proofs.DescriptiveComplexity.connectedOn_iff_exists_root_order`). Walking
down that order reaches the root, and the root joins any two vertices.

Producing the certificate from connectivity is the direction with content: it
needs a *distance*, which `Relation.ReflTransGen` does not carry. The
`Lax117614Proofs.DescriptiveComplexity.reachIn` staging below supplies it – reachability in at most
`n` steps, with `Nat.find` picking the least such `n` – and that is the whole
of the extra machinery. It is stated for an arbitrary relation, so the
Hamilton problems and the edge-weighted Steiner tree can reuse it.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Connectivity and its certificate -/

section Connectivity

variable {A : Type}

/-! #### Reachability in a bounded number of steps

`Relation.ReflTransGen` carries no length, and the certificate needs one: the
order it guesses is “distance to the root”. -/

/-- Reachability in at most `n` steps. -/
def reachIn (R : A → A → Prop) : ℕ → A → A → Prop
  | 0, x, y => x = y
  | n + 1, x, y => reachIn R n x y ∨ ∃ z, reachIn R n x z ∧ R z y

/-- Reachability is reachability in some bounded number of steps. -/
theorem reflTransGen_iff_exists_reachIn (R : A → A → Prop) (x y : A) :
    Relation.ReflTransGen R x y ↔ ∃ n, reachIn R n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, hn, hbc⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing y with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ k ih =>
      rcases hn with h | ⟨z, hz, hzy⟩
      · exact ih _ h
      · exact (ih _ hz).tail hzy

/-! #### The certificate -/

end Connectivity

/-! #### Connectivity costs edges

The certificate gives each non-root member of a connected set a *parent edge*,
and that assignment is injective: two members sharing an edge would have to be
each other's parent, hence strictly below each other. This is the
`n - 1` edge bound for connected graphs, in the form the edge-weighted Steiner
tree needs, and it is proved from the certificate rather than from a spanning
tree. -/

/-! ### The problem -/

section Generic

variable {A : Type}

variable {B : Type}

end Generic

section Problem

section Shorthands

end Shorthands

end Problem

section Iso

end Iso

end Lax117614Proofs.DescriptiveComplexity


