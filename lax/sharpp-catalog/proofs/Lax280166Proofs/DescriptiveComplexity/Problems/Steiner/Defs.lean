/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Vocabulary
import Lax280166Proofs.DescriptiveComplexity.Interpretation
import Lax280166Proofs.DescriptiveComplexity.Numbers.Unary
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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

namespace Lax280166Proofs.DescriptiveComplexity.ConnectedOn
end Lax280166Proofs.DescriptiveComplexity.ConnectedOn

namespace Lax280166Proofs.DescriptiveComplexity.SteinerEdgeOn
end Lax280166Proofs.DescriptiveComplexity.SteinerEdgeOn

namespace Lax280166Proofs.DescriptiveComplexity.SteinerOn
end Lax280166Proofs.DescriptiveComplexity.SteinerOn

namespace Lax799700.Steiner
end Lax799700.Steiner

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Steiner (ConnectedOn HasSmallEdgeSteinerTree HasSmallSteinerTree Link STAdj STMarked STTerminal SteinerEdgeOn SteinerOn)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Steiner (stAdj stMarked stTerminal steinerGraph)
end FirstOrder.Language

/-!
# Steiner Tree: definitions

STEINER TREE ([Karp 1972][karp1972reducibility]) in its *node-weighted* form
with unit weights: given a graph, a set of *terminals* and a threshold `k`, is
there a connected set of vertices containing every terminal and using at most
`k` non-terminals? The vocabulary `FirstOrder.Language.steinerGraph` is that of
graphs with two unary marks – the terminals, and the marked set carrying `k`
in the *unary representation* of `DescriptiveComplexity.Numbers.Unary`.

Karp's original problem weights *edges* and bounds the total weight; on a tree
the two readings differ by one (`#edges = #vertices - 1`), so the reduction
below would carry over, but the bridge between them needs the fact that a
connected graph has at least `n - 1` edges. Mathlib has it only for trees on a
whole vertex type (`SimpleGraph.IsTree.card_edgeFinset`), so the edge-weighted
version waits for that glue; the node-weighted version is the standard variant
and is what this file formalizes.

## Connectivity, and its first-order certificate

Connectivity (`DescriptiveComplexity.ConnectedOn`) is stated with
`Relation.ReflTransGen` over the *symmetric* restriction of adjacency to the
chosen set, so it is the usual undirected notion and is not first-order. As
for acyclicity in `DescriptiveComplexity.Problems.Feedback`, what saves the
membership proof is a certificate: a root of the chosen set together with a
strict partial order in which every other chosen vertex has a chosen neighbor
strictly below it (`DescriptiveComplexity.connectedOn_iff_exists_root_order`). Walking
down that order reaches the root, and the root joins any two vertices.

Producing the certificate from connectivity is the direction with content: it
needs a *distance*, which `Relation.ReflTransGen` does not carry. The
`DescriptiveComplexity.reachIn` staging below supplies it – reachability in at most
`n` steps, with `Nat.find` picking the least such `n` – and that is the whole
of the extra machinery. It is stated for an arbitrary relation, so the
Hamilton problems and the edge-weighted Steiner tree can reuse it.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Connectivity and its certificate -/

section Connectivity

variable {A : Type}

theorem link_symm {Adjp : A → A → Prop} {S : A → Prop} {a b : A} (h : Lax799700.Steiner.Link Adjp S a b) :
    Lax799700.Steiner.Link Adjp S b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

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

/-- The reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem reflTransGen_symm {R : A → A → Prop} (hsymm : ∀ a b, R a b → R b a) {x y : A}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

/-! #### The certificate -/

/-- `ConnectedOn` transports along an equivalence commuting with the
adjacency relations and the chosen sets. -/
theorem ConnectedOn.of_equiv {B : Type} (u : B ≃ A) {AdjB : B → B → Prop} {SB : B → Prop}
    {AdjA : A → A → Prop} {SA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hS : ∀ b, SB b ↔ SA (u b))
    (h : Lax799700.Steiner.ConnectedOn AdjB SB) : Lax799700.Steiner.ConnectedOn AdjA SA := by
  have hlink : ∀ a a', Lax799700.Steiner.Link AdjA SA a a' → Lax799700.Steiner.Link AdjB SB (u.symm a) (u.symm a') := by
    rintro a a' ⟨h₁, h₂, h₃⟩
    exact ⟨(hS _).mpr (by simpa using h₁), (hS _).mpr (by simpa using h₂),
      by rcases h₃ with h | h
         · exact Or.inl ((hadj _ _).mpr (by simpa using h))
         · exact Or.inr ((hadj _ _).mpr (by simpa using h))⟩
  intro x y hx hy
  have hxy := h (u.symm x) (u.symm y) ((hS _).mpr (by simpa using hx))
    ((hS _).mpr (by simpa using hy))
  have hmap : ∀ {b b' : B}, Relation.ReflTransGen (Lax799700.Steiner.Link AdjB SB) b b' →
      Relation.ReflTransGen (Lax799700.Steiner.Link AdjA SA) (u b) (u b') := by
    intro b b' hb
    induction hb with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hcd ih =>
      refine ih.tail ⟨(hS _).mp hcd.1, (hS _).mp hcd.2.1, ?_⟩
      rcases hcd.2.2 with h | h
      · exact Or.inl ((hadj _ _).mp h)
      · exact Or.inr ((hadj _ _).mp h)
  simpa using hmap hxy

end Connectivity

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.Steiner.ConnectedOn

export Lax280166Proofs.DescriptiveComplexity.ConnectedOn (of_equiv)

end Lax799700.Steiner.ConnectedOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Connectivity

variable {A : Type}

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

/-- `SteinerOn` transports along an equivalence commuting with the three
predicates. -/
theorem SteinerOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) (h : Lax799700.Steiner.SteinerOn AdjB TermB KB) :
    Lax799700.Steiner.SteinerOn AdjA TermA KA := by
  obtain ⟨S, hterms, hconn, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), fun x hx => hterms _ ((hterm _).mpr (by simpa using hx)),
    ConnectedOn.of_equiv u hadj (fun b => by simp) hconn, ?_⟩
  rw [← ncard_setOf_equiv u hK,
    ← ncard_setOf_equiv (KB := fun b => S b ∧ ¬TermB b) u (fun b => by
      simp only [hterm b]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using h₁, h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using h₁, h₂⟩)]
  exact hcard

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.Steiner.SteinerOn

export Lax280166Proofs.DescriptiveComplexity.SteinerOn (of_equiv)

end Lax799700.Steiner.SteinerOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `SteinerOn` transports along an equivalence, iff version. -/
theorem SteinerOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) : Lax799700.Steiner.SteinerOn AdjB TermB KB ↔ Lax799700.Steiner.SteinerOn AdjA TermA KA :=
  ⟨SteinerOn.of_equiv u hadj hterm hK,
    SteinerOn.of_equiv u.symm (fun a a' => by rw [hadj]; simp) (fun a => by rw [hterm]; simp)
      fun a => by rw [hK]; simp⟩

end Generic

end Lax280166Proofs.DescriptiveComplexity

namespace Lax799700.Steiner.SteinerOn

export Lax280166Proofs.DescriptiveComplexity.SteinerOn (equiv_iff)

end Lax799700.Steiner.SteinerOn

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

section Problem

section Shorthands

variable {A : Type} [Lax799700.Steiner.steinerGraph.Structure A]

end Shorthands

variable (A : Type) [Lax799700.Steiner.steinerGraph.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A] [Lax799700.Steiner.steinerGraph.Structure B]

/-- The Steiner-tree property is isomorphism-invariant. -/
theorem hasSmallSteinerTree_iso (e : A ≃[Lax799700.Steiner.steinerGraph] B) :
    Lax799700.Steiner.HasSmallSteinerTree A ↔ Lax799700.Steiner.HasSmallSteinerTree B :=
  and_congr e.toEquiv.finite_iff
    (SteinerOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e Lax799700.Steiner.stAdj a b)
      (fun a => relMap_equiv₁ e Lax799700.Steiner.stTerminal a) fun a => relMap_equiv₁ e Lax799700.Steiner.stMarked a)

end Iso

/-- STEINER TREE (node-weighted, unit weights), as a problem on graphs with
terminals: is there a connected set of vertices containing every terminal and
using at most as many non-terminals as the marked set has elements? -/
def SteinerTree : Lax904597.Problems.DecisionProblem Lax799700.Steiner.steinerGraph where
  Holds := fun A inst => @Lax799700.Steiner.HasSmallSteinerTree A inst
  iso_invariant := fun e => hasSmallSteinerTree_iso e

end Lax280166Proofs.DescriptiveComplexity


