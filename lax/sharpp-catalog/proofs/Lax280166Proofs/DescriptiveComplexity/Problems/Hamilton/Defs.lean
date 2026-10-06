/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Vocabulary
import Lax280166Proofs.DescriptiveComplexity.Numbers.BinRel
import Lax280166Proofs.DescriptiveComplexity.Interpretation
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

namespace Lax799700.Hamilton
end Lax799700.Hamilton

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Hamilton (DGArc DGEdge HasDirHamCircuit HasHamCircuit SuccOf TourOn)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Hamilton (dgArc digraph)
end FirstOrder.Language

/-!
# Hamilton circuits: definitions

DIRECTED HAMILTON CIRCUIT and (undirected) HAMILTON CIRCUIT
([Karp 1972][karp1972reducibility]): does a graph have a circuit visiting
every vertex exactly once? Both live on the same vocabulary
`FirstOrder.Language.digraph`, a single binary relation `arc`; the undirected
problem reads that relation *symmetrically*
(`DescriptiveComplexity.DGEdge`), which is the honest reading of an undirected
graph presented by a possibly asymmetric edge relation.

## A circuit is a linear order

A Hamilton circuit is a cyclic enumeration of the universe, and cutting it
anywhere turns it into a **linear order whose consecutive elements are
adjacent and whose last element is adjacent to its first**
(`DescriptiveComplexity.TourOn`). That reading is what makes the problem `Σ₁`: a
relation is what an existential second-order block can guess, and “being a
linear order”, “being the immediate successor” and the two adjacency demands
are first-order. It is the same device the job-sequencing certificate uses for
its schedule, one dimension down: there the order is a *sequence* of the
universe, here it is a *cycle* of it.

On the empty universe every condition is vacuous, so the empty graph counts as
a yes-instance; on a one-element universe the wrap-around demand becomes a
self-loop, which is the usual convention.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Tours of a relation -/

section Tour

variable {A : Type}

variable {B : Type}

/-- Being the immediate successor transports along an equivalence. -/
theorem succOf_equiv (u : A ≃ B) {Le : A → A → Prop} {x y : A} :
    Lax799700.Hamilton.SuccOf (fun b b' => Le (u.symm b) (u.symm b')) (u x) (u y) ↔ Lax799700.Hamilton.SuccOf Le x y := by
  simp only [Lax799700.Hamilton.SuccOf, Equiv.symm_apply_apply]
  refine and_congr Iff.rfl (and_congr ⟨fun h he => h (congrArg u he), fun h he => h ?_⟩ ?_)
  · simpa using congrArg u.symm he
  · constructor
    · intro h z h₁ h₂
      have := h (u z) (by simpa using h₁) (by simpa using h₂)
      simpa using this.imp (congrArg u.symm) (congrArg u.symm)
    · intro h z h₁ h₂
      have := h (u.symm z) h₁ h₂
      exact this.imp (fun hz => by simpa using congrArg u hz) fun hz => by simpa using congrArg u hz

/-- Having a tour transports along an equivalence commuting with the two
relations. -/
theorem tourOn_of_equiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) (h : Lax799700.Hamilton.TourOn RA) : Lax799700.Hamilton.TourOn RB := by
  obtain ⟨Le, hlin, hsucc, hwrap⟩ := h
  refine ⟨fun b b' => Le (u.symm b) (u.symm b'), IsLinOrd.of_equiv u (fun a a' => by simp) hlin,
    fun b b' hb => ?_, fun b b' hb hb' => ?_⟩
  · have h' : Lax799700.Hamilton.SuccOf Le (u.symm b) (u.symm b') := by
      rw [← succOf_equiv u]
      simpa using hb
    simpa using (hR _ _).mp (hsucc _ _ h')
  · have h₁ : ∀ z : A, Le (u.symm b) z := fun z => by simpa using hb (u z)
    have h₂ : ∀ z : A, Le z (u.symm b') := fun z => by simpa using hb' (u z)
    simpa using (hR _ _).mp (hwrap _ _ h₁ h₂)

end Tour

/-! ### The two problems -/

section Problems

variable {A : Type} [Lax799700.Hamilton.digraph.Structure A]

end Problems

section Iso

variable {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B]

private theorem dgArc_equiv (e : A ≃[Lax799700.Hamilton.digraph] B) (a a' : A) :
    Lax799700.Hamilton.DGArc a a' ↔ Lax799700.Hamilton.DGArc (e a) (e a') :=
  relMap_equiv₂ e Lax799700.Hamilton.dgArc a a'

private theorem hasDirHamCircuit_of_iso (e : A ≃[Lax799700.Hamilton.digraph] B)
    (h : Lax799700.Hamilton.HasDirHamCircuit A) : Lax799700.Hamilton.HasDirHamCircuit B :=
  ⟨e.toEquiv.finite_iff.mp h.1, tourOn_of_equiv e.toEquiv (dgArc_equiv e) h.2⟩

private theorem hasHamCircuit_of_iso (e : A ≃[Lax799700.Hamilton.digraph] B)
    (h : Lax799700.Hamilton.HasHamCircuit A) : Lax799700.Hamilton.HasHamCircuit B :=
  ⟨e.toEquiv.finite_iff.mp h.1,
    tourOn_of_equiv e.toEquiv (fun a a' => or_congr (dgArc_equiv e a a') (dgArc_equiv e a' a)) h.2⟩

/-- Having a directed Hamilton circuit is isomorphism-invariant. -/
theorem hasDirHamCircuit_iso (e : A ≃[Lax799700.Hamilton.digraph] B) :
    Lax799700.Hamilton.HasDirHamCircuit A ↔ Lax799700.Hamilton.HasDirHamCircuit B :=
  ⟨hasDirHamCircuit_of_iso e, hasDirHamCircuit_of_iso e.symm⟩

/-- Having a Hamilton circuit is isomorphism-invariant. -/
theorem hasHamCircuit_iso (e : A ≃[Lax799700.Hamilton.digraph] B) :
    Lax799700.Hamilton.HasHamCircuit A ↔ Lax799700.Hamilton.HasHamCircuit B :=
  ⟨hasHamCircuit_of_iso e, hasHamCircuit_of_iso e.symm⟩

end Iso

/-- DIRECTED HAMILTON CIRCUIT, as a problem on digraphs: is there a circuit
following the arcs and visiting every vertex exactly once? -/
def DirHamCircuit : Lax904597.Problems.DecisionProblem Lax799700.Hamilton.digraph where
  Holds := fun A inst => @Lax799700.Hamilton.HasDirHamCircuit A inst
  iso_invariant := fun e => hasDirHamCircuit_iso e

/-- HAMILTON CIRCUIT, as a problem on digraphs read symmetrically: is there a
circuit following the edges and visiting every vertex exactly once? -/
def HamCircuit : Lax904597.Problems.DecisionProblem Lax799700.Hamilton.digraph where
  Holds := fun A inst => @Lax799700.Hamilton.HasHamCircuit A inst
  iso_invariant := fun e => hasHamCircuit_iso e

end Lax280166Proofs.DescriptiveComplexity


