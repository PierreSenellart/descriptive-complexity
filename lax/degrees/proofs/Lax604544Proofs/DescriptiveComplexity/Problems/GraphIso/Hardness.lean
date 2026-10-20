/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Problems.GraphIso.Defs
import Lax604544Proofs.DescriptiveComplexity.Problems.GraphIso.Gadget
import Lax604544Proofs.DescriptiveComplexity.Problems.DigraphIso.Bridge
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

namespace Lax604544.GraphIsomorphism
end Lax604544.GraphIsomorphism

namespace Lax799700.SubgraphIso
end Lax799700.SubgraphIso

namespace Lax604544Proofs.DescriptiveComplexity
export Lax604544.GraphIsomorphism (SimpleOn)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax799700.SubgraphIso (TGHostE TGHostV TGPatE TGPatV)
end Lax604544Proofs.DescriptiveComplexity

/-!
# Graph Isomorphism is GI-complete

The last step: the gadget of `DescriptiveComplexity.Problems.GraphIso.Gadget`,
doubled by `DescriptiveComplexity.GadgetDouble` and read through the renaming
of `DescriptiveComplexity.Problems.DigraphIso.Bridge`, reduces Digraph
Isomorphism to Graph Isomorphism. Since simplicity is first-order the converse
reduction is a gated copy (`DescriptiveComplexity.Problems.GraphIso.Defs`), so
the two problems are interreducible and the degree they define is the same.

The one thing the doubling does not carry by itself is *simplicity*: its target
is the unrestricted `DescriptiveComplexity.TwoCopiesIso`, while
`DescriptiveComplexity.GraphIso` asks its instances to be simple graphs. That
is discharged here, by transporting the gadget's symmetry and irreflexivity
(`DescriptiveComplexity.GraphGadget.edge_symm`,
`DescriptiveComplexity.GraphGadget.edge_irrefl`) along the identification of
the sides of a doubled construction with the gadget's values
(`DescriptiveComplexity.patSideDoubleEquiv`).
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure GraphGadget

namespace GraphHard

/-! ### The doubled gadget builds simple graphs -/

section Simple

variable {Z : Type} [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure Z]

/-- The pattern side of the doubled gadget is a simple graph: its adjacency is
the gadget's, which is symmetric and loopless. -/
theorem simpleOn_pat :
    Lax604544.GraphIsomorphism.SimpleOn (TCPatMark (L₁ := Language.graph) (A := gadget.double.Map Z))
      DigraphBridge.TCPatAdj := by
  have hside : ∀ (x y : gadget.double.Map Z) (hx : TCPatMark (L₁ := Language.graph) x)
      (hy : TCPatMark (L₁ := Language.graph) y),
      DigraphBridge.TCPatAdj x y ↔
        GEdge (patSideDoubleEquiv gadget ⟨x, hx⟩) (patSideDoubleEquiv gadget ⟨y, hy⟩) := by
    intro x y hx hy
    rw [← DigraphBridge.patSide_relMap ⟨x, hx⟩ ⟨y, hy⟩]
    have h := (patSideDoubleEquiv (L₀ := Language.graph) gadget (A := Z)).map_rel'
      Language.adj ![(⟨x, hx⟩ : {p : gadget.double.Map Z // TCPatMark p}), ⟨y, hy⟩]
    rw [show ((patSideDoubleEquiv (L₀ := Language.graph) gadget (A := Z)).toFun ∘
        ![(⟨x, hx⟩ : {p : gadget.double.Map Z // TCPatMark p}), ⟨y, hy⟩])
        = ![patSideDoubleEquiv gadget ⟨x, hx⟩, patSideDoubleEquiv gadget ⟨y, hy⟩] by
      funext i; fin_cases i <;> rfl] at h
    exact h.symm
  constructor
  · intro x y hx hy hxy
    rw [hside x y hx hy] at hxy
    rw [hside y x hy hx]
    exact (edge_symm _ _).mp hxy
  · intro x hx hxx
    rw [hside x x hx hx] at hxx
    exact edge_irrefl _ hxx

/-- The host side of the doubled gadget is a simple graph. -/
theorem simpleOn_host :
    Lax604544.GraphIsomorphism.SimpleOn (TCHostMark (L₁ := Language.graph) (A := gadget.double.Map Z))
      DigraphBridge.TCHostAdj := by
  have hside : ∀ (x y : gadget.double.Map Z) (hx : TCHostMark (L₁ := Language.graph) x)
      (hy : TCHostMark (L₁ := Language.graph) y),
      DigraphBridge.TCHostAdj x y ↔
        GEdge (hostSideDoubleEquiv gadget ⟨x, hx⟩) (hostSideDoubleEquiv gadget ⟨y, hy⟩) := by
    intro x y hx hy
    rw [← DigraphBridge.hostSide_relMap ⟨x, hx⟩ ⟨y, hy⟩]
    have h := (hostSideDoubleEquiv (L₀ := Language.graph) gadget (A := Z)).map_rel'
      Language.adj ![(⟨x, hx⟩ : {p : gadget.double.Map Z // TCHostMark p}), ⟨y, hy⟩]
    rw [show ((hostSideDoubleEquiv (L₀ := Language.graph) gadget (A := Z)).toFun ∘
        ![(⟨x, hx⟩ : {p : gadget.double.Map Z // TCHostMark p}), ⟨y, hy⟩])
        = ![hostSideDoubleEquiv gadget ⟨x, hx⟩, hostSideDoubleEquiv gadget ⟨y, hy⟩] by
      funext i; fin_cases i <;> rfl] at h
    exact h.symm
  constructor
  · intro x y hx hy hxy
    rw [hside x y hx hy] at hxy
    rw [hside y x hy hx]
    exact (edge_symm _ _).mp hxy
  · intro x hx hxx
    rw [hside x x hx hx] at hxx
    exact edge_irrefl _ hxx

end Simple

/-! ### Reading the result in the hand-rolled vocabulary -/

section Read

variable {Y : Type} [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure Y]

/-- If the two sides of a generic instance are simple, so are the two sides of
its renaming into `FirstOrder.Language.twoGraphs`. -/
theorem simpleOn_ofTC_pat
    (h : Lax604544.GraphIsomorphism.SimpleOn (TCPatMark (L₁ := Language.graph) (A := Y)) DigraphBridge.TCPatAdj) :
    Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGPatV (A := DigraphBridge.ofTC.Map Y)) Lax799700.SubgraphIso.TGPatE := by
  obtain ⟨hsymm, hirr⟩ := h
  constructor
  · intro x y hx hy hxy
    rw [DigraphBridge.ofTC_patE] at hxy ⊢
    exact hsymm _ _ ((DigraphBridge.ofTC_patV x).mp hx) ((DigraphBridge.ofTC_patV y).mp hy) hxy
  · intro x hx hxx
    rw [DigraphBridge.ofTC_patE] at hxx
    exact hirr _ ((DigraphBridge.ofTC_patV x).mp hx) hxx

@[inherit_doc simpleOn_ofTC_pat]
theorem simpleOn_ofTC_host
    (h : Lax604544.GraphIsomorphism.SimpleOn (TCHostMark (L₁ := Language.graph) (A := Y)) DigraphBridge.TCHostAdj) :
    Lax604544.GraphIsomorphism.SimpleOn (Lax799700.SubgraphIso.TGHostV (A := DigraphBridge.ofTC.Map Y)) Lax799700.SubgraphIso.TGHostE := by
  obtain ⟨hsymm, hirr⟩ := h
  constructor
  · intro x y hx hy hxy
    rw [DigraphBridge.ofTC_hostE] at hxy ⊢
    exact hsymm _ _ ((DigraphBridge.ofTC_hostV x).mp hx) ((DigraphBridge.ofTC_hostV y).mp hy) hxy
  · intro x hx hxx
    rw [DigraphBridge.ofTC_hostE] at hxx
    exact hirr _ ((DigraphBridge.ofTC_hostV x).mp hx) hxx

end Read

/-! ### Correctness of the composite -/

section Correct

variable {Z : Type} [(Lax604544Proofs.Foreign.FirstOrder.Language.twoCopies Language.graph).Structure Z] [Finite Z]

/-- **The doubled gadget, renamed, reduces the generic isomorphism problem to
Graph Isomorphism.** Simplicity of the image is what upgrades the target from
the unrestricted problem to the simple-graph one. -/
theorem twoCopiesIso_iff_graphIso_map :
    (TwoCopiesIso Language.graph).Holds Z ↔
      GraphIso.Holds (DigraphBridge.ofTC.Map (gadget.double.Map Z)) := by
  have : Finite (gadget.double.Map Z) := gadget.double.map_finite Z
  rw [twoCopiesIso_double_iff gadget gadget_isoReflecting ‹Finite Z›,
    DigraphBridge.ofTC_correct (gadget.double.Map Z)]
  constructor
  · rintro ⟨hfin, hiso⟩
    exact ⟨hfin, simpleOn_ofTC_pat simpleOn_pat, simpleOn_ofTC_host simpleOn_host, hiso⟩
  · rintro ⟨hfin, -, -, hiso⟩
    exact ⟨hfin, hiso⟩

end Correct

end GraphHard

/-! ### The reduction and the completeness theorem -/

/-- **The generic isomorphism problem reduces to Graph Isomorphism**: subdivide
every arc three times, mark each vertex with a lollipop and each tail with a
pendant, then read the result as a pair of simple graphs. -/
noncomputable def twoCopiesIso_fo_reduction_graphIso :
    TwoCopiesIso Language.graph ≤ᶠᵒ GraphIso where
  Tag := Unit × (Fin 1 → GraphGadget.GTag)
  dim := 1 * 2
  toInterpretation := DigraphBridge.ofTC.comp gadget.double
  correct Z _ _ _ := by
    rw [GraphHard.twoCopiesIso_iff_graphIso_map]
    exact (GraphIso.iso_invariant (DigraphBridge.ofTC.compLEquiv gadget.double Z)).symm

/-- **Digraph Isomorphism reduces to Graph Isomorphism**: the classical
digraph-to-graph construction, through the renaming into the generic
vocabulary. -/
noncomputable def digraphIso_fo_reduction_graphIso : DigraphIso ≤ᶠᵒ GraphIso :=
  digraphIso_fo_reduction_twoCopiesIso.trans twoCopiesIso_fo_reduction_graphIso

/-- **Graph Isomorphism is GI-complete**, the degree being defined on it. -/
theorem graphIso_GI_complete : GI.Complete GraphIso :=
  ComplexityClass.below_complete_self GraphIso

/-- **Digraph Isomorphism is GI-complete too**: it reduces to the undirected
problem by the gadget – every arc subdivided three times, each vertex carrying
a lollipop and each tail a pendant – and the undirected problem reduces back to
it by testing simplicity. The directed problem is *not* what the literature
calls GI, which is why the degree is named after the other one; this theorem is
what says the choice costs nothing. -/
theorem digraphIso_GI_complete : GI.Complete DigraphIso :=
  ⟨⟨digraphIso_fo_reduction_graphIso.toOrdered⟩,
    GI.hard_of_foReduction graphIso_fo_reduction_digraphIso graphIso_GI_complete.hard⟩

/-- **The directed and undirected problems have the same degree.** -/
theorem GI_eq_below_digraphIso : GI = ComplexityClass.below DigraphIso :=
  ComplexityClass.below_congr ⟨graphIso_fo_reduction_digraphIso.toOrdered⟩
    ⟨digraphIso_fo_reduction_graphIso.toOrdered⟩

end Lax604544Proofs.DescriptiveComplexity


