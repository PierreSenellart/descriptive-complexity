/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.GraphIso.Defs
import DescriptiveComplexity.Problems.GraphIso.Gadget
import DescriptiveComplexity.Problems.DigraphIso.Bridge

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure GraphGadget

namespace GraphHard

/-! ### The doubled gadget builds simple graphs -/

section Simple

variable {Z : Type} [(Language.twoCopies Language.graph).Structure Z]

/-- The pattern side of the doubled gadget is a simple graph: its adjacency is
the gadget's, which is symmetric and loopless. -/
theorem simpleOn_pat :
    SimpleOn (TCPatMark (L₁ := Language.graph) (A := gadget.double.Map Z))
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
    SimpleOn (TCHostMark (L₁ := Language.graph) (A := gadget.double.Map Z))
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

variable {Y : Type} [(Language.twoCopies Language.graph).Structure Y]

/-- If the two sides of a generic instance are simple, so are the two sides of
its renaming into `FirstOrder.Language.twoGraphs`. -/
theorem simpleOn_ofTC_pat
    (h : SimpleOn (TCPatMark (L₁ := Language.graph) (A := Y)) DigraphBridge.TCPatAdj) :
    SimpleOn (TGPatV (A := DigraphBridge.ofTC.Map Y)) TGPatE := by
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
    (h : SimpleOn (TCHostMark (L₁ := Language.graph) (A := Y)) DigraphBridge.TCHostAdj) :
    SimpleOn (TGHostV (A := DigraphBridge.ofTC.Map Y)) TGHostE := by
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

variable {Z : Type} [(Language.twoCopies Language.graph).Structure Z] [Finite Z]

/-- **The doubled gadget, renamed, reduces the generic isomorphism problem to
Graph Isomorphism.** Simplicity of the image is what upgrades the target from
the unrestricted problem to the simple-graph one. -/
theorem twoCopiesIso_iff_graphIso_map :
    (TwoCopiesIso Language.graph).Holds Z ↔
      GraphIso.Holds (DigraphBridge.ofTC.Map (gadget.double.Map Z)) := by
  haveI : Finite (gadget.double.Map Z) := gadget.double.map_finite Z
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

/-- **Graph Isomorphism is GI-complete**: it reduces to Digraph Isomorphism by
testing simplicity, and Digraph Isomorphism reduces back to it by the gadget.
This is the statement in the shape the literature uses – GI is the problem for
*simple* graphs – and it says the directed and undirected problems have the
same degree. -/
theorem graphIso_GI_complete : GI.Complete GraphIso :=
  ⟨graphIso_mem_GI,
    GI.hard_of_foReduction digraphIso_fo_reduction_graphIso digraphIso_GI_complete.hard⟩

/-- **The GI degree is the degree of the undirected problem.** The anchor can
therefore move to `DescriptiveComplexity.GraphIso`, which is what the
literature means by GI, without touching any completeness theorem: they
transfer along this equality. -/
theorem GI_eq_below_graphIso : GI = ComplexityClass.below GraphIso :=
  ComplexityClass.below_congr ⟨digraphIso_fo_reduction_graphIso.toOrdered⟩
    ⟨graphIso_fo_reduction_digraphIso.toOrdered⟩

end DescriptiveComplexity
