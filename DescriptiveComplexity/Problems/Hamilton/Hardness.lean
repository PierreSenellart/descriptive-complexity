/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Gadget
import DescriptiveComplexity.Problems.Hamilton.Cycle
import DescriptiveComplexity.Problems.Hamilton.Forward
import DescriptiveComplexity.Problems.Hamilton.Reverse
import DescriptiveComplexity.Problems.CliqueFamily
import Mathlib.Data.Fintype.Lattice

/-!
# Vertex Cover reduces to Hamilton Circuit

Assembles the relativized ordered first-order reduction
`DescriptiveComplexity.vertexCover_rel_ordered_fo_reduction_hamCircuit` out of the
gadget interpretation `DescriptiveComplexity.hamInterp` of `Gadget`, from which the
umbrella `DescriptiveComplexity.Problems.Hamilton` derives the NP-hardness of
HAMILTON CIRCUIT (hence, through the existing reduction to the directed
problem, of DIRECTED HAMILTON CIRCUIT).

The interpretation carries a **domain formula** (it is a
`DescriptiveComplexity.RelFOInterpretation`), so it is the first reduction of the catalog
targeting a *spanning* problem, where a yes-witness must visit every universe
element. The reduction's extra obligation `dom_nonempty` – a definable domain
can be empty on a nonempty input – is discharged here: a marked vertex yields a
selector, an edge yields a gadget vertex, and the degenerate input with neither
yields the hub.

The correctness of the interpretation
(`DescriptiveComplexity.hasSmallVertexCover_iff_hamCircuit_mapRel`) splits into the two
classical directions, proved in `Forward` and `Reverse` and linked here.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section DomNonempty

variable (A : Type) [Language.markedGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The definable domain is inhabited.** A marked vertex gives a selector, an
edge gives a gadget vertex, and the degenerate input with no marks and no edges
gives the hub, at the minimum. -/
theorem hamInterp_dom_nonempty :
    ∃ (t : HTag) (w : Fin 2 → A), (hamInterp.domFormula t).Realize w := by
  by_cases hm : ∃ m : A, MGMarked m
  · obtain ⟨m, hm⟩ := hm
    exact ⟨.sel, ![m, m], (dom_sel ![m, m]).mpr ⟨rfl, by simpa using hm⟩⟩
  · by_cases he : ∃ a b : A, HEdge a b
    · obtain ⟨a, b, he⟩ := he
      exact ⟨.g0, ![a, b], (dom_gadget .g0 ⟨by decide, by decide⟩ ![a, b]).mpr (by simpa using he)⟩
    · obtain ⟨m, hmin⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
      have hm' : ∀ y : A, ¬MGMarked y := fun y hy => hm ⟨y, hy⟩
      have he' : ∀ y z : A, ¬HEdge y z := fun y z hyz => he ⟨y, z, hyz⟩
      exact ⟨.hub, ![m, m], (dom_hub ![m, m]).mpr ⟨rfl, by simpa using hmin, hm', he'⟩⟩

end DomNonempty

section Correct

variable (A : Type) [Language.markedGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **Forward direction**: a vertex cover of size at most the marked set yields
a Hamilton circuit of the gadget graph. When there is a marked vertex it is the
explicit cycle of `DescriptiveComplexity.blockCycle_tourOn` – selectors threaded with the
cover vertices' chains; otherwise (no marks, hence no edges) it is the single
self-looped hub (`DescriptiveComplexity.degenerate_tourOn`). -/
theorem cover_to_tour (hcov : CoverOn (MGAdj (A := A)) (MGMarked (A := A))) :
    TourOn (DGEdge (A := hamInterp.MapRel A)) := by
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨C, hcp, hcard⟩ := hcov
  have hcover : ∀ a b : A, HEdge a b → C a ∨ C b := by
    intro a b h
    rcases h.1 with hab | hba
    · exact hcp a b h.2 hab
    · exact (hcp b a (fun e => h.2 e.symm) hba).symm
  by_cases hmarks : ∃ m : A, MGMarked m
  · exact blockCycle_tourOn hcard hcover hmarks
  · simp only [not_exists] at hmarks
    have hmk0 : {x : A | MGMarked x}.ncard = 0 :=
      (Set.ncard_eq_zero (Set.toFinite _)).mpr (Set.eq_empty_iff_forall_notMem.mpr hmarks)
    have hCe : {x : A | C x} = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp (hmk0 ▸ hcard))
    have hCempty : ∀ x, ¬C x := fun x => Set.eq_empty_iff_forall_notMem.mp hCe x
    have hne : ∀ y z : A, ¬HEdge y z := fun y z h =>
      (hcover y z h).elim (hCempty y) (hCempty z)
    exact degenerate_tourOn hmarks hne

omit [Nonempty A] in
/-- **Reverse direction**: a Hamilton circuit of the gadget graph yields a
vertex cover at most as large as the marked set. The local gadget analysis
forces each edge's gadget to be traversed through the `u`-side, the `v`-side or
both (never neither), and the number of active chains is at most the number of
selectors.

The counting injection `DescriptiveComplexity.active_ncard_le` bounds the active set by
the marked set; the cover property `DescriptiveComplexity.cover_property` (the local
traversal analysis) shows every edge has an active endpoint. -/
theorem tour_to_cover (htour : TourOn (DGEdge (A := hamInterp.MapRel A))) :
    CoverOn (MGAdj (A := A)) (MGMarked (A := A)) := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Finite (hamInterp.MapRel A) := hamInterp.mapRel_finite A
  obtain ⟨N, f, hf⟩ := enum_of_tourOn htour
  by_cases hedge : ∃ a b : A, HEdge a b
  · obtain ⟨a0, b0, he0⟩ := hedge
    haveI : Nonempty (hamInterp.MapRel A) := ⟨gPt .g0 ⟨by decide, by decide⟩ he0⟩
    exact ⟨Active f, fun x y hxy hadj => cover_property f hf ⟨Or.inl hadj, hxy⟩,
      active_ncard_le f⟩
  · refine ⟨fun _ => False, fun x y hxy hadj => absurd (⟨Or.inl hadj, hxy⟩ : HEdge x y)
      (fun he => hedge ⟨x, y, he⟩), ?_⟩
    simp only [Set.setOf_false, Set.ncard_empty, Nat.zero_le]

/-- **Correctness of the gadget interpretation**: a marked graph has a vertex
cover at most as large as its marked set iff its gadget graph has a Hamilton
circuit. The finiteness of the target universe is `mapRel_finite`; the two
directions are `DescriptiveComplexity.cover_to_tour` and
`DescriptiveComplexity.tour_to_cover`. -/
theorem hasSmallVertexCover_iff_hamCircuit_mapRel :
    HasSmallVertexCover A ↔ HasHamCircuit (hamInterp.MapRel A) := by
  haveI : Finite (hamInterp.MapRel A) := hamInterp.mapRel_finite A
  rw [HasSmallVertexCover, HasHamCircuit, and_iff_right ‹Finite A›, and_iff_right this]
  exact ⟨cover_to_tour A, tour_to_cover A⟩

end Correct

/-- **Vertex Cover relativized-ordered-FO-reduces to Hamilton Circuit**: the
twelve-vertex cover-testing gadget of each edge, chained along every vertex's
neighbour list, with the marked vertices as selectors and a degenerate-case
hub. The domain formula cuts the target universe down to the real gadget,
selector and hub vertices – Immerman's definable-subset reduction, needed
because HAMILTON CIRCUIT is a spanning problem. -/
noncomputable def vertexCover_rel_ordered_fo_reduction_hamCircuit :
    VertexCover ≤ʳᶠᵒ[≤] HamCircuit where
  Tag := HTag
  dim := 2
  toRelInterpretation := hamInterp
  dom_nonempty := fun A => hamInterp_dom_nonempty A
  correct := fun A _ _ _ _ => hasSmallVertexCover_iff_hamCircuit_mapRel A

end DescriptiveComplexity
