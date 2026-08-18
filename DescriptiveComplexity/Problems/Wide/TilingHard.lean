/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Draw
import DescriptiveComplexity.Problems.Wide.TilingHard.No
import DescriptiveComplexity.Problems.Wide.TilingExp
import DescriptiveComplexity.Problems.Wide.RegChannelReduce

/-!
# Tiling a wide square is NEXPTIME-complete

The reduction `WideRegAccept ≤ᶠᵒ[≤] WideTiling`, and with it the completeness of
the wide tiling: the drawing of
`DescriptiveComplexity.Problems.Wide.TilingHard.Tiles` written down as a
three-dimensional ordered interpretation, whose two halves are already proved –

* an accepting run draws a tiling
  (`DescriptiveComplexity.TilingHard.tileable_of_accepts`);
* a tiling is an accepting run
  (`DescriptiveComplexity.TilingHard.wideRegAccept_of_tileable`).

What this file adds is the bridge: the interpreted structure is the emitted one,
symbol by symbol, so the identity is an isomorphism between them and the two
halves apply to the interpretation itself.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-! ### The interpretation -/

/-- **The drawing, as an interpretation**: three dimensions – a tag, a symbol, a
state and a transition – and one formula per symbol of the tile vocabulary. The
bottom row is a parameter, as it is in the drawing itself
(`DescriptiveComplexity.TilingHard.tileStrOf`). -/
noncomputable def tileInterpOf (fF : TileTag → TileTag → wideOrd.Formula (Fin 2 × Fin 3)) :
    FOInterpretation wideOrd Language.wtile TileTag 3 where
  relFormula {n} r :=
    match n, r with
    | _, .wle => fun t => leF (t 0) (t 1)
    | _, .dig => fun t => digF (t 0) 0
    | _, .tile => fun t => tileF (t 0) 0
    | _, .tacc => fun t => accF (t 0) 0
    | _, .horiz => fun t => horizF (t 0) (t 1)
    | _, .vert => fun t => vertF (t 0) (t 1)
    | _, .first => fun t => fF (t 0) (t 1)
    | _, .base => fun t => baseF (t 0) 0
    | _, .tstart => fun t => startF (t 0) 0
    | _, .ledge => fun t => edgeLF (t 0) 0
    | _, .redge => fun t => edgeRF (t 0) 0

/-- **The clocked machine's drawing, as an interpretation**: the bottom row is
the register file. -/
noncomputable def tileInterp : FOInterpretation wideOrd Language.wtile TileTag 3 :=
  tileInterpOf firstF

/-- **And the space-bounded machine's**: the bottom row is the ruler. -/
noncomputable def tileInterpR : FOInterpretation wideOrd Language.wtile TileTag 3 :=
  tileInterpOf firstRF

section Emitted

variable (A : Type) [Language.wide.Structure A] [LinearOrder A]

/-- **The interpreted structure is the emitted one**: the identity map is an
isomorphism, since every symbol's formula was checked against the predicate it
draws. -/
noncomputable def tileEquivOf (F : TilePt A → TilePt A → Prop)
    (fF : TileTag → TileTag → wideOrd.Formula (Fin 2 × Fin 3))
    (hF : ∀ (v : Fin 2 × Fin 3 → A) (t₁ t₂ : TileTag),
      (fF t₁ t₂).Realize v ↔ F (argPt v t₁ 0) (argPt v t₂ 1)) :
    letI := tileStrOf F
    ((tileInterpOf fF).Map A ≃[Language.wtile] (TilePt A)) :=
  letI := tileStrOf F
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} r x => by
      rw [FOInterpretation.relMap_map]
      cases r with
      | wle =>
        refine Iff.trans ?_ (realize_leF (t₁ := (x 0).1) (t₂ := (x 1).1)).symm
        exact Iff.rfl
      | dig =>
        refine Iff.trans ?_ (realize_digF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | tile =>
        refine Iff.trans ?_ (realize_tileF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | tacc =>
        refine Iff.trans ?_ (realize_accF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | horiz =>
        refine Iff.trans ?_ (realize_horizF (t₁ := (x 0).1) (t₂ := (x 1).1)).symm
        exact Iff.rfl
      | vert =>
        refine Iff.trans ?_ (realize_vertF (t₁ := (x 0).1) (t₂ := (x 1).1)).symm
        exact Iff.rfl
      | first =>
        refine Iff.trans ?_ (hF (fun p => (x p.1).2 p.2) (x 0).1 (x 1).1).symm
        exact Iff.rfl
      | base =>
        refine Iff.trans ?_ (realize_baseF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | tstart =>
        refine Iff.trans ?_ (realize_startF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | ledge =>
        refine Iff.trans ?_ (realize_edgeLF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl
      | redge =>
        refine Iff.trans ?_ (realize_edgeRF (t := (x 0).1) (i := 0)).symm
        exact Iff.rfl }

/-- The clocked machine's drawing, as an isomorphism. -/
noncomputable def tileEquiv :
    letI := tileStr A
    ((tileInterp.Map A) ≃[Language.wtile] (TilePt A)) :=
  tileEquivOf A TPFirst firstF fun _ _ _ => realize_firstF

/-- And the space-bounded machine's. -/
noncomputable def tileEquivR :
    letI := tileStrR A
    ((tileInterpR.Map A) ≃[Language.wtile] (TilePt A)) :=
  tileEquivOf A TPFirstR firstRF fun _ _ _ => realize_firstRF

/-- **The interpreted structure is a yes-instance exactly when the emitted one
is.** -/
theorem wideTiling_map_iff [Finite A] [Nonempty A] :
    letI := tileStr A
    (WideTiling (tileInterp.Map A) ↔ WideTiling (TilePt A)) :=
  letI := tileStr A
  WideTiling.iso_invariant (tileEquiv A)

end Emitted

end TilingHard

/-! ### The reduction and the completeness -/

section Reduction

open TilingHard

/-- **A wide machine on a clock is drawn as a tiling of the emitted square.**
The universe is three-dimensional – a tag with a symbol, a state and a
transition – and the machine's promises ride on the start tile, so a
no-instance's drawing has no corner and hence no tiling. -/
noncomputable def wideRegAccept_ordered_fo_reduction_wideTiling :
    WideRegAccept ≤ᶠᵒ[≤] WideTiling where
  Tag := TileTag
  dim := 3
  toInterpretation := tileInterp
  correct := fun A _ _ _ _ => by
    letI := tileStr A
    haveI : Finite (TilePt A) := inferInstance
    haveI : Nonempty (TilePt A) := ⟨(TileTag.dig, fun _ => Classical.arbitrary A)⟩
    refine Iff.trans ?_ (wideTiling_map_iff A).symm
    constructor
    · rintro ⟨hwf, hacc⟩
      exact tileable_of_accepts (wideRegData_wellFormed_iff.mp hwf) hacc
    · intro h
      obtain ⟨hwf, hacc⟩ := wideRegAccept_of_tileable h.1 h.2
      exact ⟨wideRegData_wellFormed_iff.mpr hwf, hacc⟩

/-- **Tiling a wide square is NEXPTIME-hard**: the wide machine on a clock is,
and it is drawn as one. -/
theorem wideTiling_NEXPTIME_hard : NEXPTIME.Hard WideTiling :=
  NEXPTIME.hard_of_orderedReduction wideRegAccept_ordered_fo_reduction_wideTiling
    wideRegAccept_NEXPTIME_hard

/-- **Tiling a wide square is NEXPTIME-complete.** The membership half is
`DescriptiveComplexity.wideTiling_mem_NEXPTIME`: a wide tiling is an ordinary
tiling of an exponential expansion, and `DescriptiveComplexity.TILING` is in
NP. -/
theorem wideTiling_NEXPTIME_complete : NEXPTIME.Complete WideTiling :=
  ⟨wideTiling_mem_NEXPTIME, wideTiling_NEXPTIME_hard⟩

end Reduction

end DescriptiveComplexity
