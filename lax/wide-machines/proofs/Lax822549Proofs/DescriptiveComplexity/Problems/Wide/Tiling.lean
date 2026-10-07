/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Tiling.Defs
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.WellFormed
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace FirstOrder.Language
export Lax822549.WideTilings (wtAcc wtBase wtDig wtEdgeL wtEdgeR wtFirst wtHoriz wtLe wtStart wtTile wtVert wtile wtileRel)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMFileSeg WMSetLe WPoint wpAttr wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (TileData WTAcc WTBase WTDig WTEdgeL WTEdgeR WTFirst WTHasFirst WTHoriz WTLe WTStart WTTile WTVert wideTileData wtpFirst wtpLe wtpPosn)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The wide tiling: a square addressed by the subsets of its instance

The tile system of `DescriptiveComplexity.TILING` with one exponent added *in
the semantics of the problem*, exactly as `DescriptiveComplexity.WideAccept`
adds one to a machine:

> the grid is indexed by the **subsets** of the instance, while the tiles –
> with their compatibilities, the bottom row and the accepting mark – stay an
> ordinary part of the instance.

So an instance of size `n` asks whether a `2ⁿ × 2ⁿ` square can be tiled, which
is the classical second complete problem of NEXPTIME beside a machine. Nothing
is said about resources: the universe of the tiling *is* the universe of an
exponential expansion of the instance
(`DescriptiveComplexity.Problems.Wide.TilingExp`), so membership is the
composition `TILING ∘ expansion`.

## Where the order comes from

As for the wide machine, a decision problem may not read the ambient order of
its instance, so the instance carries its own order `wtLe` and the order on
addresses is the binary-number order it induces
(`DescriptiveComplexity.WMSetLe`). Linearity is a promise, folded into the
yes-instances through `DescriptiveComplexity.TileData.WellFormed`.

## Where the bottom row goes

The bottom row is described at the **initial-segment addresses**: the address
`{y | y ≤ x}` may carry the tiles `wtFirst x` names, and every other address may
carry those `wtFirst` names of no element at all – the same device as the wide
machine's input (`wmInp`), and for the same reason: a first-order condition on
the *element* is what an expansion can carry, while a listing of `2ⁿ` cells is
not.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax822549.WideTilings.wtile.Structure A]

end Shorthands

/-! ### The universe and the tile system -/

section System

variable {A : Type} [Lax822549.WideTilings.wtile.Structure A]

/-- **The order of a wide tiling is linear** as soon as the instance's is: the
addresses are ordered as binary numbers, the tiles as in the instance, and the
addresses come first. -/
theorem isLinOrd_wtpLe [Finite A] (h : Lax904597.Machines.IsLinOrd (Lax822549.WideTilings.WTLe (A := A))) :
    Lax904597.Machines.IsLinOrd (Lax822549.WideTilings.wtpLe (A := A)) := by
  have hs := isLinOrd_wmSetLe h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (s | x)
    · exact hs.1 s
    · exact h.1 x
  · rintro (s | x) (t | y) (u | z) h1 h2 <;>
      first
        | exact trivial
        | exact False.elim h1
        | exact False.elim h2
        | exact hs.2.1 _ _ _ h1 h2
        | exact h.2.1 _ _ _ h1 h2
  · rintro (s | x) (t | y) h1 h2 <;>
      first
        | exact False.elim h1
        | exact False.elim h2
        | exact congrArg Sum.inl (hs.2.2.1 _ _ h1 h2)
        | exact congrArg Sum.inr (h.2.2.1 _ _ h1 h2)
  · rintro (s | x) (t | y)
    · exact hs.2.2.2 s t
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact h.2.2.2 x y

/-- **The promise of a wide tiling is a promise about its instance**: the grid
adds nothing to it, the empty address being a position whatever the instance
says. -/
theorem wideTileData_wellFormed [Finite A] (h : Lax904597.Machines.IsLinOrd (Lax822549.WideTilings.WTLe (A := A))) :
    (Lax822549.WideTilings.wideTileData A).WellFormed :=
  ⟨isLinOrd_wtpLe h, ⟨Sum.inl fun _ => False, fun _ hc => hc.elim⟩⟩

end System

/-! ### Isomorphism-invariance -/

section Transport

variable {A B : Type} [Lax822549.WideTilings.wtile.Structure A] [Lax822549.WideTilings.wtile.Structure B]

/-- **An isomorphism of instances is a bijection of the tilings' universes**:
an address goes to its image, a tile to its image. -/
def wtPointEquiv (e : A ≃[Lax822549.WideTilings.wtile] B) : Lax822549.WideMachines.WPoint A ≃ Lax822549.WideMachines.WPoint B where
  toFun := Sum.map (fun s y => s (e.symm y)) e
  invFun := Sum.map (fun t x => t (e x)) e.symm
  left_inv := by
    rintro (s | x)
    · exact congrArg Sum.inl (funext fun z => by simp only [e.symm_apply_apply])
    · exact congrArg Sum.inr (e.symm_apply_apply x)
  right_inv := by
    rintro (t | y)
    · exact congrArg Sum.inl (funext fun z => by simp only [e.apply_symm_apply])
    · exact congrArg Sum.inr (e.apply_symm_apply y)

variable (e : A ≃[Lax822549.WideTilings.wtile] B)

theorem wtLe_map (a a' : A) : Lax822549.WideTilings.WTLe a a' ↔ Lax822549.WideTilings.WTLe (e a) (e a') := relMap_equiv₂ e Lax822549.WideTilings.wtLe a a'

theorem wtTile_map (a : A) : Lax822549.WideTilings.WTTile a ↔ Lax822549.WideTilings.WTTile (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtTile a

theorem wtAcc_map (a : A) : Lax822549.WideTilings.WTAcc a ↔ Lax822549.WideTilings.WTAcc (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtAcc a

theorem wtHoriz_map (a a' : A) : Lax822549.WideTilings.WTHoriz a a' ↔ Lax822549.WideTilings.WTHoriz (e a) (e a') :=
  relMap_equiv₂ e Lax822549.WideTilings.wtHoriz a a'

theorem wtVert_map (a a' : A) : Lax822549.WideTilings.WTVert a a' ↔ Lax822549.WideTilings.WTVert (e a) (e a') :=
  relMap_equiv₂ e Lax822549.WideTilings.wtVert a a'

theorem wtFirst_map (a a' : A) : Lax822549.WideTilings.WTFirst a a' ↔ Lax822549.WideTilings.WTFirst (e a) (e a') :=
  relMap_equiv₂ e Lax822549.WideTilings.wtFirst a a'

theorem wtBase_map (a : A) : Lax822549.WideTilings.WTBase a ↔ Lax822549.WideTilings.WTBase (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtBase a

theorem wtDig_map (a : A) : Lax822549.WideTilings.WTDig a ↔ Lax822549.WideTilings.WTDig (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtDig a

theorem wtStart_map (a : A) : Lax822549.WideTilings.WTStart a ↔ Lax822549.WideTilings.WTStart (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtStart a

theorem wtEdgeL_map (a : A) : Lax822549.WideTilings.WTEdgeL a ↔ Lax822549.WideTilings.WTEdgeL (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtEdgeL a

theorem wtEdgeR_map (a : A) : Lax822549.WideTilings.WTEdgeR a ↔ Lax822549.WideTilings.WTEdgeR (e a) := relMap_equiv₁ e Lax822549.WideTilings.wtEdgeR a

/-- The elements the bottom row is described at correspond. -/
theorem wtHasFirst_map (a : A) : Lax822549.WideTilings.WTHasFirst a ↔ Lax822549.WideTilings.WTHasFirst (e a) := by
  refine ⟨fun ⟨t, ht⟩ => ⟨e t, (wtFirst_map e a t).mp ht⟩, fun ⟨t, ht⟩ => ⟨e.symm t, ?_⟩⟩
  refine (wtFirst_map e a (e.symm t)).mpr ?_
  rwa [e.apply_symm_apply]

/-- And so do the cells of the file. -/
theorem wtFileSeg_map (s : A → Prop) (x : A) :
    Lax822549.WideMachines.WMFileSeg Lax822549.WideTilings.WTLe Lax822549.WideTilings.WTHasFirst s x ↔
      Lax822549.WideMachines.WMFileSeg Lax822549.WideTilings.WTLe Lax822549.WideTilings.WTHasFirst (fun y => s (e.symm y)) (e x) := by
  refine ⟨fun h y => (h (e.symm y)).trans ?_, fun h y => ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have h1' := (wtLe_map e (e.symm y) x).mp h1
      have h2' := (wtHasFirst_map e (e.symm y)).mp h2
      rw [e.apply_symm_apply] at h1' h2'
      exact ⟨h1', h2'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(wtLe_map e (e.symm y) x).mpr ?_, (wtHasFirst_map e (e.symm y)).mpr ?_⟩
      · rwa [e.apply_symm_apply]
      · rwa [e.apply_symm_apply]
  · have h1 := h (e y)
    simp only [e.symm_apply_apply] at h1
    exact h1.trans ⟨fun ⟨ha, hb⟩ => ⟨(wtLe_map e y x).mpr ha, (wtHasFirst_map e y).mpr hb⟩,
      fun ⟨ha, hb⟩ => ⟨(wtLe_map e y x).mp ha, (wtHasFirst_map e y).mp hb⟩⟩

/-- The positions correspond: an address of digits is a position, a tile is
not. -/
theorem wtPosn_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Posn p ↔ (Lax822549.WideTilings.wideTileData B).Posn (wtPointEquiv e p) := by
  rcases p with s | x
  · refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · have hd := (wtDig_map e (e.symm y)).mp (h (e.symm y) hy)
      rwa [e.apply_symm_apply] at hd
    · refine (wtDig_map e y).mpr (h (e y) ?_)
      simpa only [e.symm_apply_apply] using hy
  · exact Iff.rfl

/-- The orders correspond: the binary-number order on addresses is the
instance's order read through the isomorphism. -/
theorem wtLe_point_map (p q : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Le p q ↔ (Lax822549.WideTilings.wideTileData B).Le (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact wmSetLe_congr e.toEquiv (fun a a' => wtLe_map e a a') s t
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtLe_map e x y

/-- The tiles correspond. -/
theorem wtTile_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Tile p ↔ (Lax822549.WideTilings.wideTileData B).Tile (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtTile_map e x

/-- The accepting tiles correspond. -/
theorem wtAcc_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Acc p ↔ (Lax822549.WideTilings.wideTileData B).Acc (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtAcc_map e x

/-- Horizontal compatibility corresponds. -/
theorem wtHoriz_point_map (p q : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Horiz p q ↔
      (Lax822549.WideTilings.wideTileData B).Horiz (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtHoriz_map e x y

/-- Vertical compatibility corresponds. -/
theorem wtVert_point_map (p q : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Vert p q ↔
      (Lax822549.WideTilings.wideTileData B).Vert (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtVert_map e x y

/-- The bottom row corresponds: the cell of an element goes to the cell of its
image. -/
theorem wtFirst_point_map (p q : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).First p q ↔
      (Lax822549.WideTilings.wideTileData B).First (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · refine ⟨fun ⟨z, hseg, hf⟩ => ⟨e z, (wtFileSeg_map e s z).mp hseg,
      (wtFirst_map e z y).mp hf⟩, fun ⟨z, hseg, hf⟩ => ⟨e.symm z, ?_, ?_⟩⟩
    · refine (wtFileSeg_map e s (e.symm z)).mpr ?_
      rwa [e.apply_symm_apply]
    · refine (wtFirst_map e (e.symm z) y).mpr ?_
      rwa [e.apply_symm_apply]
  · exact Iff.rfl
  · exact Iff.rfl

/-- The base tiles correspond. -/
theorem wtBase_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Base p ↔ (Lax822549.WideTilings.wideTileData B).Base (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtBase_map e x

/-- The start tiles correspond. -/
theorem wtStart_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).Start p ↔ (Lax822549.WideTilings.wideTileData B).Start (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtStart_map e x

/-- The left-edge tiles correspond. -/
theorem wtEdgeL_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).EdgeL p ↔ (Lax822549.WideTilings.wideTileData B).EdgeL (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtEdgeL_map e x

/-- And so do the right-edge tiles. -/
theorem wtEdgeR_point_map (p : Lax822549.WideMachines.WPoint A) :
    (Lax822549.WideTilings.wideTileData A).EdgeR p ↔ (Lax822549.WideTilings.wideTileData B).EdgeR (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtEdgeR_map e x

end Transport

/-! ### The problem -/

section Problem

/-- **The two halves transport**, in either direction: the wide tile system of
the image is the source's read through the isomorphism. -/
theorem wideTile_map {A B : Type} [Lax822549.WideTilings.wtile.Structure A] [Lax822549.WideTilings.wtile.Structure B]
    (e : A ≃[Lax822549.WideTilings.wtile] B)
    (h : (Lax822549.WideTilings.wideTileData A).WellFormed ∧ (Lax822549.WideTilings.wideTileData A).Tileable) :
    (Lax822549.WideTilings.wideTileData B).WellFormed ∧ (Lax822549.WideTilings.wideTileData B).Tileable :=
  ⟨TileData.wellFormed_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e) h.1,
    TileData.tileable_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e)
      (wtTile_point_map e) (wtAcc_point_map e) (wtHoriz_point_map e)
      (wtVert_point_map e) (wtFirst_point_map e) (wtBase_point_map e)
      (wtStart_point_map e) (wtEdgeL_point_map e) (wtEdgeR_point_map e) h.2⟩

/-- **Tiling a wide square.** Can the square whose sides are the *subsets* of
the instance be tiled, with the bottom row the description allows and an
accepting tile somewhere? The well-formedness promises are folded into the
yes-instances, exactly as for `DescriptiveComplexity.WideAccept`. -/
def WideTiling : Lax904597.Problems.DecisionProblem Lax822549.WideTilings.wtile where
  Holds := fun A _ => (Lax822549.WideTilings.wideTileData A).WellFormed ∧ (Lax822549.WideTilings.wideTileData A).Tileable
  iso_invariant := fun {_ _} _ _ e => ⟨wideTile_map e, wideTile_map e.symm⟩

end Problem

end Lax822549Proofs.DescriptiveComplexity


