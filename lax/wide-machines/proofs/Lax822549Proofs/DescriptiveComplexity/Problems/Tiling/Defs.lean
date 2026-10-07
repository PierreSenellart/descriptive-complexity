/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Complexity
import Lax822549Proofs.DescriptiveComplexity.Numbers.BinRel
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

namespace Lax822549.WideTilings
end Lax822549.WideTilings

namespace Lax822549Proofs.DescriptiveComplexity.TileData
end Lax822549Proofs.DescriptiveComplexity.TileData

namespace Lax822549Proofs.Foreign.FirstOrder.Language
end Lax822549Proofs.Foreign.FirstOrder.Language

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideTilings (MaxPos TileData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Tiling a square: the local problem behind the machines

The problem the exponential classes are usually read on ([Fürer
1983][furer1983domino]; [Börger, Grädel & Gurevich 1997][borger1997classical]
is the book-length account).

A **tile system** is a set of tiles with two compatibility relations – which
tile may stand immediately to the right of which, and which immediately above
which – a description of the bottom row, and a set of accepting tiles. The
question is whether the square whose sides are the *positions* of the instance
can be tiled: every cell carries a tile, neighbors are compatible, the bottom
row and the two edge columns are as described, and some cell carries an
accepting tile.

Nothing here is about resources. As with `DescriptiveComplexity.NTMAccept`, the
grid is indexed by the elements the instance marks as positions, so an instance
of size `n` asks about an `n × n` square and the problem sits in NP; read over
an exponential expansion, the same definition asks about a `2ⁿ × 2ⁿ` square and
sits one exponential up (`DescriptiveComplexity.Problems.Wide.Tiling`).

## Why the tiling and not the machine

A tile system has no head, no clock and no time: its conditions are *local* in
two dimensions and quantify over neighbors alone. That is what makes it the
cheap second complete problem of a class whose first one is a machine – the
work is a drawing, not an evaluator.

## The shape of the conditions

The two edge columns carry tiles marked `ledge` and `redge`, which is what the
border colors of a classical tiling problem do: a condition on neighbors says
nothing about the column at either end, where one neighbor is missing.

The bottom row is described by a relation `first p t` rather than listed,
exactly as a machine's initial tape is described by `inp p a`: a first-order
condition on the position, which is what an expansion can carry. The accepting
condition is a mark on tiles, and it is what turns a *tiling* into a *decision*:
without it every tile system with a compatible bottom row is a yes-instance.
-/

namespace FirstOrder

namespace Language

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- Relation symbols of tile-system instances. -/
inductive _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a column, and equally a row. -/
  | posn : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `tile t`: `t` is a tile. -/
  | tile : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `tacc t`: `t` is an accepting tile. -/
  | tacc : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `tle p q`: the linear order along which the grid is read. -/
  | tle : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 2
  /-- `horiz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 2
  /-- `vert t t'`: `t'` may stand immediately above `t`. -/
  | vert : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 2
  /-- `first p t`: the cell of the bottom row in column `p` may carry `t`. -/
  | first : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 2
  /-- `base t`: `t` is a base tile – what the bottom row carries in a column the
  description says nothing about. -/
  | base : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `tstart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `ledge t`: `t` may stand in the leftmost column. -/
  | ledge : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1
  /-- `redge t`: `t` may stand in the rightmost column. -/
  | redge : Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel 1

end Language

end FirstOrder

namespace Lax822549Proofs.Derived

open FirstOrder FirstOrder.Language

deriving instance DecidableEq for Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel

end Lax822549Proofs.Derived

namespace FirstOrder

namespace Language

export Lax822549Proofs.Foreign.FirstOrder.Language (tilingRel)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The relational vocabulary of tile-system instances: positions with their
order, tiles with their two compatibility relations, the bottom row and the
accepting tiles. -/
protected def _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tiling : Language :=
  ⟨fun _ => Empty, Lax822549Proofs.Foreign.FirstOrder.Language.tilingRel⟩

end Language

end FirstOrder

namespace Lax822549Proofs.Derived

open FirstOrder FirstOrder.Language

deriving instance IsRelational for Lax822549Proofs.Foreign.FirstOrder.Language.tiling

end Lax822549Proofs.Derived

namespace FirstOrder

namespace Language

export Lax822549Proofs.Foreign.FirstOrder.Language (tiling)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The position symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlPosn : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .posn

export Lax822549Proofs.Foreign.FirstOrder.Language (tlPosn)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The tile symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlTile : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .tile

export Lax822549Proofs.Foreign.FirstOrder.Language (tlTile)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The accepting-tile symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlAcc : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .tacc

export Lax822549Proofs.Foreign.FirstOrder.Language (tlAcc)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The order symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlLe : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2 := .tle

export Lax822549Proofs.Foreign.FirstOrder.Language (tlLe)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The horizontal-compatibility symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlHoriz : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2 := .horiz

export Lax822549Proofs.Foreign.FirstOrder.Language (tlHoriz)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The vertical-compatibility symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlVert : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2 := .vert

export Lax822549Proofs.Foreign.FirstOrder.Language (tlVert)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The bottom-row symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlFirst : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 2 := .first

export Lax822549Proofs.Foreign.FirstOrder.Language (tlFirst)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The base-tile symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlBase : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .base

export Lax822549Proofs.Foreign.FirstOrder.Language (tlBase)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The start-tile symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlStart : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .tstart

export Lax822549Proofs.Foreign.FirstOrder.Language (tlStart)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The left-edge symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeL : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .ledge

export Lax822549Proofs.Foreign.FirstOrder.Language (tlEdgeL)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The right-edge symbol. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeR : Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Relations 1 := .redge

export Lax822549Proofs.Foreign.FirstOrder.Language (tlEdgeR)

end Language

end FirstOrder

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The tile system an instance describes -/

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

/-! ### Transport along a bijection -/

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

/-- The least position of the image is the image of the least position. -/
theorem minPos_map (a : A) :
    Lax904597.Machines.MinPos T.Le T.Posn a ↔ Lax904597.Machines.MinPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle a b).mp (h b ((hposn b).mpr hq))
  · exact (hle a q).mpr (h (u q) ((hposn q).mp hq))

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (minPos_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

/-- The greatest position of the image is the image of the greatest one. -/
theorem maxPos_map (a : A) :
    Lax822549.WideTilings.MaxPos T.Le T.Posn a ↔ Lax822549.WideTilings.MaxPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle b a).mp (h b ((hposn b).mpr hq))
  · exact (hle q a).mpr (h (u q) ((hposn q).mp hq))

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (maxPos_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

/-- And the successor of the image is the image of the successor. -/
theorem succPos_map (a a' : A) :
    Lax904597.Machines.SuccPos T.Le T.Posn a a' ↔ Lax904597.Machines.SuccPos S.Le S.Posn (u a) (u a') := by
  refine and_congr (hposn a) (and_congr (hposn a') (and_congr (hle a a')
    (and_congr ⟨fun h hc => h (u.injective hc), fun h hc => h (congrArg u hc)⟩ ?_)))
  refine ⟨fun h q hq h1 h2 => ?_, fun h q hq h1 h2 => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    rcases h b ((hposn b).mpr hq) ((hle a b).mpr h1) ((hle b a').mpr h2) with hc | hc
    · exact Or.inl (congrArg u hc)
    · exact Or.inr (congrArg u hc)
  · rcases h (u q) ((hposn q).mp hq) ((hle a q).mp h1) ((hle q a').mp h2) with hc | hc
    · exact Or.inl (u.injective hc)
    · exact Or.inr (u.injective hc)

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (succPos_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))

variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))

variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))

variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))

variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))

variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))

variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))

include htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR

/-- **A bijection matching the two systems carries a tiling across.** -/
theorem isTiling_map {τ : A → A → A} (h : T.IsTiling τ) :
    S.IsTiling fun x y => u (τ (u.symm x) (u.symm y)) := by
  obtain ⟨htiles, hfst, hel, her, hhor, hver, x, y, hx, hy, hax⟩ := h
  refine ⟨fun p q hp hq => ?_, fun p q hp hq => ?_, fun p q hq hp => ?_,
    fun p q hq hp => ?_, fun p p' q hp hq => ?_,
    fun p q q' hp hq => ?_, u x, u y, (hposn x).mp hx, (hposn y).mp hy, ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (htile _).mp (htiles a b ((hposn a).mpr hp) ((hposn b).mpr hq))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    obtain ⟨hst, hfr⟩ := hfst a b ((hposn a).mpr hp) ((minPos_map T u S hposn hle b).mpr hq)
    refine ⟨fun hmin => (hstart _).mp (hst ((minPos_map T u S hposn hle a).mpr hmin)), ?_⟩
    intro hmin
    rcases hfr (fun hc => hmin ((minPos_map T u S hposn hle a).mp hc)) with h | ⟨hno, hb⟩
    · exact Or.inl ((hfirst _ _).mp h)
    · refine Or.inr ⟨fun v hv => ?_, (hbase _).mp hb⟩
      obtain ⟨c, rfl⟩ : ∃ c, v = u c := ⟨u.symm v, (u.apply_symm_apply v).symm⟩
      exact hno c ((hfirst a c).mpr hv)
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hedgeL _).mp
      (hel a b ((hposn b).mpr hq) ((minPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hedgeR _).mp
      (her a b ((hposn b).mpr hq) ((maxPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨a', rfl⟩ : ∃ a', p' = u a' := ⟨u.symm p', (u.apply_symm_apply p').symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hhoriz _ _).mp
      (hhor a a' b ((succPos_map T u S hposn hle a a').mpr hp) ((hposn b).mpr hq))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    obtain ⟨b', rfl⟩ : ∃ b', q' = u b' := ⟨u.symm q', (u.apply_symm_apply q').symm⟩
    simp only [u.symm_apply_apply]
    exact (hvert _ _).mp
      (hver a b b' ((hposn a).mpr hp) ((succPos_map T u S hposn hle b b').mpr hq))
  · simp only [u.symm_apply_apply]
    exact (hacc _).mp hax

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (isTiling_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))

variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))

variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))

variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))

variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))

variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))

variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))

include htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR

/-- **And with it, tileability.** -/
theorem tileable_map (h : T.Tileable) : S.Tileable :=
  ⟨_, isTiling_map T u S hposn hle htile hacc hhoriz hvert hfirst hbase hstart
    hedgeL hedgeR h.choose_spec⟩

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (tileable_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))

variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))

variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))

variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))

variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))

variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))

variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))

include htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR

omit htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR in
/-- **And well-formedness**: the order is linear and there is a position. -/
theorem wellFormed_map (h : T.WellFormed) : S.WellFormed :=
  ⟨IsLinOrd.of_equiv u hle h.1, ⟨u h.2.choose, (hposn _).mp h.2.choose_spec⟩⟩

end Transport

end TileData

end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549.WideTilings.TileData

export Lax822549Proofs.DescriptiveComplexity.TileData (wellFormed_map)

end Lax822549.WideTilings.TileData

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TileData

variable {A : Type} (T : Lax822549.WideTilings.TileData A)

section Transport

variable {B : Type} (u : A ≃ B) (S : Lax822549.WideTilings.TileData B)

variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))

variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))

variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))

variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))

variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))

variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))

variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))

include htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR

end Transport

end TileData

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure A]

/-- Being a position. -/
def TLPosn (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlPosn ![a]

/-- Being a tile. -/
def TLTile (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlTile ![a]

/-- Being an accepting tile. -/
def TLAcc (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlAcc ![a]

/-- The order on positions. -/
def TLLe (a b : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlLe ![a, b]

/-- Horizontal compatibility. -/
def TLHoriz (a b : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlHoriz ![a, b]

/-- Vertical compatibility. -/
def TLVert (a b : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlVert ![a, b]

/-- The bottom row. -/
def TLFirst (a b : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlFirst ![a, b]

/-- Being a base tile. -/
def TLBase (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlBase ![a]

/-- Being a start tile. -/
def TLStart (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlStart ![a]

/-- Being a left-edge tile. -/
def TLEdgeL (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeL ![a]

/-- Being a right-edge tile. -/
def TLEdgeR (a : A) : Prop := RelMap Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeR ![a]

/-- The tile system an instance describes. -/
def tileData (A : Type) [Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure A] : Lax822549.WideTilings.TileData A where
  Posn := TLPosn
  Le := TLLe
  Tile := TLTile
  Acc := TLAcc
  Horiz := TLHoriz
  Vert := TLVert
  First := TLFirst
  Base := TLBase
  Start := TLStart
  EdgeL := TLEdgeL
  EdgeR := TLEdgeR

end Shorthands

/-! ### The problem -/

section Problem

variable {A B : Type} [Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure A] [Lax822549Proofs.Foreign.FirstOrder.Language.tiling.Structure B]

section Transport

variable (e : A ≃[Lax822549Proofs.Foreign.FirstOrder.Language.tiling] B)

theorem tlPosn_map (a : A) : TLPosn a ↔ TLPosn (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlPosn a

theorem tlTile_map (a : A) : TLTile a ↔ TLTile (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlTile a

theorem tlAcc_map (a : A) : TLAcc a ↔ TLAcc (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlAcc a

theorem tlLe_map (a a' : A) : TLLe a a' ↔ TLLe (e a) (e a') := relMap_equiv₂ e Lax822549Proofs.Foreign.FirstOrder.Language.tlLe a a'

theorem tlHoriz_map (a a' : A) : TLHoriz a a' ↔ TLHoriz (e a) (e a') :=
  relMap_equiv₂ e Lax822549Proofs.Foreign.FirstOrder.Language.tlHoriz a a'

theorem tlVert_map (a a' : A) : TLVert a a' ↔ TLVert (e a) (e a') :=
  relMap_equiv₂ e Lax822549Proofs.Foreign.FirstOrder.Language.tlVert a a'

theorem tlFirst_map (a a' : A) : TLFirst a a' ↔ TLFirst (e a) (e a') :=
  relMap_equiv₂ e Lax822549Proofs.Foreign.FirstOrder.Language.tlFirst a a'

theorem tlBase_map (a : A) : TLBase a ↔ TLBase (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlBase a

theorem tlStart_map (a : A) : TLStart a ↔ TLStart (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlStart a

theorem tlEdgeL_map (a : A) : TLEdgeL a ↔ TLEdgeL (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeL a

theorem tlEdgeR_map (a : A) : TLEdgeR a ↔ TLEdgeR (e a) := relMap_equiv₁ e Lax822549Proofs.Foreign.FirstOrder.Language.tlEdgeR a

/-- **An isomorphism carries a tiling across**: the tiling of the image is the
tiling of the source read through the isomorphism, and every condition is a
condition on relations the isomorphism preserves. -/
theorem isTiling_map {τ : A → A → A} (h : (tileData A).IsTiling τ) :
    (tileData B).IsTiling fun u v => e (τ (e.symm u) (e.symm v)) :=
  TileData.isTiling_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) (tlTile_map e)
    (tlAcc_map e) (tlHoriz_map e) (tlVert_map e) (tlFirst_map e) (tlBase_map e)
    (tlStart_map e) (tlEdgeL_map e) (tlEdgeR_map e) h

/-- **And it carries well-formedness across**: the order and the positions are
relations of the vocabulary. -/
theorem wellFormed_map (e : A ≃[Lax822549Proofs.Foreign.FirstOrder.Language.tiling] B) (h : (tileData A).WellFormed) :
    (tileData B).WellFormed :=
  TileData.wellFormed_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) h

end Transport

/-- **Tileability is an isomorphism invariant.** -/
theorem tileable_congr (e : A ≃[Lax822549Proofs.Foreign.FirstOrder.Language.tiling] B) :
    (tileData A).Tileable ↔ (tileData B).Tileable :=
  ⟨fun ⟨_, h⟩ => ⟨_, isTiling_map e h⟩, fun ⟨_, h⟩ => ⟨_, isTiling_map e.symm h⟩⟩

/-- **And so is well-formedness.** -/
theorem wellFormed_congr (e : A ≃[Lax822549Proofs.Foreign.FirstOrder.Language.tiling] B) :
    (tileData A).WellFormed ↔ (tileData B).WellFormed :=
  ⟨wellFormed_map e, wellFormed_map e.symm⟩

/-- **Tiling a square.** Can the square whose sides are the positions of the
instance be tiled, with the bottom row the description allows and an accepting
tile somewhere? The well-formedness promises of
`DescriptiveComplexity.TileData.WellFormed` are folded into the yes-instances,
exactly as for `DescriptiveComplexity.NTMAccept`. -/
def TILING : Lax904597.Problems.DecisionProblem Lax822549Proofs.Foreign.FirstOrder.Language.tiling where
  Holds := fun A _ => (tileData A).WellFormed ∧ (tileData A).Tileable
  iso_invariant := fun {_ _} _ _ e =>
    and_congr (wellFormed_congr e) (tileable_congr e)

end Problem

end Lax822549Proofs.DescriptiveComplexity


