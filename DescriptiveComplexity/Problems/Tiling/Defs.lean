/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Complexity
import DescriptiveComplexity.Numbers.BinRel

/-!
# Tiling a square: the local problem behind the machines

The problem the exponential classes are usually read on ([Fürer
1983][furer1983domino]; [Börger, Grädel & Gurevich 1997][borger1997classical]
is the book-length account).

A **tile system** is a set of tiles with two compatibility relations – which
tile may stand immediately to the right of which, and which immediately above
which – a description of the bottom row, and a set of accepting tiles. The
question is whether the square whose sides are the *positions* of the instance
can be tiled: every cell carries a tile, neighbours are compatible, the bottom
row and the two edge columns are as described, and some cell carries an
accepting tile.

Nothing here is about resources. As with `DescriptiveComplexity.NTMAccept`, the
grid is indexed by the elements the instance marks as positions, so an instance
of size `n` asks about an `n × n` square and the problem sits in NP; read over
an exponential expansion, the same definition asks about a `2ⁿ × 2ⁿ` square and
sits one exponential up (`DescriptiveComplexity.Problems.Wide.Tiling`).

## Why the tiling and not the machine

A tile system has no head, no clock and no time: its conditions are *local* in
two dimensions and quantify over neighbours alone. That is what makes it the
cheap second complete problem of a class whose first one is a machine – the
work is a drawing, not an evaluator.

## The shape of the conditions

The two edge columns carry tiles marked `ledge` and `redge`, which is what the
border colors of a classical tiling problem do: a condition on neighbours says
nothing about the column at either end, where one neighbour is missing.

The bottom row is described by a relation `first p t` rather than listed,
exactly as a machine's initial tape is described by `inp p a`: a first-order
condition on the position, which is what an expansion can carry. The accepting
condition is a mark on tiles, and it is what turns a *tiling* into a *decision*:
without it every tile system with a compatible bottom row is a yes-instance.
-/

/- The vocabulary of tile systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.turing`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of tile-system instances. -/
inductive tilingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a column, and equally a row. -/
  | posn : tilingRel 1
  /-- `tile t`: `t` is a tile. -/
  | tile : tilingRel 1
  /-- `tacc t`: `t` is an accepting tile. -/
  | tacc : tilingRel 1
  /-- `tle p q`: the linear order along which the grid is read. -/
  | tle : tilingRel 2
  /-- `horiz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : tilingRel 2
  /-- `vert t t'`: `t'` may stand immediately above `t`. -/
  | vert : tilingRel 2
  /-- `first p t`: the cell of the bottom row in column `p` may carry `t`. -/
  | first : tilingRel 2
  /-- `base t`: `t` is a base tile – what the bottom row carries in a column the
  description says nothing about. -/
  | base : tilingRel 1
  /-- `tstart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : tilingRel 1
  /-- `ledge t`: `t` may stand in the leftmost column. -/
  | ledge : tilingRel 1
  /-- `redge t`: `t` may stand in the rightmost column. -/
  | redge : tilingRel 1
  deriving DecidableEq

/-- The relational vocabulary of tile-system instances: positions with their
order, tiles with their two compatibility relations, the bottom row and the
accepting tiles. -/
protected def tiling : Language :=
  ⟨fun _ => Empty, tilingRel⟩
  deriving IsRelational

/-- The position symbol. -/
abbrev tlPosn : Language.tiling.Relations 1 := .posn

/-- The tile symbol. -/
abbrev tlTile : Language.tiling.Relations 1 := .tile

/-- The accepting-tile symbol. -/
abbrev tlAcc : Language.tiling.Relations 1 := .tacc

/-- The order symbol. -/
abbrev tlLe : Language.tiling.Relations 2 := .tle

/-- The horizontal-compatibility symbol. -/
abbrev tlHoriz : Language.tiling.Relations 2 := .horiz

/-- The vertical-compatibility symbol. -/
abbrev tlVert : Language.tiling.Relations 2 := .vert

/-- The bottom-row symbol. -/
abbrev tlFirst : Language.tiling.Relations 2 := .first

/-- The base-tile symbol. -/
abbrev tlBase : Language.tiling.Relations 1 := .base

/-- The start-tile symbol. -/
abbrev tlStart : Language.tiling.Relations 1 := .tstart

/-- The left-edge symbol. -/
abbrev tlEdgeL : Language.tiling.Relations 1 := .ledge

/-- The right-edge symbol. -/
abbrev tlEdgeR : Language.tiling.Relations 1 := .redge

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The tile system an instance describes -/

/-- **A tile system**, read off an instance: the positions with their order,
the tiles with their compatibilities, the bottom row and the accepting tiles.
As with `DescriptiveComplexity.TMData`, the record is a plain bundle of
predicates, so everything about tilings is stated once and read at whatever
structure supplies them. -/
structure TileData (A : Type) where
  /-- Being a position – a column, and equally a row. -/
  Posn : A → Prop
  /-- The order on positions. -/
  Le : A → A → Prop
  /-- Being a tile. -/
  Tile : A → Prop
  /-- Being an accepting tile. -/
  Acc : A → Prop
  /-- The right neighbour may carry this tile. -/
  Horiz : A → A → Prop
  /-- The upper neighbour may carry this tile. -/
  Vert : A → A → Prop
  /-- The bottom row's cell in this column may carry this tile. -/
  First : A → A → Prop
  /-- Being a base tile: what a column the description says nothing about
  carries in the bottom row. -/
  Base : A → Prop
  /-- Being a start tile: what the corner of the grid carries. -/
  Start : A → Prop
  /-- Being a left-edge tile: what the leftmost column may carry. -/
  EdgeL : A → Prop
  /-- Being a right-edge tile: what the rightmost column may carry. -/
  EdgeR : A → Prop

namespace TileData

variable {A : Type} (T : TileData A)

/-- **The tiles the bottom row may carry in a column**: the ones the
description names there, and the base tiles in a column it names none. This is
`DescriptiveComplexity.TMData.InitTape`'s device – a description of the row
rather than a listing – and it is what lets an expansion carry it. -/
def FirstTile (x t : A) : Prop :=
  T.First x t ∨ ((∀ u, ¬T.First x u) ∧ T.Base t)

/-- **A tiling of the square**: every cell carries a tile, the bottom row is one
the description allows, the two edge columns carry tiles allowed there,
horizontal and vertical neighbours are compatible, and some cell carries an
accepting tile.

The two **edge conditions** are what the classical border colors of a tiling
problem do. A condition on neighbours says nothing about a column with no
neighbour on one side, so without them a tile whose meaning is “something is
arriving from the left” could stand in the leftmost column, justified by nothing;
a machine drawn as a tiling would then grow a head out of nowhere. -/
def IsTiling (τ : A → A → A) : Prop :=
  (∀ x y, T.Posn x → T.Posn y → T.Tile (τ x y)) ∧
    (∀ x y, T.Posn x → MinPos T.Le T.Posn y →
      ((MinPos T.Le T.Posn x → T.Start (τ x y)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ x y)))) ∧
    (∀ x y, T.Posn y → MinPos T.Le T.Posn x → T.EdgeL (τ x y)) ∧
    (∀ x y, T.Posn y → MaxPos T.Le T.Posn x → T.EdgeR (τ x y)) ∧
    (∀ x x' y, SuccPos T.Le T.Posn x x' → T.Posn y → T.Horiz (τ x y) (τ x' y)) ∧
    (∀ x y y', T.Posn x → SuccPos T.Le T.Posn y y' → T.Vert (τ x y) (τ x y')) ∧
    ∃ x y, T.Posn x ∧ T.Posn y ∧ T.Acc (τ x y)

/-- **The square is tileable**: some assignment of tiles to cells is a tiling.
The assignment is a function on the whole universe – what it does off the grid
is not read, so nothing is lost by not restricting it. -/
def Tileable : Prop := ∃ τ : A → A → A, T.IsTiling τ

/-- **Well-formedness**, folded into the yes-instances exactly as
`DescriptiveComplexity.TMData.WellFormed` is: the order is linear, and there is
a position to index the grid by. -/
def WellFormed : Prop := IsLinOrd T.Le ∧ ∃ p, T.Posn p

/-! ### Transport along a bijection -/

section Transport

variable {B : Type} (u : A ≃ B) (S : TileData B)
variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))

include hposn hle

/-- The least position of the image is the image of the least position. -/
theorem minPos_map (a : A) :
    MinPos T.Le T.Posn a ↔ MinPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle a b).mp (h b ((hposn b).mpr hq))
  · exact (hle a q).mpr (h (u q) ((hposn q).mp hq))

/-- The greatest position of the image is the image of the greatest one. -/
theorem maxPos_map (a : A) :
    MaxPos T.Le T.Posn a ↔ MaxPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle b a).mp (h b ((hposn b).mpr hq))
  · exact (hle q a).mpr (h (u q) ((hposn q).mp hq))

/-- And the successor of the image is the image of the successor. -/
theorem succPos_map (a a' : A) :
    SuccPos T.Le T.Posn a a' ↔ SuccPos S.Le S.Posn (u a) (u a') := by
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

/-- **And with it, tileability.** -/
theorem tileable_map (h : T.Tileable) : S.Tileable :=
  ⟨_, isTiling_map T u S hposn hle htile hacc hhoriz hvert hfirst hbase hstart
    hedgeL hedgeR h.choose_spec⟩

omit htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR in
/-- **And well-formedness**: the order is linear and there is a position. -/
theorem wellFormed_map (h : T.WellFormed) : S.WellFormed :=
  ⟨IsLinOrd.of_equiv u hle h.1, ⟨u h.2.choose, (hposn _).mp h.2.choose_spec⟩⟩

end Transport

end TileData

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Language.tiling.Structure A]

/-- Being a position. -/
def TLPosn (a : A) : Prop := RelMap tlPosn ![a]

/-- Being a tile. -/
def TLTile (a : A) : Prop := RelMap tlTile ![a]

/-- Being an accepting tile. -/
def TLAcc (a : A) : Prop := RelMap tlAcc ![a]

/-- The order on positions. -/
def TLLe (a b : A) : Prop := RelMap tlLe ![a, b]

/-- Horizontal compatibility. -/
def TLHoriz (a b : A) : Prop := RelMap tlHoriz ![a, b]

/-- Vertical compatibility. -/
def TLVert (a b : A) : Prop := RelMap tlVert ![a, b]

/-- The bottom row. -/
def TLFirst (a b : A) : Prop := RelMap tlFirst ![a, b]

/-- Being a base tile. -/
def TLBase (a : A) : Prop := RelMap tlBase ![a]

/-- Being a start tile. -/
def TLStart (a : A) : Prop := RelMap tlStart ![a]

/-- Being a left-edge tile. -/
def TLEdgeL (a : A) : Prop := RelMap tlEdgeL ![a]

/-- Being a right-edge tile. -/
def TLEdgeR (a : A) : Prop := RelMap tlEdgeR ![a]

/-- The tile system an instance describes. -/
def tileData (A : Type) [Language.tiling.Structure A] : TileData A where
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

variable {A B : Type} [Language.tiling.Structure A] [Language.tiling.Structure B]

section Transport

variable (e : A ≃[Language.tiling] B)

theorem tlPosn_map (a : A) : TLPosn a ↔ TLPosn (e a) := relMap_equiv₁ e tlPosn a

theorem tlTile_map (a : A) : TLTile a ↔ TLTile (e a) := relMap_equiv₁ e tlTile a

theorem tlAcc_map (a : A) : TLAcc a ↔ TLAcc (e a) := relMap_equiv₁ e tlAcc a

theorem tlLe_map (a a' : A) : TLLe a a' ↔ TLLe (e a) (e a') := relMap_equiv₂ e tlLe a a'

theorem tlHoriz_map (a a' : A) : TLHoriz a a' ↔ TLHoriz (e a) (e a') :=
  relMap_equiv₂ e tlHoriz a a'

theorem tlVert_map (a a' : A) : TLVert a a' ↔ TLVert (e a) (e a') :=
  relMap_equiv₂ e tlVert a a'

theorem tlFirst_map (a a' : A) : TLFirst a a' ↔ TLFirst (e a) (e a') :=
  relMap_equiv₂ e tlFirst a a'

theorem tlBase_map (a : A) : TLBase a ↔ TLBase (e a) := relMap_equiv₁ e tlBase a

theorem tlStart_map (a : A) : TLStart a ↔ TLStart (e a) := relMap_equiv₁ e tlStart a

theorem tlEdgeL_map (a : A) : TLEdgeL a ↔ TLEdgeL (e a) := relMap_equiv₁ e tlEdgeL a

theorem tlEdgeR_map (a : A) : TLEdgeR a ↔ TLEdgeR (e a) := relMap_equiv₁ e tlEdgeR a

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
theorem wellFormed_map (e : A ≃[Language.tiling] B) (h : (tileData A).WellFormed) :
    (tileData B).WellFormed :=
  TileData.wellFormed_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) h

end Transport

/-- **Tileability is an isomorphism invariant.** -/
theorem tileable_congr (e : A ≃[Language.tiling] B) :
    (tileData A).Tileable ↔ (tileData B).Tileable :=
  ⟨fun ⟨_, h⟩ => ⟨_, isTiling_map e h⟩, fun ⟨_, h⟩ => ⟨_, isTiling_map e.symm h⟩⟩

/-- **And so is well-formedness.** -/
theorem wellFormed_congr (e : A ≃[Language.tiling] B) :
    (tileData A).WellFormed ↔ (tileData B).WellFormed :=
  ⟨wellFormed_map e, wellFormed_map e.symm⟩

/-- **Tiling a square.** Can the square whose sides are the positions of the
instance be tiled, with the bottom row the description allows and an accepting
tile somewhere? The well-formedness promises of
`DescriptiveComplexity.TileData.WellFormed` are folded into the yes-instances,
exactly as for `DescriptiveComplexity.NTMAccept`. -/
def TILING : DecisionProblem Language.tiling where
  Holds := fun A _ => (tileData A).WellFormed ∧ (tileData A).Tileable
  iso_invariant := fun {_ _} _ _ e =>
    and_congr (wellFormed_congr e) (tileable_congr e)

end Problem

end DescriptiveComplexity
