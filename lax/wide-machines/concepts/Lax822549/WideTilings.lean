import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Lax822549.WideMachines
import Lax904597.Machines
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: Tilings one exponential up
type: definition
---
A tile system gives tiles, horizontal and vertical compatibilities, the
tiles allowed on the first row and its edges, and accepting tiles. Over an
instance of the wide tiling vocabulary, the system tiles the square whose
sides are the $2^n$ addresses of the instance; the square tiling problem
asks whether that square has a tiling, and the corridor tiling problem
whether the corridor of width $2^n$ and unbounded height has one, both on a
well-formed instance.
-/

namespace Lax822549.WideTilings

open Lax822549.WideMachines Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

open FirstOrder

open Language Structure

/-- **A tile system**, read off an instance: the positions with their order,
the tiles with their compatibilities, the bottom row and the accepting tiles.
As with `TMData`, the record is a plain bundle of
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
  /-- The right neighbor may carry this tile. -/
  Horiz : A → A → Prop
  /-- The upper neighbor may carry this tile. -/
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
`TMData.InitTape`'s device – a description of the row
rather than a listing – and it is what lets an expansion carry it. -/
def FirstTile (x t : A) : Prop :=
  T.First x t ∨ ((∀ u, ¬T.First x u) ∧ T.Base t)

/-- **A tiling of the square**: every cell carries a tile, the bottom row is one
the description allows, the two edge columns carry tiles allowed there,
horizontal and vertical neighbors are compatible, and some cell carries an
accepting tile.

The two **edge conditions** are what the classical border colors of a tiling
problem do. A condition on neighbors says nothing about a column with no
neighbor on one side, so without them a tile whose meaning is “something is
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
`TMData.WellFormed` is: the order is linear, and there is
a position to index the grid by. -/
def WellFormed : Prop := IsLinOrd T.Le ∧ ∃ p, T.Posn p

open FirstOrder

open Language Structure

variable {A : Type} (T : TileData A)

/-- **A tiling of the corridor up to a given height**: every cell of the strip
carries a tile, the bottom row is one the description allows, the two edge
columns carry tiles allowed there, neighbors in a row and rows one above the
other are compatible, and the top row carries an accepting tile.

The height is where a corridor differs from
`TileData.IsTiling`: nothing in the instance bounds it,
and the tiles above the accepting row are not asked about at all. -/
def IsCorridor (h : ℕ) (τ : ℕ → A → A) : Prop :=
  (∀ k x, k ≤ h → T.Posn x → T.Tile (τ k x)) ∧
    (∀ x, T.Posn x →
      ((MinPos T.Le T.Posn x → T.Start (τ 0 x)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ 0 x)))) ∧
    (∀ k x, k ≤ h → MinPos T.Le T.Posn x → T.EdgeL (τ k x)) ∧
    (∀ k x, k ≤ h → MaxPos T.Le T.Posn x → T.EdgeR (τ k x)) ∧
    (∀ k x x', k ≤ h → SuccPos T.Le T.Posn x x' → T.Horiz (τ k x) (τ k x')) ∧
    (∀ k x, k < h → T.Posn x → T.Vert (τ k x) (τ (k + 1) x)) ∧
    ∃ x, T.Posn x ∧ T.Acc (τ h x)

/-- **The corridor can be tiled**: some assignment of tiles to its cells is a
tiling of it, of some height. -/
def CorridorTileable : Prop := ∃ (h : ℕ) (τ : ℕ → A → A), T.IsCorridor h τ

end TileData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide tile-system instances: the tiles of
`FirstOrder.Language.tiling` with their compatibilities, and the positions and
their order replaced by an order on the elements – the digits of an address. -/
inductive wtileRel : ℕ → Type
  /-- `wtLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wtileRel 2
  /-- `wtDig x`: `x` is a digit – one of the elements the grid's coordinates are
  subsets of. -/
  | dig : wtileRel 1
  /-- `wtTile t`: `t` is a tile. -/
  | tile : wtileRel 1
  /-- `wtAcc t`: `t` is an accepting tile. -/
  | tacc : wtileRel 1
  /-- `wtHoriz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : wtileRel 2
  /-- `wtVert t t'`: `t'` may stand immediately above `t`. -/
  | vert : wtileRel 2
  /-- `wtFirst x t`: the bottom row's cell of `x` may carry `t`. -/
  | first : wtileRel 2
  /-- `wtBase t`: `t` is a base tile – what the bottom row carries where the
  description says nothing. -/
  | base : wtileRel 1
  /-- `wtStart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : wtileRel 1
  /-- `wtEdgeL t`: `t` may stand in the leftmost column. -/
  | ledge : wtileRel 1
  /-- `wtEdgeR t`: `t` may stand in the rightmost column. -/
  | redge : wtileRel 1
  deriving DecidableEq

/-- The relational vocabulary of wide tile-system instances. -/
def wtile : Language :=
  ⟨fun _ => Empty, wtileRel⟩

instance instIsRelationalWtile : wtile.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

/-- The order on the elements of the instance. -/
abbrev wtLe : wtile.Relations 2 := .wle

/-- The digit symbol. -/
abbrev wtDig : wtile.Relations 1 := .dig

/-- The tile symbol. -/
abbrev wtTile : wtile.Relations 1 := .tile

/-- The accepting-tile symbol. -/
abbrev wtAcc : wtile.Relations 1 := .tacc

/-- The horizontal-compatibility symbol. -/
abbrev wtHoriz : wtile.Relations 2 := .horiz

/-- The vertical-compatibility symbol. -/
abbrev wtVert : wtile.Relations 2 := .vert

/-- The bottom-row symbol. -/
abbrev wtFirst : wtile.Relations 2 := .first

/-- The base-tile symbol. -/
abbrev wtBase : wtile.Relations 1 := .base

/-- The start-tile symbol. -/
abbrev wtStart : wtile.Relations 1 := .tstart

/-- The left-edge symbol. -/
abbrev wtEdgeL : wtile.Relations 1 := .ledge

/-- The right-edge symbol. -/
abbrev wtEdgeR : wtile.Relations 1 := .redge

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wtile.Structure A]

/-- The order on the elements. -/
def WTLe (a b : A) : Prop := RelMap wtLe ![a, b]

/-- Being a digit: one of the elements the grid's coordinates are subsets of. -/
def WTDig (a : A) : Prop := RelMap wtDig ![a]

/-- Being a tile. -/
def WTTile (a : A) : Prop := RelMap wtTile ![a]

/-- Being an accepting tile. -/
def WTAcc (a : A) : Prop := RelMap wtAcc ![a]

/-- Horizontal compatibility. -/
def WTHoriz (a b : A) : Prop := RelMap wtHoriz ![a, b]

/-- Vertical compatibility. -/
def WTVert (a b : A) : Prop := RelMap wtVert ![a, b]

/-- The bottom row, at the cell of an element. -/
def WTFirst (a b : A) : Prop := RelMap wtFirst ![a, b]

/-- Being a base tile. -/
def WTBase (a : A) : Prop := RelMap wtBase ![a]

/-- Being a start tile. -/
def WTStart (a : A) : Prop := RelMap wtStart ![a]

/-- Being a left-edge tile: one the leftmost column may carry. -/
def WTEdgeL (a : A) : Prop := RelMap wtEdgeL ![a]

/-- Being a right-edge tile: one the rightmost column may carry. -/
def WTEdgeR (a : A) : Prop := RelMap wtEdgeR ![a]

/-- **An element the bottom row is described at**: one whose cell carries a
tile. These are the elements the file has cells for. -/
def WTHasFirst (a : A) : Prop := ∃ t : A, WTFirst a t

end Shorthands

section System

variable {A : Type} [wtile.Structure A]

/-- Being a position: an address is one exactly when it holds digits alone, so
the grid is indexed by the subsets of the *marked* part of the instance. That is
what leaves the instance room for its tiles: a tile is an element like any
other, and only the digits are coordinates. -/
def wtpPosn : WPoint A → Prop
  | Sum.inl s => ∀ x, s x → WTDig x
  | Sum.inr _ => False

/-- The order on the universe of the tiling: addresses first, in the
binary-number order they inherit from the instance's own order, then the tiles
in that same order. -/
def wtpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WTLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WTLe x y

/-- The bottom row: the cell of `x` – the segment `x` cuts among the elements
the description names – may carry the tiles of `x`, and every other address a
base tile. That is the same device as the register channel's input
(`wpInpReg`): a file of cells, not the ruler of all the
segments, because a clocked machine's tape is described the same way and that is
where this problem's hardness comes from. -/
def wtpFirst : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMFileSeg WTLe WTHasFirst s x ∧ WTFirst x y
  | _, _ => False

variable (A) in
/-- **The wide tile system an instance describes**: the tiles read off the
instance, the positions being the addresses. -/
def wideTileData : TileData (WPoint A) where
  Posn := wtpPosn
  Le := wtpLe
  Tile := wpMark WTTile
  Acc := wpMark WTAcc
  Horiz := wpAttr WTHoriz
  Vert := wpAttr WTVert
  First := wtpFirst
  Base := wpMark WTBase
  Start := wpMark WTStart
  EdgeL := wpMark WTEdgeL
  EdgeR := wpMark WTEdgeR

end System

open Lax904597.Problems Lax485149.Problems

/-- **Square tiling one exponential up.** -/
def WideTiling : DecisionProblem wtile :=
  DecisionProblem.ofPred fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).Tileable

/-- **Corridor tiling one exponential up.** -/
def WideCorridor : DecisionProblem wtile :=
  DecisionProblem.ofPred fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable

end Lax822549.WideTilings
