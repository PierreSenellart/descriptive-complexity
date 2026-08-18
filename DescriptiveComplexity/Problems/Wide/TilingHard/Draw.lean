/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Atoms

/-!
# The drawing, as formulas

The tile system of `DescriptiveComplexity.Problems.Wide.TilingHard.Tiles`
written down: one formula per symbol of `FirstOrder.Language.wtile` and per
tuple of tags, over the machine's own vocabulary with the order of the instance.

The dimension is three – a tile is a tag with a symbol, a state and a
transition – and every case analysis on tags is a
`DescriptiveComplexity.TilingHard.tagIfF`, so each formula is a fixed
conjunction and the tags decide which of its parts are `⊤`. The order is the
only symbol needing the ambient order of the instance, through
`DescriptiveComplexity.lexLeF`: the points that are not digits are compared
lexicographically, and the digits by the machine's own order.

Each formula is checked against the predicate it draws, at an arbitrary
valuation, so `DescriptiveComplexity.TilingHard.tileInterp` is the emitted
structure of `DescriptiveComplexity.TilingHard.tileStr` symbol by symbol.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-! ### The coordinates of an argument -/

section Coords

variable {n : ℕ}

/-- The symbol coordinate of the `i`-th argument. -/
def argSym (i : Fin n) : Fin n × Fin 3 := (i, 0)

/-- Its state coordinate. -/
def argState (i : Fin n) : Fin n × Fin 3 := (i, 1)

/-- Its transition coordinate. -/
def argTr (i : Fin n) : Fin n × Fin 3 := (i, 2)

variable {A : Type}

/-- **The tile an argument is**, at a valuation and a tag. -/
def argPt (v : Fin n × Fin 3 → A) (t : TileTag) (i : Fin n) : TilePt A :=
  (t, fun j => v (i, j))

@[simp]
theorem argPt_fst (v : Fin n × Fin 3 → A) (t : TileTag) (i : Fin n) :
    (argPt v t i).1 = t := rfl

@[simp]
theorem tpSym_argPt (v : Fin n × Fin 3 → A) (t : TileTag) (i : Fin n) :
    tpSym (argPt v t i) = v (argSym i) := rfl

@[simp]
theorem tpState_argPt (v : Fin n × Fin 3 → A) (t : TileTag) (i : Fin n) :
    tpState (argPt v t i) = v (argState i) := rfl

@[simp]
theorem tpTr_argPt (v : Fin n × Fin 3 → A) (t : TileTag) (i : Fin n) :
    tpTr (argPt v t i) = v (argTr i) := rfl

end Coords

/-! ### The marks of one tile -/

section Unary

variable {n : ℕ}

/-- `x` is a digit: its tag says so and its triple is diagonal. -/
noncomputable def digF (t : TileTag) (i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  tagIfF (t = TileTag.dig) ⊓ (wdEqF (argSym i) (argState i) ⊓ wdEqF (argState i) (argTr i))

/-- `x` holds no head. -/
noncomputable def noHeadF (t : TileTag) (_i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  tagIfF (t = TileTag.sym ∨ t = TileTag.arrL ∨ t = TileTag.arrR)

/-- `x` is a tile: a head carries a transition the machine may fire, a digit is
no tile, and every other kind asks nothing. -/
noncomputable def tileF (t : TileTag) (i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  match t with
  | TileTag.dig => ⊥
  | TileTag.head =>
    wdTrF (argTr i) ⊓ (wdSrcF (argTr i) (argState i) ⊓ wdReadF (argTr i) (argSym i))
  | _ => ⊤

/-- `x` is an accepting tile: the head is here, in an accepting state. -/
noncomputable def accF (t : TileTag) (i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  tagIfF (t = TileTag.head ∨ t = TileTag.halt) ⊓ wdAccF (argState i)

/-- `x` is a base tile: no head, holding the blank. -/
noncomputable def baseF (t : TileTag) (i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  noHeadF t i ⊓ wdBlankF (argSym i)

/-- `x` is a start tile: the head on the blank in a start state, and the
machine's promises. -/
noncomputable def startF (t : TileTag) (i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  wideWFF ⊓
    (((tagIfF (t = TileTag.head) ⊓
          (wdTrF (argTr i) ⊓ (wdSrcF (argTr i) (argState i) ⊓ wdReadF (argTr i) (argSym i)))) ⊔
        tagIfF (t = TileTag.halt)) ⊓
      (wdStartF (argState i) ⊓ wdBlankF (argSym i)))

/-- `x` may stand in the leftmost column. -/
noncomputable def edgeLF (t : TileTag) (_i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  tagIfF (t ≠ TileTag.arrL)

/-- `x` may stand in the rightmost column. -/
noncomputable def edgeRF (t : TileTag) (_i : Fin n) : wideOrd.Formula (Fin n × Fin 3) :=
  tagIfF (t ≠ TileTag.arrR)

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]
variable {v : Fin n × Fin 3 → A} {t : TileTag} {i : Fin n}

@[simp]
theorem realize_digF : (digF t i).Realize v ↔ TPDig (argPt v t i) := by
  simp only [digF, Formula.realize_inf, realize_tagIfF, realize_wdEqF, TPDig]
  rfl

@[simp]
theorem realize_noHeadF : (noHeadF t i).Realize v ↔ TPNoHead (argPt v t i) := by
  simp only [noHeadF, realize_tagIfF, TPNoHead]
  rfl

@[simp]
theorem realize_tileF : (tileF t i).Realize v ↔ TPTile (argPt v t i) := by
  cases t <;>
    simp only [tileF, TPTile, argPt_fst, Formula.realize_bot, Formula.realize_top,
      Formula.realize_inf, realize_wdTrF, realize_wdSrcF, realize_wdReadF,
      tpSym_argPt, tpState_argPt, tpTr_argPt]

@[simp]
theorem realize_accF : (accF t i).Realize v ↔ TPAcc (argPt v t i) := by
  simp only [accF, Formula.realize_inf, realize_tagIfF, realize_wdAccF, TPAcc,
    argPt_fst, tpState_argPt]

@[simp]
theorem realize_baseF : (baseF t i).Realize v ↔ TPBase (argPt v t i) := by
  simp only [baseF, Formula.realize_inf, realize_noHeadF, realize_wdBlankF, TPBase,
    tpSym_argPt]

@[simp]
theorem realize_startF : (startF t i).Realize v ↔ TPStart (argPt v t i) := by
  simp only [startF, Formula.realize_inf, Formula.realize_sup, realize_wideWFF,
    realize_tagIfF, realize_wdTrF, realize_wdSrcF, realize_wdReadF, realize_wdStartF,
    realize_wdBlankF, TPStart, argPt_fst, tpSym_argPt, tpState_argPt, tpTr_argPt]

@[simp]
theorem realize_edgeLF : (edgeLF t i).Realize v ↔ TPEdgeL (argPt v t i) := by
  simp only [edgeLF, realize_tagIfF, TPEdgeL, argPt_fst]

@[simp]
theorem realize_edgeRF : (edgeRF t i).Realize v ↔ TPEdgeR (argPt v t i) := by
  simp only [edgeRF, realize_tagIfF, TPEdgeR, argPt_fst]

end Unary

/-! ### The relations between two tiles -/

section Binary

/-- The order the drawing emits: the digits last, in the machine's own order,
and everything else lexicographically. -/
noncomputable def leF (t₁ t₂ : TileTag) : wideOrd.Formula (Fin 2 × Fin 3) :=
  (digF t₁ 0 ⊓ (digF t₂ 1 ⊓ wdLeF (argSym 0) (argSym 1))) ⊔
    ((∼(digF t₁ 0) ⊓ digF t₂ 1) ⊔
      (∼(digF t₁ 0) ⊓ (∼(digF t₂ 1) ⊓ lexLeF Language.wide 3 t₁ t₂)))

/-- The bottom row: the cell of a digit may carry a tile holding that element's
input symbol, and no head. -/
noncomputable def firstF (t₁ t₂ : TileTag) : wideOrd.Formula (Fin 2 × Fin 3) :=
  digF t₁ 0 ⊓ (noHeadF t₂ 1 ⊓ wdInpF (argSym 0) (argSym 1))

/-- The bottom row at the ruler: the cell of a digit carries that element's
input symbol, or the blank where it has none. -/
noncomputable def firstRF (t₁ t₂ : TileTag) : wideOrd.Formula (Fin 2 × Fin 3) :=
  digF t₁ 0 ⊓ (noHeadF t₂ 1 ⊓
    (wdInpF (argSym 0) (argSym 1) ⊔
      (Formula.iAlls (Fin 1) (∼(wdInpF (Sum.inl (argSym 0)) (Sum.inr 0))) ⊓
        wdBlankF (argSym 1))))

/-- What may stand immediately to the right of a tile: an announced head is the
neighbor's arrival and an arrival is a neighboring head, so a row keeps to one
head. -/
noncomputable def horizF (t₁ t₂ : TileTag) : wideOrd.Formula (Fin 2 × Fin 3) :=
  tileF t₁ 0 ⊓ (tileF t₂ 1 ⊓
    ((tagIfF (t₁ = TileTag.head) ⟹
        (wdRightF (argTr 0) ⟹
          (tagIfF (t₂ = TileTag.arrL) ⊓ wdDstF (argTr 0) (argState 1)))) ⊓
      ((tagIfF (t₂ = TileTag.head) ⟹
          (∼(wdRightF (argTr 1)) ⟹
            (tagIfF (t₁ = TileTag.arrR) ⊓ wdDstF (argTr 1) (argState 0)))) ⊓
        ((tagIfF (t₂ = TileTag.arrL) ⟹
            (tagIfF (t₁ = TileTag.head) ⊓
              (wdRightF (argTr 0) ⊓ wdDstF (argTr 0) (argState 1)))) ⊓
          ((tagIfF (t₁ = TileTag.arrR) ⟹
              (tagIfF (t₂ = TileTag.head) ⊓
                (∼(wdRightF (argTr 1)) ⊓ wdDstF (argTr 1) (argState 0)))) ⊓
            ∼(tagIfF ((t₁ = TileTag.head ∨ t₁ = TileTag.halt) ∧
              (t₂ = TileTag.head ∨ t₂ = TileTag.halt))))))))

/-- What may stand immediately above a tile: the head writes, an arrival becomes
the head, and every other cell copies itself. -/
noncomputable def vertF (t₁ t₂ : TileTag) : wideOrd.Formula (Fin 2 × Fin 3) :=
  match t₁ with
  | TileTag.dig => ⊥
  | TileTag.sym => noHeadF t₂ 1 ⊓ wdEqF (argSym 1) (argSym 0)
  | TileTag.head => noHeadF t₂ 1 ⊓ wdWriteF (argTr 0) (argSym 1)
  | TileTag.halt =>
    tagIfF (t₂ = TileTag.halt) ⊓
      (wdEqF (argSym 1) (argSym 0) ⊓ wdEqF (argState 1) (argState 0))
  | TileTag.arrL | TileTag.arrR =>
    tagIfF (t₂ = TileTag.head ∨ t₂ = TileTag.halt) ⊓
      (wdEqF (argSym 1) (argSym 0) ⊓ wdEqF (argState 1) (argState 0))

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]
variable {v : Fin 2 × Fin 3 → A} {t₁ t₂ : TileTag}

@[simp]
theorem realize_leF : (leF t₁ t₂).Realize v ↔ tpLe (argPt v t₁ 0) (argPt v t₂ 1) := by
  simp only [leF, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_digF, realize_wdLeF, realize_lexLeF, tpLe]
  rfl

@[simp]
theorem realize_firstF :
    (firstF t₁ t₂).Realize v ↔ TPFirst (argPt v t₁ 0) (argPt v t₂ 1) := by
  simp only [firstF, Formula.realize_inf, realize_digF, realize_noHeadF, realize_wdInpF,
    TPFirst, tpSym_argPt]
  constructor
  · rintro ⟨hd, hnh, hinp⟩
    exact ⟨v (argSym 1), hd, hnh, hinp, rfl⟩
  · rintro ⟨a, hd, hnh, hinp, hsym⟩
    exact ⟨hd, hnh, hsym ▸ hinp⟩

@[simp]
theorem realize_firstRF :
    (firstRF t₁ t₂).Realize v ↔ TPFirstR (argPt v t₁ 0) (argPt v t₂ 1) := by
  simp only [firstRF, Formula.realize_inf, Formula.realize_sup, Formula.realize_iAlls,
    Formula.realize_not, realize_digF, realize_noHeadF, realize_wdInpF, realize_wdBlankF,
    TPFirstR, tpSym_argPt, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl (and_congr Iff.rfl (or_congr Iff.rfl
    (and_congr ⟨fun h a => h (fun _ => a), fun h w => h (w 0)⟩ Iff.rfl)))

@[simp]
theorem realize_horizF :
    (horizF t₁ t₂).Realize v ↔ TPHoriz (argPt v t₁ 0) (argPt v t₂ 1) := by
  simp only [horizF, Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    realize_tileF, realize_tagIfF, realize_wdRightF, realize_wdDstF, TPHoriz,
    argPt_fst, tpState_argPt, tpTr_argPt]

@[simp]
theorem realize_vertF : (vertF t₁ t₂).Realize v ↔ TPVert (argPt v t₁ 0) (argPt v t₂ 1) := by
  cases t₁ <;>
    simp only [vertF, TPVert, argPt_fst, Formula.realize_bot, Formula.realize_inf,
      realize_noHeadF, realize_tagIfF, realize_wdEqF, realize_wdWriteF,
      tpSym_argPt, tpState_argPt, tpTr_argPt]

end Binary

end TilingHard

end DescriptiveComplexity
