/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Tiling.Defs
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Hierarchy

/-!
# Tiling a square is existential second-order definable

The membership half of the problem's completeness: a tiling *is* a certificate,
and checking it is local. The `Σ₁` definition guesses one **ternary** relation
variable `R x y t`, read as “the cell in column `x` and row `y` carries the tile
`t`”, and its first-order kernel says what a tiling is:

* every cell of the grid carries exactly one tile, and that tile is one of the
  instance's;
* the bottom row is one the description allows, and the two edge columns carry
  tiles allowed there;
* horizontal and vertical neighbors are compatible;
* some cell carries an accepting tile;

together with the well-formedness the yes-instances fold in – the order is
linear and there is a position.

The guess has to be **functional** where a coloring's need not be
(`DescriptiveComplexity.paletteKernel`): the accepting condition asks for a cell
that *carries* an accepting tile, so a cell holding two tiles could satisfy the
compatibility clauses by one and the acceptance by the other, which no tiling
does.

The grid is indexed by the positions of the instance, so this is an `n × n`
tiling and the definition is a `Σ₁` one. Read over an exponential expansion the
same sentence asks about a `2ⁿ × 2ⁿ` square.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

/-! ### The guessed tiling -/

section Kernel

/-- The single existential block of the `Σ₁` definition: one ternary relation
variable, read as “the cell in this column and this row carries this tile”. -/
def tileGuessBlock : SOBlock where
  ι := Unit
  arity := fun _ => 3

/-- The symbol of the guessed tiling. -/
def tgTileRel : tileGuessBlock.lang.Relations 3 := ⟨(), rfl⟩

/-- The vocabulary of the kernel: tile systems together with the guessed
tiling. -/
abbrev tileSOLang : Language := Language.tiling.sum tileGuessBlock.lang

/-- The position symbol in the kernel's vocabulary. -/
abbrev tsPosn : tileSOLang.Relations 1 := Sum.inl tlPosn

/-- The tile symbol in the kernel's vocabulary. -/
abbrev tsTile : tileSOLang.Relations 1 := Sum.inl tlTile

/-- The accepting-tile symbol in the kernel's vocabulary. -/
abbrev tsAcc : tileSOLang.Relations 1 := Sum.inl tlAcc

/-- The order symbol in the kernel's vocabulary. -/
abbrev tsLe : tileSOLang.Relations 2 := Sum.inl tlLe

/-- The horizontal-compatibility symbol in the kernel's vocabulary. -/
abbrev tsHoriz : tileSOLang.Relations 2 := Sum.inl tlHoriz

/-- The vertical-compatibility symbol in the kernel's vocabulary. -/
abbrev tsVert : tileSOLang.Relations 2 := Sum.inl tlVert

/-- The bottom-row symbol in the kernel's vocabulary. -/
abbrev tsFirst : tileSOLang.Relations 2 := Sum.inl tlFirst

/-- The base-tile symbol in the kernel's vocabulary. -/
abbrev tsBase : tileSOLang.Relations 1 := Sum.inl tlBase

/-- The start-tile symbol in the kernel's vocabulary. -/
abbrev tsStart : tileSOLang.Relations 1 := Sum.inl tlStart

/-- The left-edge symbol in the kernel's vocabulary. -/
abbrev tsEdgeL : tileSOLang.Relations 1 := Sum.inl tlEdgeL

/-- The right-edge symbol in the kernel's vocabulary. -/
abbrev tsEdgeR : tileSOLang.Relations 1 := Sum.inl tlEdgeR

/-- The guessed tiling's symbol in the kernel's vocabulary. -/
abbrev tsRel : tileSOLang.Relations 3 := Sum.inr tgTileRel

/-! ### The atoms, at an arbitrary index of free variables -/

section Atoms

variable {γ : Type}

/-- `x` is a position. -/
noncomputable def tlPosnF (x : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsPosn (Term.var x)

/-- `t` is a tile. -/
noncomputable def tlTileF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsTile (Term.var t)

/-- `t` is an accepting tile. -/
noncomputable def tlAccF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsAcc (Term.var t)

/-- `x` is at most `y`. -/
noncomputable def tlLeF (x y : γ) : tileSOLang.Formula γ :=
  Relations.formula₂ tsLe (Term.var x) (Term.var y)

/-- `t'` may stand immediately to the right of `t`. -/
noncomputable def tlHorizF (t t' : γ) : tileSOLang.Formula γ :=
  Relations.formula₂ tsHoriz (Term.var t) (Term.var t')

/-- `t'` may stand immediately above `t`. -/
noncomputable def tlVertF (t t' : γ) : tileSOLang.Formula γ :=
  Relations.formula₂ tsVert (Term.var t) (Term.var t')

/-- The bottom row's cell in column `x` may carry `t`. -/
noncomputable def tlFirstF (x t : γ) : tileSOLang.Formula γ :=
  Relations.formula₂ tsFirst (Term.var x) (Term.var t)

/-- `t` is a base tile. -/
noncomputable def tlBaseF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsBase (Term.var t)

/-- `t` is a start tile. -/
noncomputable def tlStartF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsStart (Term.var t)

/-- `t` may stand in the leftmost column. -/
noncomputable def tlEdgeLF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsEdgeL (Term.var t)

/-- `t` may stand in the rightmost column. -/
noncomputable def tlEdgeRF (t : γ) : tileSOLang.Formula γ :=
  Relations.formula₁ tsEdgeR (Term.var t)

/-- The cell in column `x` and row `y` carries the tile `t`. -/
noncomputable def tlRelF (x y t : γ) : tileSOLang.Formula γ :=
  Relations.formula tsRel ![Term.var x, Term.var y, Term.var t]

/-- `x` and `y` are the same element. -/
noncomputable def tlEqF (x y : γ) : tileSOLang.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

end Atoms

/-! ### What the kernel says -/

variable {A : Type} [Language.tiling.Structure A]

section Realize

variable {γ : Type} (ρ : tileGuessBlock.Assignment A) {v : γ → A}

@[simp]
theorem realize_tlPosnF (x : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlPosnF x) v ↔ TLPosn (v x)) := by
  let := tileGuessBlock.structure ρ
  rw [tlPosnF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlTileF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlTileF t) v ↔ TLTile (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlTileF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlAccF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlAccF t) v ↔ TLAcc (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlAccF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlLeF (x y : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlLeF x y) v ↔ TLLe (v x) (v y)) := by
  let := tileGuessBlock.structure ρ
  rw [tlLeF, Formula.realize_rel₂, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlHorizF (t t' : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlHorizF t t') v ↔ TLHoriz (v t) (v t')) := by
  let := tileGuessBlock.structure ρ
  rw [tlHorizF, Formula.realize_rel₂, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlVertF (t t' : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlVertF t t') v ↔ TLVert (v t) (v t')) := by
  let := tileGuessBlock.structure ρ
  rw [tlVertF, Formula.realize_rel₂, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlFirstF (x t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlFirstF x t) v ↔ TLFirst (v x) (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlFirstF, Formula.realize_rel₂, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlBaseF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlBaseF t) v ↔ TLBase (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlBaseF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlStartF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlStartF t) v ↔ TLStart (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlStartF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlEdgeLF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlEdgeLF t) v ↔ TLEdgeL (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlEdgeLF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlEdgeRF (t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlEdgeRF t) v ↔ TLEdgeR (v t)) := by
  let := tileGuessBlock.structure ρ
  rw [tlEdgeRF, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlRelF (x y t : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlRelF x y t) v ↔ ρ () ![v x, v y, v t]) := by
  let := tileGuessBlock.structure ρ
  rw [tlRelF, realize_rel₃]
  simp only [Term.realize_var]
  rfl

@[simp]
theorem realize_tlEqF (x y : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlEqF x y) v ↔ v x = v y) := by
  let := tileGuessBlock.structure ρ
  rw [tlEqF, Formula.realize_equal, Term.realize_var, Term.realize_var]

end Realize

/-! ### The two order guards, as formulas -/

section Guards

variable {γ : Type}

/-- `y` is the least position. -/
noncomputable def tlMinPosF (y : γ) : tileSOLang.Formula γ :=
  tlPosnF y ⊓ Formula.iAlls (Fin 1) (tlPosnF (Sum.inr 0) ⟹ tlLeF (Sum.inl y) (Sum.inr 0))

/-- `y` is the greatest position. -/
noncomputable def tlMaxPosF (y : γ) : tileSOLang.Formula γ :=
  tlPosnF y ⊓ Formula.iAlls (Fin 1) (tlPosnF (Sum.inr 0) ⟹ tlLeF (Sum.inr 0) (Sum.inl y))

/-- `x'` is the position immediately above `x`. -/
noncomputable def tlSuccPosF (x x' : γ) : tileSOLang.Formula γ :=
  tlPosnF x ⊓ (tlPosnF x' ⊓ (tlLeF x x' ⊓ (∼(tlEqF x x') ⊓
    Formula.iAlls (Fin 1)
      ((tlPosnF (Sum.inr 0) ⊓ (tlLeF (Sum.inl x) (Sum.inr 0) ⊓ tlLeF (Sum.inr 0) (Sum.inl x'))) ⟹
        (tlEqF (Sum.inr 0) (Sum.inl x) ⊔ tlEqF (Sum.inr 0) (Sum.inl x'))))))

variable {A : Type} [Language.tiling.Structure A] (ρ : tileGuessBlock.Assignment A) {v : γ → A}

@[simp]
theorem realize_tlMinPosF (y : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlMinPosF y) v ↔ MinPos (tileData A).Le (tileData A).Posn (v y)) := by
  let := tileGuessBlock.structure ρ
  rw [tlMinPosF, MinPos]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tlPosnF, realize_tlLeF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w hw => h (w 0) hw⟩

@[simp]
theorem realize_tlMaxPosF (y : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlMaxPosF y) v ↔ MaxPos (tileData A).Le (tileData A).Posn (v y)) := by
  let := tileGuessBlock.structure ρ
  rw [tlMaxPosF, MaxPos]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_tlPosnF, realize_tlLeF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w hw => h (w 0) hw⟩

@[simp]
theorem realize_tlSuccPosF (x x' : γ) :
    (@Formula.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ)) _
      (tlSuccPosF x x') v ↔ SuccPos (tileData A).Le (tileData A).Posn (v x) (v x')) := by
  let := tileGuessBlock.structure ρ
  rw [tlSuccPosF, SuccPos]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_tlPosnF, realize_tlLeF, realize_tlEqF,
    Sum.elim_inl, Sum.elim_inr]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  exact ⟨fun h q hq h1 h2 => h (fun _ => q) ⟨hq, h1, h2⟩,
    fun h w hw => h (w 0) hw.1 hw.2.1 hw.2.2⟩

end Guards

/-! ### The clauses of the kernel -/

section Clauses

/-- The order is linear and there is a position: the well-formedness the
yes-instances fold in. -/
noncomputable def tileWfC : tileSOLang.Sentence :=
  (Formula.iAlls (Fin 1) (tlLeF (Sum.inr 0) (Sum.inr 0)) ⊓
      (Formula.iAlls (Fin 3)
          ((tlLeF (Sum.inr 0) (Sum.inr 1) ⊓ tlLeF (Sum.inr 1) (Sum.inr 2)) ⟹
            tlLeF (Sum.inr 0) (Sum.inr 2)) ⊓
        (Formula.iAlls (Fin 2)
            ((tlLeF (Sum.inr 0) (Sum.inr 1) ⊓ tlLeF (Sum.inr 1) (Sum.inr 0)) ⟹
              tlEqF (Sum.inr 0) (Sum.inr 1)) ⊓
          Formula.iAlls (Fin 2) (tlLeF (Sum.inr 0) (Sum.inr 1) ⊔ tlLeF (Sum.inr 1) (Sum.inr 0))))) ⊓
    Formula.iExs (Fin 1) (tlPosnF (Sum.inr 0))

/-- Every cell of the grid carries a tile of the instance. -/
noncomputable def tileTotalC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((tlPosnF (Sum.inr 0) ⊓ tlPosnF (Sum.inr 1)) ⟹
      Formula.iExs (Fin 1)
        (tlRelF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)) (Sum.inr 0) ⊓ tlTileF (Sum.inr 0)))

/-- A cell carries at most one tile. -/
noncomputable def tileFuncC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 4)
    ((tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)) ⟹
      tlEqF (Sum.inr 2) (Sum.inr 3))

/-- The bottom row is one the description allows: the tiles it names in that
column, or a base tile where it names none. -/
noncomputable def tileFirstC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((tlPosnF (Sum.inr 0) ⊓ (tlMinPosF (Sum.inr 1) ⊓ tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))) ⟹
      ((tlMinPosF (Sum.inr 0) ⟹ tlStartF (Sum.inr 2)) ⊓
        (∼(tlMinPosF (Sum.inr 0)) ⟹
          (tlFirstF (Sum.inr 0) (Sum.inr 2) ⊔
            (Formula.iAlls (Fin 1) (∼(tlFirstF (Sum.inl (Sum.inr 0)) (Sum.inr 0))) ⊓
              tlBaseF (Sum.inr 2))))))

/-- The leftmost column carries tiles allowed there. -/
noncomputable def tileEdgeLC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((tlPosnF (Sum.inr 1) ⊓ (tlMinPosF (Sum.inr 0) ⊓
      tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))) ⟹ tlEdgeLF (Sum.inr 2))

/-- And the rightmost column those allowed there. -/
noncomputable def tileEdgeRC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 3)
    ((tlPosnF (Sum.inr 1) ⊓ (tlMaxPosF (Sum.inr 0) ⊓
      tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))) ⟹ tlEdgeRF (Sum.inr 2))

/-- Horizontal neighbors are compatible. -/
noncomputable def tileHorizC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 5)
    ((tlSuccPosF (Sum.inr 0) (Sum.inr 1) ⊓ (tlPosnF (Sum.inr 2) ⊓
      (tlRelF (Sum.inr 0) (Sum.inr 2) (Sum.inr 3) ⊓
        tlRelF (Sum.inr 1) (Sum.inr 2) (Sum.inr 4)))) ⟹ tlHorizF (Sum.inr 3) (Sum.inr 4))

/-- Vertical neighbors are compatible. -/
noncomputable def tileVertC : tileSOLang.Sentence :=
  Formula.iAlls (Fin 5)
    ((tlPosnF (Sum.inr 0) ⊓ (tlSuccPosF (Sum.inr 1) (Sum.inr 2) ⊓
      (tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3) ⊓
        tlRelF (Sum.inr 0) (Sum.inr 2) (Sum.inr 4)))) ⟹ tlVertF (Sum.inr 3) (Sum.inr 4))

/-- Some cell of the grid carries an accepting tile. -/
noncomputable def tileAccC : tileSOLang.Sentence :=
  Formula.iExs (Fin 3)
    (tlPosnF (Sum.inr 0) ⊓ (tlPosnF (Sum.inr 1) ⊓
      (tlRelF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ tlAccF (Sum.inr 2))))

/-- **The first-order kernel of the `Σ₁` definition**: the tiling the block
guesses is a tiling of the square, and the instance is well-formed. -/
noncomputable def tileKernel : tileSOLang.Sentence :=
  tileWfC ⊓ (tileTotalC ⊓ (tileFuncC ⊓ (tileFirstC ⊓ (tileEdgeLC ⊓ (tileEdgeRC ⊓
    (tileHorizC ⊓ (tileVertC ⊓ tileAccC)))))))

end Clauses

/-! ### What each clause says -/

section ClauseRealize

variable {A : Type} [Language.tiling.Structure A] (ρ : tileGuessBlock.Assignment A)

theorem realize_tileWfC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileWfC ↔ (tileData A).WellFormed) := by
  let := tileGuessBlock.structure ρ
  rw [tileWfC, TileData.WellFormed, IsLinOrd]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_imp, Formula.realize_sup, realize_tlLeF,
    realize_tlEqF, realize_tlPosnF, Sum.elim_inr]
  refine and_congr (and_congr ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
      (and_congr ⟨fun h a b c h1 h2 => h ![a, b, c] ⟨h1, h2⟩,
          fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
        (and_congr ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩))) ?_
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩

theorem realize_tileTotalC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileTotalC ↔
      ∀ x y : A, TLPosn x → TLPosn y → ∃ t, ρ () ![x, y, t] ∧ TLTile t) := by
  let := tileGuessBlock.structure ρ
  rw [tileTotalC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_inf, realize_tlPosnF, realize_tlRelF, realize_tlTileF,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun h x y hx hy => ?_, fun h w hw => ?_⟩
  · obtain ⟨w, hw⟩ := h ![x, y] ⟨hx, hy⟩
    exact ⟨w 0, hw⟩
  · obtain ⟨t, ht⟩ := h (w 0) (w 1) hw.1 hw.2
    exact ⟨fun _ => t, ht⟩

theorem realize_tlTileFuncC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileFuncC ↔
      ∀ x y t t' : A, ρ () ![x, y, t] → ρ () ![x, y, t'] → t = t') := by
  let := tileGuessBlock.structure ρ
  rw [tileFuncC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tlRelF, realize_tlEqF, Sum.elim_inr]
  exact ⟨fun h x y t t' h1 h2 => h ![x, y, t, t'] ⟨h1, h2⟩,
    fun h w hw => h (w 0) (w 1) (w 2) (w 3) hw.1 hw.2⟩

theorem realize_tlTileFirstC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileFirstC ↔
      ∀ x y t : A, TLPosn x → MinPos (tileData A).Le (tileData A).Posn y →
        ρ () ![x, y, t] →
        ((MinPos (tileData A).Le (tileData A).Posn x → TLStart t) ∧
          (¬MinPos (tileData A).Le (tileData A).Posn x →
            (tileData A).FirstTile x t))) := by
  let := tileGuessBlock.structure ρ
  rw [tileFirstC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_tlPosnF,
    realize_tlMinPosF, realize_tlRelF, realize_tlFirstF, realize_tlBaseF,
    realize_tlStartF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x y t h1 h2 h3
    obtain ⟨hst, hfr⟩ := h ![x, y, t] ⟨h1, h2, h3⟩
    refine ⟨hst, fun hmin => ?_⟩
    rcases hfr hmin with hf | ⟨hno, hb⟩
    · exact Or.inl hf
    · exact Or.inr ⟨fun u hu => hno (fun _ => u) hu, hb⟩
  · intro h w hw
    obtain ⟨hst, hfr⟩ := h (w 0) (w 1) (w 2) hw.1 hw.2.1 hw.2.2
    refine ⟨hst, fun hmin => ?_⟩
    rcases hfr hmin with hf | ⟨hno, hb⟩
    · exact Or.inl hf
    · exact Or.inr ⟨fun u hu => hno (u 0) hu, hb⟩

theorem realize_tileEdgeLC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileEdgeLC ↔
      ∀ x y t : A, TLPosn y → MinPos (tileData A).Le (tileData A).Posn x →
        ρ () ![x, y, t] → TLEdgeL t) := by
  let := tileGuessBlock.structure ρ
  rw [tileEdgeLC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tlPosnF, realize_tlMinPosF, realize_tlRelF, realize_tlEdgeLF,
    Sum.elim_inr]
  exact ⟨fun h x y t h1 h2 h3 => h ![x, y, t] ⟨h1, h2, h3⟩,
    fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2.1 hw.2.2⟩

theorem realize_tileEdgeRC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileEdgeRC ↔
      ∀ x y t : A, TLPosn y → MaxPos (tileData A).Le (tileData A).Posn x →
        ρ () ![x, y, t] → TLEdgeR t) := by
  let := tileGuessBlock.structure ρ
  rw [tileEdgeRC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tlPosnF, realize_tlMaxPosF, realize_tlRelF, realize_tlEdgeRF,
    Sum.elim_inr]
  exact ⟨fun h x y t h1 h2 h3 => h ![x, y, t] ⟨h1, h2, h3⟩,
    fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2.1 hw.2.2⟩

theorem realize_tileHorizC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileHorizC ↔
      ∀ x x' y t t' : A, SuccPos (tileData A).Le (tileData A).Posn x x' → TLPosn y →
        ρ () ![x, y, t] → ρ () ![x', y, t'] → TLHoriz t t') := by
  let := tileGuessBlock.structure ρ
  rw [tileHorizC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tlPosnF, realize_tlSuccPosF, realize_tlRelF, realize_tlHorizF,
    Sum.elim_inr]
  exact ⟨fun h x x' y t t' h1 h2 h3 h4 => h ![x, x', y, t, t'] ⟨h1, h2, h3, h4⟩,
    fun h w hw => h (w 0) (w 1) (w 2) (w 3) (w 4) hw.1 hw.2.1 hw.2.2.1 hw.2.2.2⟩

theorem realize_tileVertC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileVertC ↔
      ∀ x y y' t t' : A, TLPosn x → SuccPos (tileData A).Le (tileData A).Posn y y' →
        ρ () ![x, y, t] → ρ () ![x, y', t'] → TLVert t t') := by
  let := tileGuessBlock.structure ρ
  rw [tileVertC]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tlPosnF, realize_tlSuccPosF, realize_tlRelF, realize_tlVertF,
    Sum.elim_inr]
  exact ⟨fun h x y y' t t' h1 h2 h3 h4 => h ![x, y, y', t, t'] ⟨h1, h2, h3, h4⟩,
    fun h w hw => h (w 0) (w 1) (w 2) (w 3) (w 4) hw.1 hw.2.1 hw.2.2.1 hw.2.2.2⟩

theorem realize_tileAccC :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileAccC ↔
      ∃ x y t : A, TLPosn x ∧ TLPosn y ∧ ρ () ![x, y, t] ∧ TLAcc t) := by
  let := tileGuessBlock.structure ρ
  rw [tileAccC]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_tlPosnF, realize_tlRelF, realize_tlAccF, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, w 2, hw⟩, fun ⟨x, y, t, hx⟩ => ⟨![x, y, t], hx⟩⟩

end ClauseRealize

/-! ### The definition -/

section Definable

variable {A : Type} [Language.tiling.Structure A]

/-- **What the kernel says**, at an assignment of the guessed tiling: the
instance is well-formed and the guess is a tiling of the square, read as a
relation. -/
theorem realize_tileKernel (ρ : tileGuessBlock.Assignment A) :
    (@Sentence.Realize tileSOLang A (@sumStructure _ _ A _ (tileGuessBlock.structure ρ))
      tileKernel ↔
      (tileData A).WellFormed ∧
        (∀ x y : A, TLPosn x → TLPosn y → ∃ t, ρ () ![x, y, t] ∧ TLTile t) ∧
        (∀ x y t t' : A, ρ () ![x, y, t] → ρ () ![x, y, t'] → t = t') ∧
        (∀ x y t : A, TLPosn x → MinPos (tileData A).Le (tileData A).Posn y →
          ρ () ![x, y, t] →
          ((MinPos (tileData A).Le (tileData A).Posn x → TLStart t) ∧
            (¬MinPos (tileData A).Le (tileData A).Posn x →
              (tileData A).FirstTile x t))) ∧
        (∀ x y t : A, TLPosn y → MinPos (tileData A).Le (tileData A).Posn x →
          ρ () ![x, y, t] → TLEdgeL t) ∧
        (∀ x y t : A, TLPosn y → MaxPos (tileData A).Le (tileData A).Posn x →
          ρ () ![x, y, t] → TLEdgeR t) ∧
        (∀ x x' y t t' : A, SuccPos (tileData A).Le (tileData A).Posn x x' → TLPosn y →
          ρ () ![x, y, t] → ρ () ![x', y, t'] → TLHoriz t t') ∧
        (∀ x y y' t t' : A, TLPosn x → SuccPos (tileData A).Le (tileData A).Posn y y' →
          ρ () ![x, y, t] → ρ () ![x, y', t'] → TLVert t t') ∧
        ∃ x y t : A, TLPosn x ∧ TLPosn y ∧ ρ () ![x, y, t] ∧ TLAcc t) := by
  let := tileGuessBlock.structure ρ
  rw [tileKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_tileWfC ρ) (and_congr (realize_tileTotalC ρ)
    (and_congr (realize_tlTileFuncC ρ) (and_congr (realize_tlTileFirstC ρ)
      (and_congr (realize_tileEdgeLC ρ) (and_congr (realize_tileEdgeRC ρ)
        (and_congr (realize_tileHorizC ρ) (and_congr (realize_tileVertC ρ)
          (realize_tileAccC ρ))))))))

/-- **Tiling a square is `Σ₁`-definable**: guess the tiling as one ternary
relation, and check first-order that it is one. Since NP is `Σ₁`-definability,
this is the membership half of the problem's completeness. -/
theorem tiling_sigmaSODefinable : SigmaSODefinable 1 TILING := by
  refine ⟨[tileGuessBlock], rfl, tileKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨hwf, τ, htile, hfirst, hel, her, hhoriz, hvert, x₀, y₀, hx₀, hy₀, hacc⟩
    refine ⟨fun () (w : Fin 3 → A) => w 2 = τ (w 0) (w 1), (realize_tileKernel _).mpr
      ⟨hwf, fun x y hx hy => ⟨τ x y, rfl, htile x y hx hy⟩, fun x y t t' h1 h2 => ?_,
        fun x y t hx hy ht => ?_, fun x y t hy hx ht => ?_, fun x y t hy hx ht => ?_,
        fun x x' y t t' hs hy h1 h2 => ?_,
        fun x y y' t t' hx hs h1 h2 => ?_, x₀, y₀, τ x₀ y₀, hx₀, hy₀, rfl, hacc⟩⟩
    · exact h1.trans h2.symm
    · rw [show t = τ x y from ht]
      exact hfirst x y hx hy
    · rw [show t = τ x y from ht]
      exact hel x y hy hx
    · rw [show t = τ x y from ht]
      exact her x y hy hx
    · rw [show t = τ x y from h1, show t' = τ x' y from h2]
      exact hhoriz x x' y hs hy
    · rw [show t = τ x y from h1, show t' = τ x y' from h2]
      exact hvert x y y' hx hs
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hwf, htotal, hfunc, hfirst, hel, her, hhoriz, hvert,
      x₀, y₀, t₀, hx₀, hy₀, ht₀, hacc⟩ :=
      (realize_tileKernel ρ).mp hρ
    classical
    -- the tile a cell carries, read off the guessed relation
    set τ : A → A → A := fun x y => if h : ∃ t, ρ () ![x, y, t] then h.choose else x with hτ
    have hread : ∀ x y t, ρ () ![x, y, t] → τ x y = t := by
      intro x y t ht
      have hex : ∃ t, ρ () ![x, y, t] := ⟨t, ht⟩
      rw [hτ]
      simp only [dif_pos hex]
      exact hfunc x y hex.choose t hex.choose_spec ht
    refine ⟨hwf, τ, fun x y hx hy => ?_, fun x y hx hy => ?_, fun x y hy hx => ?_,
      fun x y hy hx => ?_, fun x x' y hs hy => ?_,
      fun x y y' hx hs => ?_, x₀, y₀, hx₀, hy₀, ?_⟩
    · obtain ⟨t, ht, htile⟩ := htotal x y hx hy
      rw [hread x y t ht]
      exact htile
    · obtain ⟨t, ht, -⟩ := htotal x y hx hy.1
      rw [hread x y t ht]
      exact hfirst x y t hx hy ht
    · obtain ⟨t, ht, -⟩ := htotal x y hx.1 hy
      rw [hread x y t ht]
      exact hel x y t hy hx ht
    · obtain ⟨t, ht, -⟩ := htotal x y hx.1 hy
      rw [hread x y t ht]
      exact her x y t hy hx ht
    · obtain ⟨t, ht, -⟩ := htotal x y hs.1 hy
      obtain ⟨t', ht', -⟩ := htotal x' y hs.2.1 hy
      rw [hread x y t ht, hread x' y t' ht']
      exact hhoriz x x' y t t' hs hy ht ht'
    · obtain ⟨t, ht, -⟩ := htotal x y hx hs.1
      obtain ⟨t', ht', -⟩ := htotal x y' hx hs.2.1
      rw [hread x y t ht, hread x y' t' ht']
      exact hvert x y y' t t' hx hs ht ht'
    · rw [hread x₀ y₀ t₀ ht₀]
      exact hacc

/-- **Tiling a square is in NP.** -/
theorem tiling_mem_NP : TILING ∈ NP := tiling_sigmaSODefinable

end Definable

end Kernel

end DescriptiveComplexity
