/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Emit

/-!
# The atoms the drawing is written with

The vocabulary a reduction *from* a wide machine writes its formulas in: the
machine's own relations, over the ordered expansion `Language.wide.sum
Language.order`, one shorthand each, together with the two shapes every tile
formula is built from –

* a **static** choice on the tags, `DescriptiveComplexity.TilingHard.tagIfF`,
  which is where all the case analysis of the drawing goes;
* the machine's promises as a sentence,
  `DescriptiveComplexity.TilingHard.wideWFF`, which the start tile carries.

Everything here is about the *source* of the reduction, so it says nothing about
tiles; the formulas that draw them are in
`DescriptiveComplexity.Problems.Wide.TilingHard.Draw`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-- The vocabulary the drawing's formulas are written in: the machine's, with
the order of the instance. -/
abbrev wideOrd : Language.{0, 0} := Language.wide.sum Language.order

/-! ### The machine's relations, as atoms -/

section Atoms

/-- The order symbol of the machine, in the drawing's vocabulary. -/
abbrev wdLeSym : wideOrd.Relations 2 := Sum.inl wmLe

/-- The transition symbol, in the drawing's vocabulary. -/
abbrev wdTrSym : wideOrd.Relations 1 := Sum.inl wmTr

/-- The start-state symbol, in the drawing's vocabulary. -/
abbrev wdStartSym : wideOrd.Relations 1 := Sum.inl wmStart

/-- The accepting-state symbol, in the drawing's vocabulary. -/
abbrev wdAccSym : wideOrd.Relations 1 := Sum.inl wmAcc

/-- The blank symbol, in the drawing's vocabulary. -/
abbrev wdBlankSym : wideOrd.Relations 1 := Sum.inl wmBlank

/-- The right-move symbol, in the drawing's vocabulary. -/
abbrev wdRightSym : wideOrd.Relations 1 := Sum.inl wmRight

/-- The source-state symbol, in the drawing's vocabulary. -/
abbrev wdSrcSym : wideOrd.Relations 2 := Sum.inl wmSrc

/-- The read-symbol symbol, in the drawing's vocabulary. -/
abbrev wdReadSym : wideOrd.Relations 2 := Sum.inl wmRead

/-- The destination-state symbol, in the drawing's vocabulary. -/
abbrev wdDstSym : wideOrd.Relations 2 := Sum.inl wmDst

/-- The written-symbol symbol, in the drawing's vocabulary. -/
abbrev wdWriteSym : wideOrd.Relations 2 := Sum.inl wmWrite

/-- The input symbol, in the drawing's vocabulary. -/
abbrev wdInpSym : wideOrd.Relations 2 := Sum.inl wmInp

variable {γ : Type}

/-- `x ≤ y` in the machine's own order. -/
noncomputable def wdLeF (x y : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdLeSym (Term.var x) (Term.var y)

/-- `t` is a transition. -/
noncomputable def wdTrF (t : γ) : wideOrd.Formula γ :=
  Relations.formula₁ wdTrSym (Term.var t)

/-- `q` is a start state. -/
noncomputable def wdStartF (q : γ) : wideOrd.Formula γ :=
  Relations.formula₁ wdStartSym (Term.var q)

/-- `q` is an accepting state. -/
noncomputable def wdAccF (q : γ) : wideOrd.Formula γ :=
  Relations.formula₁ wdAccSym (Term.var q)

/-- `a` is the blank symbol. -/
noncomputable def wdBlankF (a : γ) : wideOrd.Formula γ :=
  Relations.formula₁ wdBlankSym (Term.var a)

/-- `t` moves the head to the right. -/
noncomputable def wdRightF (t : γ) : wideOrd.Formula γ :=
  Relations.formula₁ wdRightSym (Term.var t)

/-- `t` applies in the state `q`. -/
noncomputable def wdSrcF (t q : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdSrcSym (Term.var t) (Term.var q)

/-- `t` applies on the symbol `a`. -/
noncomputable def wdReadF (t a : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdReadSym (Term.var t) (Term.var a)

/-- `t` moves to the state `q`. -/
noncomputable def wdDstF (t q : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdDstSym (Term.var t) (Term.var q)

/-- `t` writes the symbol `a`. -/
noncomputable def wdWriteF (t a : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdWriteSym (Term.var t) (Term.var a)

/-- The cell of `x` starts holding `a`. -/
noncomputable def wdInpF (x a : γ) : wideOrd.Formula γ :=
  Relations.formula₂ wdInpSym (Term.var x) (Term.var a)

/-- `x` and `y` are the same element. -/
noncomputable def wdEqF (x y : γ) : wideOrd.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_wdLeF (x y : γ) : (wdLeF x y).Realize v ↔ WMLe (v x) (v y) := by
  simp only [wdLeF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdTrF (t : γ) : (wdTrF t).Realize v ↔ WMTr (v t) := by
  simp only [wdTrF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdStartF (q : γ) : (wdStartF q).Realize v ↔ WMStart (v q) := by
  simp only [wdStartF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdAccF (q : γ) : (wdAccF q).Realize v ↔ WMAcc (v q) := by
  simp only [wdAccF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdBlankF (a : γ) : (wdBlankF a).Realize v ↔ WMBlank (v a) := by
  simp only [wdBlankF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdRightF (t : γ) : (wdRightF t).Realize v ↔ WMRight (v t) := by
  simp only [wdRightF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdSrcF (t q : γ) : (wdSrcF t q).Realize v ↔ WMSrc (v t) (v q) := by
  simp only [wdSrcF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdReadF (t a : γ) : (wdReadF t a).Realize v ↔ WMRead (v t) (v a) := by
  simp only [wdReadF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdDstF (t q : γ) : (wdDstF t q).Realize v ↔ WMDst (v t) (v q) := by
  simp only [wdDstF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdWriteF (t a : γ) : (wdWriteF t a).Realize v ↔ WMWrite (v t) (v a) := by
  simp only [wdWriteF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdInpF (x a : γ) : (wdInpF x a).Realize v ↔ WMInp (v x) (v a) := by
  simp only [wdInpF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdEqF (x y : γ) : (wdEqF x y).Realize v ↔ v x = v y := by
  rw [wdEqF, Formula.realize_equal, Term.realize_var, Term.realize_var]

end Atoms

/-! ### The two shapes every tile formula is built from -/

section Shapes

variable {γ : Type}

open Classical in
/-- **A static choice on the tags**: the truth value a tag decides, as a
formula. Every case analysis the drawing does on tags is one of these, so the
formulas themselves stay small. -/
noncomputable def tagIfF (b : Prop) : wideOrd.Formula γ := if b then ⊤ else ⊥

/-- **The machine's promises**: the order is linear, the input is functional,
and there is exactly one blank. This is
`DescriptiveComplexity.WideWF` written out, and the start tile is where the
drawing carries it – a no-instance whose promises fail has no start tile, hence
no tiling. -/
noncomputable def wideWFF : wideOrd.Formula γ :=
  (Formula.iAlls (Fin 1) (wdLeF (Sum.inr 0) (Sum.inr 0)) ⊓
      (Formula.iAlls (Fin 3)
          ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 2)) ⟹
            wdLeF (Sum.inr 0) (Sum.inr 2)) ⊓
        (Formula.iAlls (Fin 2)
            ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 0)) ⟹
              wdEqF (Sum.inr 0) (Sum.inr 1)) ⊓
          Formula.iAlls (Fin 2)
            (wdLeF (Sum.inr 0) (Sum.inr 1) ⊔ wdLeF (Sum.inr 1) (Sum.inr 0))))) ⊓
    (Formula.iAlls (Fin 3)
        ((wdInpF (Sum.inr 0) (Sum.inr 1) ⊓ wdInpF (Sum.inr 0) (Sum.inr 2)) ⟹
          wdEqF (Sum.inr 1) (Sum.inr 2)) ⊓
      (Formula.iExs (Fin 1) (wdBlankF (Sum.inr 0)) ⊓
        Formula.iAlls (Fin 2)
          ((wdBlankF (Sum.inr 0) ⊓ wdBlankF (Sum.inr 1)) ⟹ wdEqF (Sum.inr 0) (Sum.inr 1))))

variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_tagIfF (b : Prop) : ((tagIfF b).Realize v) ↔ b := by
  classical
  by_cases hb : b
  · rw [tagIfF, if_pos hb]
    simp only [Formula.realize_top]
    exact iff_of_true trivial hb
  · rw [tagIfF, if_neg hb]
    simp only [Formula.realize_bot]
    exact iff_of_false (fun h => h) hb

@[simp]
theorem realize_wideWFF : ((wideWFF (γ := γ)).Realize v) ↔ WideWF A := by
  rw [wideWFF, WideWF, IsLinOrd]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_sup, realize_wdLeF, realize_wdEqF,
    realize_wdInpF, realize_wdBlankF, Sum.elim_inr]
  refine and_congr (and_congr ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
      (and_congr ⟨fun h a b c h1 h2 => h ![a, b, c] ⟨h1, h2⟩,
          fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
        (and_congr ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩)))
    (and_congr ⟨fun h x a b h1 h2 => h ![x, a, b] ⟨h1, h2⟩,
        fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
      (and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
        ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩))

end Shapes

end TilingHard

end DescriptiveComplexity
