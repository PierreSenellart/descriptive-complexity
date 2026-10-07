/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.TilingHard.Emit
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

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wmAcc wmBlank wmDst wmInp wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMRead WMRight WMSrc WMStart WMTr WMWrite)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-- The vocabulary the drawing's formulas are written in: the machine's, with
the order of the instance. -/
abbrev wideOrd : Language.{0, 0} := Lax822549.WideMachines.wide.sum Language.order

/-! ### The machine's relations, as atoms -/

section Atoms

/-- The order symbol of the machine, in the drawing's vocabulary. -/
abbrev wdLeSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmLe

/-- The transition symbol, in the drawing's vocabulary. -/
abbrev wdTrSym : wideOrd.Relations 1 := Sum.inl Lax822549.WideMachines.wmTr

/-- The start-state symbol, in the drawing's vocabulary. -/
abbrev wdStartSym : wideOrd.Relations 1 := Sum.inl Lax822549.WideMachines.wmStart

/-- The accepting-state symbol, in the drawing's vocabulary. -/
abbrev wdAccSym : wideOrd.Relations 1 := Sum.inl Lax822549.WideMachines.wmAcc

/-- The blank symbol, in the drawing's vocabulary. -/
abbrev wdBlankSym : wideOrd.Relations 1 := Sum.inl Lax822549.WideMachines.wmBlank

/-- The right-move symbol, in the drawing's vocabulary. -/
abbrev wdRightSym : wideOrd.Relations 1 := Sum.inl Lax822549.WideMachines.wmRight

/-- The source-state symbol, in the drawing's vocabulary. -/
abbrev wdSrcSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmSrc

/-- The read-symbol symbol, in the drawing's vocabulary. -/
abbrev wdReadSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmRead

/-- The destination-state symbol, in the drawing's vocabulary. -/
abbrev wdDstSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmDst

/-- The written-symbol symbol, in the drawing's vocabulary. -/
abbrev wdWriteSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmWrite

/-- The input symbol, in the drawing's vocabulary. -/
abbrev wdInpSym : wideOrd.Relations 2 := Sum.inl Lax822549.WideMachines.wmInp

variable {γ : Type}

/-- `x ≤ y` in the machine's own order. -/
noncomputable def wdLeF (x y : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdLeSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- `t` is a transition. -/
noncomputable def wdTrF (t : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₁ wdTrSym (FirstOrder.Language.Term.var t)

/-- `q` is a start state. -/
noncomputable def wdStartF (q : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₁ wdStartSym (FirstOrder.Language.Term.var q)

/-- `q` is an accepting state. -/
noncomputable def wdAccF (q : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₁ wdAccSym (FirstOrder.Language.Term.var q)

/-- `a` is the blank symbol. -/
noncomputable def wdBlankF (a : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₁ wdBlankSym (FirstOrder.Language.Term.var a)

/-- `t` moves the head to the right. -/
noncomputable def wdRightF (t : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₁ wdRightSym (FirstOrder.Language.Term.var t)

/-- `t` applies in the state `q`. -/
noncomputable def wdSrcF (t q : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdSrcSym (FirstOrder.Language.Term.var t) (FirstOrder.Language.Term.var q)

/-- `t` applies on the symbol `a`. -/
noncomputable def wdReadF (t a : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdReadSym (FirstOrder.Language.Term.var t) (FirstOrder.Language.Term.var a)

/-- `t` moves to the state `q`. -/
noncomputable def wdDstF (t q : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdDstSym (FirstOrder.Language.Term.var t) (FirstOrder.Language.Term.var q)

/-- `t` writes the symbol `a`. -/
noncomputable def wdWriteF (t a : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdWriteSym (FirstOrder.Language.Term.var t) (FirstOrder.Language.Term.var a)

/-- The cell of `x` starts holding `a`. -/
noncomputable def wdInpF (x a : γ) : wideOrd.Formula γ := FirstOrder.Language.Relations.formula₂ wdInpSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var a)

/-- `x` and `y` are the same element. -/
noncomputable def wdEqF (x y : γ) : wideOrd.Formula γ := FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_wdLeF (x y : γ) : (wdLeF x y).Realize v ↔ Lax822549.WideMachines.WMLe (v x) (v y) := by
  simp only [wdLeF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdTrF (t : γ) : (wdTrF t).Realize v ↔ Lax822549.WideMachines.WMTr (v t) := by
  simp only [wdTrF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdStartF (q : γ) : (wdStartF q).Realize v ↔ Lax822549.WideMachines.WMStart (v q) := by
  simp only [wdStartF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdAccF (q : γ) : (wdAccF q).Realize v ↔ Lax822549.WideMachines.WMAcc (v q) := by
  simp only [wdAccF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdBlankF (a : γ) : (wdBlankF a).Realize v ↔ Lax822549.WideMachines.WMBlank (v a) := by
  simp only [wdBlankF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdRightF (t : γ) : (wdRightF t).Realize v ↔ Lax822549.WideMachines.WMRight (v t) := by
  simp only [wdRightF, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_wdSrcF (t q : γ) : (wdSrcF t q).Realize v ↔ Lax822549.WideMachines.WMSrc (v t) (v q) := by
  simp only [wdSrcF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdReadF (t a : γ) : (wdReadF t a).Realize v ↔ Lax822549.WideMachines.WMRead (v t) (v a) := by
  simp only [wdReadF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdDstF (t q : γ) : (wdDstF t q).Realize v ↔ Lax822549.WideMachines.WMDst (v t) (v q) := by
  simp only [wdDstF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdWriteF (t a : γ) : (wdWriteF t a).Realize v ↔ Lax822549.WideMachines.WMWrite (v t) (v a) := by
  simp only [wdWriteF, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_wdInpF (x a : γ) : (wdInpF x a).Realize v ↔ Lax822549.WideMachines.WMInp (v x) (v a) := by
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
  FirstOrder.Language.Formula.iAlls (Fin 1) (wdLeF (Sum.inr 0) (Sum.inr 0)) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 3)
            ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 2)).imp (wdLeF (Sum.inr 0) (Sum.inr 2))) ⊓
          (FirstOrder.Language.Formula.iAlls (Fin 2)
              ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 0)).imp (wdEqF (Sum.inr 0) (Sum.inr 1))) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 2) (wdLeF (Sum.inr 0) (Sum.inr 1) ⊔ wdLeF (Sum.inr 1) (Sum.inr 0)))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          ((wdInpF (Sum.inr 0) (Sum.inr 1) ⊓ wdInpF (Sum.inr 0) (Sum.inr 2)).imp (wdEqF (Sum.inr 1) (Sum.inr 2))) ⊓
        (FirstOrder.Language.Formula.iExs (Fin 1) (wdBlankF (Sum.inr 0)) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            ((wdBlankF (Sum.inr 0) ⊓ wdBlankF (Sum.inr 1)).imp (wdEqF (Sum.inr 0) (Sum.inr 1)))))

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] {v : γ → A}

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
  rw [wideWFF, WideWF, Lax904597.Machines.IsLinOrd]
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

end Lax822549Proofs.DescriptiveComplexity


