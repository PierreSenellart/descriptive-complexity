/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax480241Proofs.DescriptiveComplexity.Problems.MachineAltSpace
import Lax480241Proofs.DescriptiveComplexity.Exponential.Game
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241.AlternatingSpace.ATMData
end Lax480241.AlternatingSpace.ATMData

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMAcc ATMBlank ATMDst ATMInp ATMLe ATMPosn ATMRead ATMRight ATMSrc ATMStart ATMTr ATMWrite atmData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData
export Lax480241.AlternatingSpace.ATMData (BlocksSplit)
end Lax564036.AlternatingMachines.ATMData

namespace FirstOrder.Language
export Lax564036.AlternatingMachines (atmAcc atmBlank atmBlk atmDst atmInp atmLe atmPosn atmRead atmRight atmSrc atmStart atmTr atmWrite turingAlt)
end FirstOrder.Language

/-!
# The guards of the alternating machine, and the configuration block

The first of the three layers that put `DescriptiveComplexity.ATMAcceptSpace`
in EXPTIME. Everything here is bookkeeping:

* the symbols of `FirstOrder.Language.turingAlt 2` in the **ordered** expansion,
  as abbreviations with declared types – a raw `Sum.inl r` inside
  `FirstOrder.Language.Relations.formula₁` does not elaborate;
* one guard per symbol, at an arbitrary variable type, with its realization
  lemma, in the style of `DescriptiveComplexity.Problems.Machine.Fixpoint`;
* the derived guards `minPosG`, `succPosG`, `initTapeG` and the two promise
  *sentences* `wfS` (`DescriptiveComplexity.TMData.WellFormed`) and
  `blocksSplitS` (`DescriptiveComplexity.ATMData.BlocksSplit`);
* the **configuration block** `cfgBlock` – one variable for the state, one for
  the head, one for the tape – its atoms at one and at two copies, and the
  lifts that read a base guard there.

The block has a binary variable for the tape because a
`DescriptiveComplexity.Config` carries a *function* `A → A`; that the variable
is one is the content of `DescriptiveComplexity.ATMSpace.isCfgS`, and
`DescriptiveComplexity.ATMSpace.cfgOf` is the assignment a configuration is.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ATMSpace

/-! ### The ordered vocabulary and its symbols -/

/-- The ordered expansion of the alternating machine vocabulary, at two
blocks. -/
abbrev tmaOrd : Language.{0, 0} := (Lax564036.AlternatingMachines.turingAlt 2).sum Language.order

/-- The position symbol. -/
abbrev posnO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmPosn

/-- The transition symbol. -/
abbrev trO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmTr

/-- The start-state symbol. -/
abbrev startO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmStart

/-- The accepting-state symbol. -/
abbrev accO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmAcc

/-- The blank symbol. -/
abbrev blankO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmBlank

/-- The move-right symbol. -/
abbrev rightO : tmaOrd.Relations 1 := Sum.inl Lax564036.AlternatingMachines.atmRight

/-- The order symbol of the machine. -/
abbrev leO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmLe

/-- The transition-source symbol. -/
abbrev srcO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmSrc

/-- The transition-read symbol. -/
abbrev readO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmRead

/-- The transition-destination symbol. -/
abbrev dstO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmDst

/-- The transition-write symbol. -/
abbrev writeO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmWrite

/-- The input symbol. -/
abbrev inpO : tmaOrd.Relations 2 := Sum.inl Lax564036.AlternatingMachines.atmInp

/-- The mark of the `i`-th player. -/
abbrev blkO (i : Fin 2) : tmaOrd.Relations 1 := Sum.inl (Lax564036.AlternatingMachines.atmBlk i)

/-! ### One guard per symbol -/

section Guards

variable {γ : Type}

/-- `x` is a position. -/
noncomputable def posnG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ posnO (FirstOrder.Language.Term.var x)

/-- `x` is a transition. -/
noncomputable def trG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ trO (FirstOrder.Language.Term.var x)

/-- `x` is a start state. -/
noncomputable def startG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ startO (FirstOrder.Language.Term.var x)

/-- `x` is an accepting state. -/
noncomputable def accG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ accO (FirstOrder.Language.Term.var x)

/-- `x` is the blank symbol. -/
noncomputable def blankG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ blankO (FirstOrder.Language.Term.var x)

/-- The transition `x` moves the head right. -/
noncomputable def rightG (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ rightO (FirstOrder.Language.Term.var x)

/-- `x` is marked by the `i`-th player. -/
noncomputable def blkG (i : Fin 2) (x : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₁ (blkO i) (FirstOrder.Language.Term.var x)

/-- `x ≤ y` in the machine's own order. -/
noncomputable def leG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ leO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` applies in the state `y`. -/
noncomputable def srcG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ srcO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` reads the symbol `y`. -/
noncomputable def readG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ readO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` moves to the state `y`. -/
noncomputable def dstG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ dstO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The transition `x` writes the symbol `y`. -/
noncomputable def writeG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ writeO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- The cell `x` initially holds the input symbol `y`. -/
noncomputable def inpG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Relations.formula₂ inpO (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

/-- `x` and `y` are the same element. -/
noncomputable def eqG (x y : γ) : tmaOrd.Formula γ := FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)

variable {A : Type} [(Lax564036.AlternatingMachines.turingAlt 2).Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_posnG (x : γ) : (posnG x).Realize v ↔ Lax564036.AlternatingMachines.ATMPosn (k := 2) (v x) := by
  rw [posnG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_trG (x : γ) : (trG x).Realize v ↔ Lax564036.AlternatingMachines.ATMTr (k := 2) (v x) := by
  rw [trG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_startG (x : γ) : (startG x).Realize v ↔ Lax564036.AlternatingMachines.ATMStart (k := 2) (v x) := by
  rw [startG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_accG (x : γ) : (accG x).Realize v ↔ Lax564036.AlternatingMachines.ATMAcc (k := 2) (v x) := by
  rw [accG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_blankG (x : γ) : (blankG x).Realize v ↔ Lax564036.AlternatingMachines.ATMBlank (k := 2) (v x) := by
  rw [blankG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_rightG (x : γ) : (rightG x).Realize v ↔ Lax564036.AlternatingMachines.ATMRight (k := 2) (v x) := by
  rw [rightG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_blkG (i : Fin 2) (x : γ) :
    (blkG i x).Realize v ↔ RelMap (Lax564036.AlternatingMachines.atmBlk i) ![v x] := by
  rw [blkG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_leG (x y : γ) : (leG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMLe (k := 2) (v x) (v y) := by
  rw [leG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_srcG (x y : γ) : (srcG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMSrc (k := 2) (v x) (v y) := by
  rw [srcG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_readG (x y : γ) : (readG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMRead (k := 2) (v x) (v y) := by
  rw [readG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_dstG (x y : γ) : (dstG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMDst (k := 2) (v x) (v y) := by
  rw [dstG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_writeG (x y : γ) : (writeG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMWrite (k := 2) (v x) (v y) := by
  rw [writeG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_inpG (x y : γ) : (inpG x y).Realize v ↔ Lax564036.AlternatingMachines.ATMInp (k := 2) (v x) (v y) := by
  rw [inpG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl

@[simp]
theorem realize_eqG (x y : γ) : (eqG x y).Realize v ↔ v x = v y := by
  rw [eqG, Formula.realize_equal, Term.realize_var, Term.realize_var]

/-! ### The derived guards -/

/-- `x` is a least position. -/
noncomputable def minPosG (x : γ) : tmaOrd.Formula γ :=
  posnG x ⊓ FirstOrder.Language.Formula.iAlls (Fin 1) ((posnG (Sum.inr 0)).imp (leG (Sum.inl x) (Sum.inr 0)))

/-- `y` is the position immediately above `x`. -/
noncomputable def succPosG (x y : γ) : tmaOrd.Formula γ :=
  posnG x ⊓
      (posnG y ⊓
        (leG x y ⊓
          (FirstOrder.Language.BoundedFormula.not (eqG x y) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 1)
              ((posnG (Sum.inr 0) ⊓ leG (Sum.inl x) (Sum.inr 0) ⊓ leG (Sum.inr 0) (Sum.inl y)).imp
                (eqG (Sum.inr 0) (Sum.inl x) ⊔ eqG (Sum.inr 0) (Sum.inl y))))))

/-- The cell `x` may initially hold the symbol `y`. -/
noncomputable def initTapeG (x y : γ) : tmaOrd.Formula γ :=
  inpG x y ⊔
      FirstOrder.Language.Formula.iAlls (Fin 1) (FirstOrder.Language.BoundedFormula.not (inpG (Sum.inl x) (Sum.inr 0))) ⊓
        blankG y

@[simp]
theorem realize_minPosG (x : γ) :
    (minPosG x).Realize v ↔ Lax904597.Machines.MinPos (Lax564036.AlternatingMachines.ATMLe (k := 2)) (Lax564036.AlternatingMachines.ATMPosn (k := 2)) (v x) := by
  rw [minPosG, Formula.realize_inf]
  simp only [Formula.realize_iAlls, Formula.realize_imp, realize_posnG, realize_leG,
    Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w => h (w 0)⟩

@[simp]
theorem realize_succPosG (x y : γ) :
    (succPosG x y).Realize v ↔ Lax904597.Machines.SuccPos (Lax564036.AlternatingMachines.ATMLe (k := 2)) (Lax564036.AlternatingMachines.ATMPosn (k := 2)) (v x) (v y) := by
  rw [succPosG, Lax904597.Machines.SuccPos]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_sup, realize_posnG, realize_leG, realize_eqG,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hp, hq, hle, hne, hbetw⟩
    exact ⟨hp, hq, hle, hne, fun r hr h1 h2 => hbetw (fun _ => r) ⟨⟨hr, h1⟩, h2⟩⟩
  · rintro ⟨hp, hq, hle, hne, hbetw⟩
    exact ⟨hp, hq, hle, hne, fun w hw => hbetw (w 0) hw.1.1 hw.1.2 hw.2⟩

@[simp]
theorem realize_initTapeG (x y : γ) :
    (initTapeG x y).Realize v ↔ (Lax564036.AlternatingMachines.atmData 2 A).toTMData.InitTape (v x) (v y) := by
  rw [initTapeG, Lax904597.Machines.TMData.InitTape]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, realize_inpG, realize_blankG, Sum.elim_inl, Sum.elim_inr]
  exact or_congr Iff.rfl
    (and_congr ⟨fun h b => h fun _ => b, fun h w => h (w 0)⟩ Iff.rfl)

end Guards

/-! ### The two promises, as sentences -/

/-- The machine's order is linear. -/
noncomputable def isLinOrdS : tmaOrd.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (leG (Sum.inr 0) (Sum.inr 0)) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 2)).imp (leG (Sum.inr 0) (Sum.inr 2))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 2)
            ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 0)).imp (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2) (leG (Sum.inr 0) (Sum.inr 1) ⊔ leG (Sum.inr 1) (Sum.inr 0))))

/-- **Well-formedness**, as a sentence: the order is linear, there is a
position, the input is functional, and there is exactly one blank. -/
noncomputable def wfS : tmaOrd.Sentence :=
  isLinOrdS ⊓
      (FirstOrder.Language.Formula.iExs (Fin 1) (posnG (Sum.inr 0)) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 3)
            ((inpG (Sum.inr 0) (Sum.inr 1) ⊓ inpG (Sum.inr 0) (Sum.inr 2)).imp (eqG (Sum.inr 1) (Sum.inr 2))) ⊓
          (FirstOrder.Language.Formula.iExs (Fin 1) (blankG (Sum.inr 0)) ⊓
            FirstOrder.Language.Formula.iAlls (Fin 2)
              ((blankG (Sum.inr 0) ⊓ blankG (Sum.inr 1)).imp (eqG (Sum.inr 0) (Sum.inr 1))))))

/-- **The two marks split the states**, as a sentence: every state carries one
of them and not both. -/
noncomputable def blocksSplitS : tmaOrd.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (((blkG 0) (Sum.inr 0) ⊔ (blkG 1) (Sum.inr 0)) ⊓
        FirstOrder.Language.BoundedFormula.not ((blkG 0) (Sum.inr 0) ⊓ (blkG 1) (Sum.inr 0)))

section PromiseRealize

variable {A : Type} [(Lax564036.AlternatingMachines.turingAlt 2).Structure A] [LinearOrder A]

theorem realize_isLinOrdS : (A ⊨ isLinOrdS) ↔ Lax904597.Machines.IsLinOrd (Lax564036.AlternatingMachines.ATMLe (k := 2) (A := A)) := by
  rw [isLinOrdS, Lax904597.Machines.IsLinOrd, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, realize_leG, realize_eqG, Sum.elim_inr]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
  · exact ⟨fun h a b c hab hbc => h ![a, b, c] ⟨hab, hbc⟩,
      fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
  · exact ⟨fun h a b hab hba => h ![a, b] ⟨hab, hba⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
  · exact ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩

theorem realize_wfS : (A ⊨ wfS) ↔ (Lax564036.AlternatingMachines.atmData 2 A).toTMData.WellFormed := by
  rw [wfS, Lax904597.Machines.TMData.WellFormed, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, realize_inpG, realize_blankG, realize_posnG, realize_eqG,
    Sum.elim_inr]
  refine and_congr realize_isLinOrdS (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩
  · exact ⟨fun h p a b h1 h2 => h ![p, a, b] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
  · exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
  · exact ⟨fun h a b ha hb => h ![a, b] ⟨ha, hb⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩

/-- The two marks split the states exactly when every state carries one and not
both: a mark index of `2` or more marks nothing, so the uniqueness clause of
`DescriptiveComplexity.ATMData.BlocksSplit` only speaks about `0` and `1`. -/
theorem realize_blocksSplitS : (A ⊨ blocksSplitS) ↔ (Lax564036.AlternatingMachines.atmData 2 A).BlocksSplit := by
  rw [blocksSplitS, Sentence.Realize]
  simp only [Formula.realize_iAlls, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, realize_blkG, Sum.elim_inr]
  constructor
  · intro h q
    obtain ⟨hone, hnot⟩ := h fun _ => q
    have hblk : ∀ (j : ℕ) (hj : j < 2), (Lax564036.AlternatingMachines.atmData 2 A).Blk j q ↔ RelMap (Lax564036.AlternatingMachines.atmBlk ⟨j, hj⟩) ![q] :=
      fun j hj => ⟨fun ⟨h', hb⟩ => by rwa [Subsingleton.elim h' hj] at hb, fun hb => ⟨hj, hb⟩⟩
    rcases hone with h0 | h1
    · refine ⟨0, by omega, (hblk 0 (by omega)).mpr h0, fun j' hj' => ?_⟩
      obtain ⟨hj2, hb⟩ := hj'
      have : j' = 0 ∨ j' = 1 := by omega
      rcases this with rfl | rfl
      · rfl
      · exact absurd ⟨h0, (hblk 1 (by omega)).mp ⟨hj2, hb⟩⟩ hnot
    · refine ⟨1, by omega, (hblk 1 (by omega)).mpr h1, fun j' hj' => ?_⟩
      obtain ⟨hj2, hb⟩ := hj'
      have : j' = 0 ∨ j' = 1 := by omega
      rcases this with rfl | rfl
      · exact absurd ⟨(hblk 0 (by omega)).mp ⟨hj2, hb⟩, h1⟩ hnot
      · rfl
  · intro h w
    obtain ⟨j, hj2, hj, huniq⟩ := h (w 0)
    have hj01 : j = 0 ∨ j = 1 := by omega
    constructor
    · rcases hj01 with rfl | rfl
      · exact Or.inl hj.2
      · exact Or.inr hj.2
    · rintro ⟨h0, h1⟩
      have e0 : (0 : ℕ) = j := huniq 0 ⟨by omega, h0⟩
      have e1 : (1 : ℕ) = j := huniq 1 ⟨by omega, h1⟩
      omega

end PromiseRealize

end ATMSpace

end Lax480241Proofs.DescriptiveComplexity


