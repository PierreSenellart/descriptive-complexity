/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannel
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Membership
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

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideRegChannel
end Lax822549.WideRegChannel

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wmAcc wmBlank wmDst wmInp wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMHasInp WMInp WMRegSeg WPoint)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideRegChannel (wideRegData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (tmData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The register channel, as an expansion

`DescriptiveComplexity.WideAccept` is in NEXPTIME because the wide machine of an
instance *is* the ordinary machine of an exponential expansion of it
(`DescriptiveComplexity.Problems.Wide.Membership`): twelve relation symbols,
each defined by a sentence over one or two copies of the address block. The
register channel changes exactly one of the twelve – the input – so this file
adds the sentence it needs, the expansion it names, and the membership that
follows.

The sentence is the segment channel's with one conjunct added: the segment
channel says «the address holds `z` exactly when `z ≤ x`», the register channel
says «exactly when `z ≤ x` *and* `z` carries an input symbol». Carrying one is
itself first-order (`hasInpG`), so the expansion stays what it was, and the two
expansions have the same tags, the same block and the same domain, hence the
same universe.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Wide

/-! ### The sentence the register channel needs -/

section Guard

variable {γ : Type}

/-- **An element the channel writes for**, as a guard: it carries an input
symbol. -/
noncomputable def hasInpG (x : γ) : wOrd.Formula γ :=
  Formula.iExs (Fin 1) (attrG Lax822549.WideMachines.wmInp (Sum.inl x) (Sum.inr 0))

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_hasInpG (x : γ) : (hasInpG x).Realize v ↔ Lax822549.WideMachines.WMHasInp (v x) := by
  rw [hasInpG]
  simp only [Formula.realize_iExs, realize_attrG, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩

end Guard

/-- **The initial tape at the register channel**: the first address is the
segment some element `x` cuts among the elements that carry input, the second
point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpRegS : wide2.Sentence :=
  Formula.iExs (Fin 2)
    (Formula.iAlls (Fin 1)
        (bitAF (Sum.inr 0) ⇔ lift2 (attrG Lax822549.WideMachines.wmLe (Sum.inr 0) (Sum.inl (Sum.inr 0)) ⊓
          hasInpG (Sum.inr 0))) ⊓
      (bitBF (Sum.inr 1) ⊓ lift2 (attrG Lax822549.WideMachines.wmInp (Sum.inr 0) (Sum.inr 1))))

section Realize

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

theorem realize_inpRegS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) inpRegS ↔
      ∃ x y, Lax822549.WideMachines.WMRegSeg (wbits ρ) x ∧ wbits σ y ∧ Lax822549.WideMachines.WMInp x y) := by
  let := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [inpRegS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_iff, realize_bitAF, realize_bitBF, realize_lift2, realize_attrG,
    realize_hasInpG, Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun ⟨w, hd, hb, hi⟩ => ⟨w 0, w 1, fun y => hd fun _ => y, hb, hi⟩,
    fun ⟨x, y, hd, hb, hi⟩ => ⟨![x, y], fun w => hd (w 0), hb, hi⟩⟩

end Realize

/-! ### The expansion, and the structure it puts on the same universe -/

/-- The initial tape of the register channel, at a pair of tags. -/
noncomputable def inpRegT : WTag → WTag → wide2.Sentence
  | .addr, .ctrl => inpRegS
  | _, _ => ⊥

/-- **The expansion of a wide-machine instance at the register channel**: the
tags, the block, the domain and eleven of the twelve symbols are
`DescriptiveComplexity.wideExp`'s; the input is the register channel's. -/
noncomputable def wideRegExp : Lax480241.Expansions.ExpExpansion Lax822549.WideMachines.wide where
  Tag := WTag
  B := addrBlock
  E := Lax904597.Machines.turing
  dom := domT
  relSentence {n} r τ :=
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tr => onS1 (markT Lax822549.WideMachines.wmTr (τ 0))
    | _, .start => onS1 (markT Lax822549.WideMachines.wmStart (τ 0))
    | _, .acc => onS1 (markT Lax822549.WideMachines.wmAcc (τ 0))
    | _, .blank => onS1 (markT Lax822549.WideMachines.wmBlank (τ 0))
    | _, .right => onS1 (markT Lax822549.WideMachines.wmRight (τ 0))
    | _, .le => onS2 (leT (τ 0) (τ 1))
    | _, .tsrc => onS2 (binT Lax822549.WideMachines.wmSrc (τ 0) (τ 1))
    | _, .tread => onS2 (binT Lax822549.WideMachines.wmRead (τ 0) (τ 1))
    | _, .tdst => onS2 (binT Lax822549.WideMachines.wmDst (τ 0) (τ 1))
    | _, .twrite => onS2 (binT Lax822549.WideMachines.wmWrite (τ 0) (τ 1))
    | _, .inp => onS2 (inpRegT (τ 0) (τ 1))
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨.addr, addrBlock.botAssign A, ?_⟩
    let := addrBlock.structure₁ (L := wOrd) (addrBlock.botAssign A)
    exact Formula.realize_top.mpr trivial

section Structure

variable (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

/-- The expanded structure at the register channel. Its universe is `wideExp`'s
– the two expansions differ in one defining sentence and in nothing that decides
the points. -/
@[instance_reducible]
noncomputable def wideRegStructure : Lax904597.Machines.turing.Structure (wideExp.Map A) :=
  wideRegExp.mapStructure A

variable {A}

/-- Reading a binary symbol of the register-channel expansion at two points. -/
theorem realize_twoReg (rt : Lax904597.Machines.turing.Relations 2) (φ : WTag → WTag → wide2.Sentence)
    (h : ∀ τ : Fin 2 → wideRegExp.Tag, wideRegExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : wideExp.Map A) :
    letI := wideRegStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) x.1.2 y.1.2)
        (φ x.1.1 y.1.1)) := by
  let := wideRegStructure A
  have h1 := wideRegExp.relMap_map rt ![x, y]
  rw [h] at h1
  exact h1.trans (realize_onS2 _ x y)

/-- **The initial tape of the expanded machine at the register channel**: the
segment an element cuts among the elements that carry input holds that element's
input symbol. -/
theorem relMap_inpReg (p q : Lax822549.WideMachines.WPoint A) :
    letI := wideRegStructure A
    (RelMap Lax904597.Machines.tmInp ![wideEmbed p, wideEmbed q] ↔ (Lax822549.WideRegChannel.wideRegData A).Inp p q) := by
  let := wideRegStructure A
  rw [realize_twoReg Lax904597.Machines.tmInp inpRegT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_inpRegS _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)

variable (A)

/-- **The wide machine at the register channel is the ordinary machine of the
register-channel expansion**, fieldwise: eleven of the twelve symbols are
defined by the same sentences as `wideExp`'s, so their readings are the same
readings, and the twelfth is `relMap_inpReg`. -/
theorem wideRegAgree :
    letI := wideRegStructure A
    TMData.Agree (wideEquiv (A := A)) (Lax822549.WideRegChannel.wideRegData A) (Lax904597.Machines.tmData (wideExp.Map A)) := by
  let := wideRegStructure A
  exact ⟨fun p => (relMap_posn p).symm, fun p q => (relMap_le p q).symm,
    fun p => (relMap_mark Lax904597.Machines.tmTr Lax822549.WideMachines.wmTr (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax904597.Machines.tmStart Lax822549.WideMachines.wmStart (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax904597.Machines.tmAcc Lax822549.WideMachines.wmAcc (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax904597.Machines.tmBlank Lax822549.WideMachines.wmBlank (fun _ => rfl) p).symm,
    fun p => (relMap_mark Lax904597.Machines.tmRight Lax822549.WideMachines.wmRight (fun _ => rfl) p).symm,
    fun p q => (relMap_attr Lax904597.Machines.tmSrc Lax822549.WideMachines.wmSrc (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr Lax904597.Machines.tmRead Lax822549.WideMachines.wmRead (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr Lax904597.Machines.tmDst Lax822549.WideMachines.wmDst (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr Lax904597.Machines.tmWrite Lax822549.WideMachines.wmWrite (fun _ => rfl) p q).symm,
    fun p q => (relMap_inpReg p q).symm⟩

end Structure

end Wide

/-! ### The membership -/

section Membership

open Wide

/-- **The register-channel machine is the ordinary machine of its expansion**:
acceptance of the one is acceptance of the other. -/
theorem wideRegAccept_iff_expansion (A : Type) [Lax822549.WideMachines.wide.Structure A]
    [LinearOrder A] :
    letI := wideRegStructure A
    (WideRegAccept A ↔ NTMAccept (wideExp.Map A)) := by
  let := wideRegStructure A
  have h := wideRegAgree A
  exact and_congr h.wellFormed h.accepts

/-- **The register-channel machine is in NEXPTIME**, for the reason
`DescriptiveComplexity.wideAccept_mem_NEXPTIME` gives: its expansion is an
ordinary machine, and `DescriptiveComplexity.NTMAccept` is in NP. The two
problems are therefore in the same class, and a reduction may choose whichever
channel puts its input where it can reach it. -/
theorem wideRegAccept_mem_NEXPTIME : WideRegAccept ∈ NEXPTIME := by
  let hinst : ∀ (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A],
      Lax904597.Machines.turing.Structure (wideExp.Map A) := fun A => wideRegStructure A
  refine ⟨wideRegExp, NTMAccept, ntmAccept_mem_NP, ?_⟩
  intro A _ _ _ _
  exact wideRegAccept_iff_expansion A

end Membership

end Lax822549Proofs.DescriptiveComplexity


