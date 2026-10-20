/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Expansion
import Lax822549Proofs.DescriptiveComplexity.Exponential.Classes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Lax822549Proofs.DescriptiveComplexity.FixedPoint
import Lax822549Proofs.DescriptiveComplexity.Hierarchy
import Lax822549Proofs.DescriptiveComplexity.OrderWalk
import Lax822549Proofs.DescriptiveComplexity.Ordered
import Lax822549Proofs.DescriptiveComplexity.OrderedComposition
import Lax822549Proofs.DescriptiveComplexity.Padding
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Membership
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Program
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Space
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.SpaceHard
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Tape
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax822549Proofs.DescriptiveComplexity.Problems.Qsat.Blocks
import Lax822549Proofs.DescriptiveComplexity.Problems.Qsat.Hardness
import Lax822549Proofs.DescriptiveComplexity.Problems.Qsat.Membership
import Lax822549Proofs.DescriptiveComplexity.Problems.Sat.TseitinFormulas
import Lax822549Proofs.DescriptiveComplexity.SecondOrder
import Lax822549Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax822549Proofs.DescriptiveComplexity.Vocabulary
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Space
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

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wmAcc wmBlank wmDst wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WPoint wideData wpAttr wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (tmData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The wide machines are members of the exponential classes

The payoff of `DescriptiveComplexity.Problems.Wide.Expansion`: the expansion's
points **are** the universe of the wide machine
(`DescriptiveComplexity.Wide.wideEquiv`), so the machine an instance describes
and the machine the expanded structure describes agree fieldwise
(`DescriptiveComplexity.Wide.wideAgree`) and the three wide problems are exactly
the three ordinary machine problems read over the expansion. With
`DescriptiveComplexity.ntmAccept_mem_NP` and
`DescriptiveComplexity.ntmAcceptSpace_mem_PSPACE` that gives

* `DescriptiveComplexity.wideAccept_mem_NEXPTIME` – `NEXPTIME := NP.exp`, so
  this is the definition being exercised;
* `DescriptiveComplexity.wideAcceptSpace_mem_EXPSPACE` and its deterministic
  variant, through `DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`.

No resource argument appears anywhere: the exponent is in the *universe* the
machine runs over, and everything else is the composition that
`DescriptiveComplexity.ExpDefinable` is made of – an expansion applied after the
problem, which is the composition that exists.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Wide

section Embed

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

/-- **The universe of the wide machine sits inside the expansion**: an address
becomes the point tagged `addr` carrying it, a control element the point tagged
`ctrl` carrying its singleton. It is the address expansion's own embedding
(`DescriptiveComplexity.AddrExp.addrEmbed`), at this expansion. -/
noncomputable def wideEmbed : Lax822549.WideMachines.WPoint A → wideExp.Map A := AddrExp.addrEmbed

/-- **The points of the expansion are the universe of the wide machine.** -/
noncomputable def wideEquiv : Lax822549.WideMachines.WPoint A ≃ wideExp.Map A := AddrExp.addrEquiv

@[simp]
theorem wideEquiv_apply (p : Lax822549.WideMachines.WPoint A) : wideEquiv p = wideEmbed p := rfl

@[simp]
theorem wideEmbed_addr_tag (s : A → Prop) :
    (wideEmbed (Sum.inl s) : wideExp.Map A).1.1 = AddrExp.WTag.addr := rfl

@[simp]
theorem wideEmbed_ctrl_tag (x : A) :
    (wideEmbed (Sum.inr x) : wideExp.Map A).1.1 = AddrExp.WTag.ctrl := rfl

end Embed

/-! ### The twelve symbols

Each defining sentence is read at the points the embedding produces, and turns
out to be the corresponding field of `DescriptiveComplexity.wideData`. The two
generic lemmas do the bookkeeping – the tag match and the passage from the
replicated block to one or two stacked copies – once for all. -/

section Symbols

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

/-- Reading a unary symbol of the expanded vocabulary at one point: the address
expansion's own reading (`DescriptiveComplexity.AddrExp.realize_one`), at this
expansion. -/
theorem realize_one (rt : Lax904597.Machines.turing.Relations 1) (φ : AddrExp.WTag → wide1.Sentence)
    (h : ∀ τ : Fin 1 → wideExp.Tag, wideExp.relSentence rt τ = onS1 (φ (τ 0)))
    (x : wideExp.Map A) :
    letI := wideStructure A
    (RelMap rt ![x] ↔
      @Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) x.1.2) (φ x.1.1)) :=
  AddrExp.realize_one rt φ h x

/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : Lax904597.Machines.turing.Relations 2)
    (φ : AddrExp.WTag → AddrExp.WTag → wide2.Sentence)
    (h : ∀ τ : Fin 2 → wideExp.Tag, wideExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : wideExp.Map A) :
    letI := wideStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) x.1.2 y.1.2)
        (φ x.1.1 y.1.1)) :=
  AddrExp.realize_two rt φ h x y

/-- **The positions of the expanded machine are the addresses.** -/
theorem relMap_posn (p : Lax822549.WideMachines.WPoint A) :
    letI := wideStructure A
    (RelMap Lax904597.Machines.tmPosn ![wideEmbed p] ↔ (Lax822549.WideMachines.wideData A).Posn p) := by
  let := wideStructure A
  rw [realize_one Lax904597.Machines.tmPosn posnT (fun _ => rfl) (wideEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_true (realize_topS _) trivial
  | Sum.inr x => exact iff_of_false (not_realize_botS _) (fun h => h)

/-- **A mark of the expanded machine is the corresponding mark of the
instance**, carried by the control elements alone. -/
theorem relMap_mark (rt : Lax904597.Machines.turing.Relations 1) (r : Lax822549.WideMachines.wide.Relations 1)
    (h : ∀ τ : Fin 1 → wideExp.Tag, wideExp.relSentence rt τ = onS1 (markT r (τ 0)))
    (p : Lax822549.WideMachines.WPoint A) :
    letI := wideStructure A
    (RelMap rt ![wideEmbed p] ↔ Lax822549.WideMachines.wpMark (fun x => RelMap r ![x]) p) := by
  let := wideStructure A
  rw [realize_one rt (markT r) h (wideEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_false (not_realize_botS _) (fun h => h)
  | Sum.inr x =>
    refine (realize_markS r _).trans ?_
    exact ⟨fun ⟨z, hz, hr⟩ => hz ▸ hr, fun hr => ⟨x, rfl, hr⟩⟩

/-- **A binary attribute of the expanded machine is the corresponding attribute
of the instance**, holding of control elements alone. -/
theorem relMap_attr (rt : Lax904597.Machines.turing.Relations 2) (r : Lax822549.WideMachines.wide.Relations 2)
    (h : ∀ τ : Fin 2 → wideExp.Tag, wideExp.relSentence rt τ = onS2 (binT r (τ 0) (τ 1)))
    (p q : Lax822549.WideMachines.WPoint A) :
    letI := wideStructure A
    (RelMap rt ![wideEmbed p, wideEmbed q] ↔ Lax822549.WideMachines.wpAttr (fun x y => RelMap r ![x, y]) p q) := by
  let := wideStructure A
  rw [realize_two rt (binT r) h (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS r _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The order of the expanded machine**: addresses in the binary-number order
the instance's own order induces, then the control elements in that order. -/
theorem relMap_le (p q : Lax822549.WideMachines.WPoint A) :
    letI := wideStructure A
    (RelMap Lax904597.Machines.tmLe ![wideEmbed p, wideEmbed q] ↔ (Lax822549.WideMachines.wideData A).Le p q) := by
  let := wideStructure A
  rw [realize_two Lax904597.Machines.tmLe leT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact realize_addrLeS _ _
  | Sum.inl s, Sum.inr y => exact iff_of_true (realize_topS₂ _ _) trivial
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS Lax822549.WideMachines.wmLe _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The initial tape of the expanded machine**: the address cutting the
initial segment of an element holds that element's input symbol. -/
theorem relMap_inp (p q : Lax822549.WideMachines.WPoint A) :
    letI := wideStructure A
    (RelMap Lax904597.Machines.tmInp ![wideEmbed p, wideEmbed q] ↔ (Lax822549.WideMachines.wideData A).Inp p q) := by
  let := wideStructure A
  rw [realize_two Lax904597.Machines.tmInp inpT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_inpS _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)

end Symbols

/-! ### The two machines agree -/

section Agree

variable (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

/-- **The wide machine of the instance is the ordinary machine of the
expansion**, fieldwise along `DescriptiveComplexity.Wide.wideEquiv`. -/
theorem wideAgree :
    letI := wideStructure A
    TMData.Agree (wideEquiv (A := A)) (Lax822549.WideMachines.wideData A) (Lax904597.Machines.tmData (wideExp.Map A)) := by
  let := wideStructure A
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
    fun p q => (relMap_inp p q).symm⟩

end Agree

end Wide

/-! ### The memberships -/

section Membership

open Wide

/-- **The wide machine is the ordinary machine of the expansion**: acceptance of
the one is acceptance of the other. -/
theorem wideAccept_iff_expansion (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (WideAccept A ↔ NTMAccept (wideExp.Map A)) := by
  let := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed h.accepts

/-- The space-bounded version of `DescriptiveComplexity.wideAccept_iff_expansion`. -/
theorem wideAcceptSpace_iff_expansion (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (WideAcceptSpace A ↔ NTMAcceptSpace (wideExp.Map A)) := by
  let := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed h.acceptsSpace

/-- The deterministic space-bounded version of
`DescriptiveComplexity.wideAccept_iff_expansion`. -/
theorem dwideAcceptSpace_iff_expansion (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (DWideAcceptSpace A ↔ DTMAcceptSpace (wideExp.Map A)) := by
  let := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)

/-- **The wide machine is in NEXPTIME**, which is `NP.exp`: the expansion turns
it into `DescriptiveComplexity.NTMAccept`, and that problem is in NP. This is
the first natural member the class has. -/
theorem wideAccept_mem_NEXPTIME : WideAccept ∈ NEXPTIME := by
  let hinst : ∀ (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A],
      Lax904597.Machines.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  refine ⟨wideExp, NTMAccept, ntmAccept_mem_NP, ?_⟩
  intro A _ _ _ _
  exact wideAccept_iff_expansion A

/-- **The space-bounded wide machine is in EXPSPACE**: the expansion turns it
into `DescriptiveComplexity.NTMAcceptSpace`, and that problem is in PSPACE. -/
theorem wideAcceptSpace_mem_EXPSPACE : WideAcceptSpace ∈ EXPSPACE := by
  let hinst : ∀ (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A],
      Lax904597.Machines.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wideExp, NTMAcceptSpace, ntmAcceptSpace_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact wideAcceptSpace_iff_expansion A

/-- **The deterministic space-bounded wide machine is in EXPSPACE**, through
`DescriptiveComplexity.DTMAcceptSpace`. -/
theorem dwideAcceptSpace_mem_EXPSPACE : DWideAcceptSpace ∈ EXPSPACE := by
  let hinst : ∀ (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A],
      Lax904597.Machines.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wideExp, DTMAcceptSpace, dtmAcceptSpace_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact dwideAcceptSpace_iff_expansion A

end Membership

end Lax822549Proofs.DescriptiveComplexity


