/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Defs
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax822549Proofs.DescriptiveComplexity.Exponential.Copies
import Lax822549Proofs.DescriptiveComplexity.Exponential.Expansion
import Lax822549Proofs.DescriptiveComplexity.Exponential.AddrExp
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

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace FirstOrder.Language
export Lax822549.WideMachines (wide wmAcc wmBlank wmDst wmInp wmLe wmRead wmRight wmSrc wmStart wmTr wmWrite)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (turing)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMDown WMInp WMLe WMSetLe)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The wide machine as an exponential expansion

The construction that makes the wide machine a *member* of an exponential class:
an `DescriptiveComplexity.ExpExpansion` of `FirstOrder.Language.wide`-structures
whose expanded vocabulary is `FirstOrder.Language.turing`. Read on an instance
`A`, it produces exactly the ordinary machine instance whose universe is
`DescriptiveComplexity.WPoint A` – so a wide machine *is* an ordinary machine,
one exponential up, and nothing has to be said about resources.

Three things fix the whole design.

* **The block is one unary relation variable** (`addrBlock`), so an assignment
  *is* a subset of the instance and the expanded universe is its power set.
  There is no padding to worry about, and the binary-number order on addresses
  can be written directly rather than through
  `DescriptiveComplexity.SOBlock.ordLeF`, which would compare padded atoms
  against the *ambient* order rather than against the instance's own.
* **Two tags** (`DescriptiveComplexity.AddrExp.WTag`): `addr`, whose domain
  sentence is `⊤`, so those points are all the addresses; and `ctrl`, whose
  domain sentence says the variable is a **singleton**, so those points are the
  elements of the instance. This is the standard way of keeping the base
  universe visible inside an expanded one.
* **Every defining sentence is a static choice on the tags** followed by one of
  five sentences: a mark of the control (`markS`), a binary attribute of it
  (`binS`), the singleton condition (`singleS`), the order on addresses
  (`addrLeS`) and the initial tape (`inpS`). Every quantifier in them ranges
  over the **base** – an element, never an address – which is exactly what
  keeps them first-order there.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Wide

/-! ### The vocabularies, the block and the sentences

All of it is the address expansion's (`DescriptiveComplexity.AddrExp`), written
once for an arbitrary base vocabulary with an order symbol; what is here is the
naming at `FirstOrder.Language.wide` and the two sentences that read *its* order
and *its* input relation. -/

/-- The ordered vocabulary of wide-machine instances: what an expansion's
sentences may read besides the block. -/
abbrev wOrd : Language.{0, 0} := AddrExp.aeOrd Lax822549.WideMachines.wide

/-- **The block whose assignments are the addresses**: a single unary relation
variable, so an assignment is a subset of the instance. -/
abbrev addrBlock : Lax904597.SecondOrder.SOBlock := AddrExp.addrBlock

/-- The base vocabulary expanded by one copy of the block. -/
abbrev wide1 : Language.{0, 0} := AddrExp.aeLang1 Lax822549.WideMachines.wide

/-- The base vocabulary expanded by two copies of the block. -/
abbrev wide2 : Language.{0, 0} := AddrExp.aeLang2 Lax822549.WideMachines.wide

/-- **The address an assignment is**: the elements its relation variable
holds of. -/
abbrev wbits {A : Type} (ρ : addrBlock.Assignment A) : A → Prop := AddrExp.aeBits ρ

export AddrExp (bit1 bitA bitB apply₁ aeBits_aeAssign aeAssign_aeBits 
  markG attrG eqG bit1F bitAF bitBF lift1 lift2 markS binS singleS WMSingle
  exists_eq_of_wmSingle wmSingle_eq realize_markG realize_attrG realize_eqG
  realize_bit1F realize_bitAF realize_bitBF realize_lift1 realize_lift2
  realize_topS not_realize_botS realize_topS₂ not_realize_botS₂
  realize_markS realize_binS realize_singleS)

section Wide

variable {γ : Type}

/-- **The order on addresses**: the two addresses agree, or, at some element the
first is out of and the second in, they agree at every strictly smaller
element. -/
noncomputable def addrLeS : wide2.Sentence := AddrExp.addrLeS Lax822549.WideMachines.wmLe

/-- **The initial tape**: the first address is the initial segment cut by some
element `x`, the second point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpS : wide2.Sentence := AddrExp.inpS Lax822549.WideMachines.wmLe Lax822549.WideMachines.wmInp

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

theorem realize_addrLeS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) addrLeS ↔
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (wbits ρ) (wbits σ)) :=
  AddrExp.realize_addrLeS Lax822549.WideMachines.wmLe ρ σ

theorem realize_inpS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) inpS ↔
      ∃ x y, Lax822549.WideMachines.WMDown Lax822549.WideMachines.WMLe (wbits ρ) x ∧ wbits σ y ∧ Lax822549.WideMachines.WMInp x y) :=
  AddrExp.realize_inpS Lax822549.WideMachines.wmLe Lax822549.WideMachines.wmInp ρ σ

end Wide

/-! ### The tags, and the defining sentences -/

export AddrExp (WTag domT onS1 onS2 realize_onS1 realize_onS2 addrEmbed addrEquiv
  addrEmbed_bijective addrEmbed_addr_tag addrEmbed_ctrl_tag addrEquiv_apply
  addrStructure)

/-- Being a position: the addresses are the positions. -/
noncomputable def posnT : WTag → wide1.Sentence
  | .addr => ⊤
  | .ctrl => ⊥

/-- A mark of the control, at a tag: only control elements carry it. -/
noncomputable def markT (r : Lax822549.WideMachines.wide.Relations 1) : WTag → wide1.Sentence
  | .addr => ⊥
  | .ctrl => markS r

/-- A binary attribute of the control, at a pair of tags. -/
noncomputable def binT (r : Lax822549.WideMachines.wide.Relations 2) : WTag → WTag → wide2.Sentence
  | .ctrl, .ctrl => binS r
  | _, _ => ⊥

/-- The order of the machine, at a pair of tags: the addresses come first, in
the binary-number order, then the control elements in the instance's order. -/
noncomputable def leT : WTag → WTag → wide2.Sentence
  | .addr, .addr => addrLeS
  | .addr, .ctrl => ⊤
  | .ctrl, .addr => ⊥
  | .ctrl, .ctrl => binS Lax822549.WideMachines.wmLe

/-- The initial tape, at a pair of tags: an address holds a symbol. -/
noncomputable def inpT : WTag → WTag → wide2.Sentence
  | .addr, .ctrl => inpS
  | _, _ => ⊥

/-- **The expansion of a wide-machine instance**: the address expansion
(`DescriptiveComplexity.AddrExp.addrExp`) at the vocabulary of ordinary
machines, every symbol of which is defined by a static choice on the tags
followed by one of the five sentences. -/
noncomputable def wideExp : Lax480241.Expansions.ExpExpansion Lax822549.WideMachines.wide :=
  AddrExp.addrExp Lax822549.WideMachines.wide Lax904597.Machines.turing fun {n} r τ =>
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
    | _, .inp => onS2 (inpT (τ 0) (τ 1))

section Structure

variable (A : Type) [Lax822549.WideMachines.wide.Structure A] [LinearOrder A]

/-- The expanded structure of `DescriptiveComplexity.wideExp`, at the
vocabulary of machines – equal to the expansion's own by definition, but not
syntactically, so instance search has to be handed it. -/
@[instance_reducible]
noncomputable def wideStructure : Lax904597.Machines.turing.Structure (wideExp.Map A) :=
  AddrExp.addrStructure (L := Lax822549.WideMachines.wide) A

end Structure

end Wide

end Lax822549Proofs.DescriptiveComplexity


