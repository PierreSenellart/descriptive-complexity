/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Expansion
import DescriptiveComplexity.Exponential.AddrExp

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

namespace DescriptiveComplexity

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
abbrev wOrd : Language.{0, 0} := AddrExp.aeOrd Language.wide

/-- **The block whose assignments are the addresses**: a single unary relation
variable, so an assignment is a subset of the instance. -/
abbrev addrBlock : SOBlock := AddrExp.addrBlock

/-- The base vocabulary expanded by one copy of the block. -/
abbrev wide1 : Language.{0, 0} := AddrExp.aeLang1 Language.wide

/-- The base vocabulary expanded by two copies of the block. -/
abbrev wide2 : Language.{0, 0} := AddrExp.aeLang2 Language.wide

/-- **The address an assignment is**: the elements its relation variable
holds of. -/
abbrev wbits {A : Type} (ρ : addrBlock.Assignment A) : A → Prop := AddrExp.aeBits ρ

export AddrExp (bit1 bitA bitB apply₁ aeBits_aeAssign aeAssign_aeBits aeAssign_injective
  markG attrG eqG bit1F bitAF bitBF lift1 lift2 markS binS singleS WMSingle
  exists_eq_of_wmSingle wmSingle_eq realize_markG realize_attrG realize_eqG
  realize_bit1F realize_bitAF realize_bitBF realize_lift1 realize_lift2
  realize_topS not_realize_botS realize_topS₂ not_realize_botS₂
  realize_markS realize_binS realize_singleS)

section Wide

variable {γ : Type}

/-- `x` is strictly below `y` in the instance's own order. -/
noncomputable def ltG (x y : γ) : wOrd.Formula γ := AddrExp.ltG wmLe x y

/-- **The order on addresses**: the two addresses agree, or, at some element the
first is out of and the second in, they agree at every strictly smaller
element. -/
noncomputable def addrLeS : wide2.Sentence := AddrExp.addrLeS wmLe

/-- **The initial tape**: the first address is the initial segment cut by some
element `x`, the second point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpS : wide2.Sentence := AddrExp.inpS wmLe wmInp

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]

@[simp]
theorem realize_ltG {v : γ → A} (x y : γ) :
    (ltG x y).Realize v ↔ (WMLe (v x) (v y) ∧ ¬WMLe (v y) (v x)) :=
  AddrExp.realize_ltG wmLe x y

theorem realize_addrLeS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) addrLeS ↔
      WMSetLe WMLe (wbits ρ) (wbits σ)) :=
  AddrExp.realize_addrLeS wmLe ρ σ

theorem realize_inpS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) inpS ↔
      ∃ x y, WMDown WMLe (wbits ρ) x ∧ wbits σ y ∧ WMInp x y) :=
  AddrExp.realize_inpS wmLe wmInp ρ σ

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
noncomputable def markT (r : Language.wide.Relations 1) : WTag → wide1.Sentence
  | .addr => ⊥
  | .ctrl => markS r

/-- A binary attribute of the control, at a pair of tags. -/
noncomputable def binT (r : Language.wide.Relations 2) : WTag → WTag → wide2.Sentence
  | .ctrl, .ctrl => binS r
  | _, _ => ⊥

/-- The order of the machine, at a pair of tags: the addresses come first, in
the binary-number order, then the control elements in the instance's order. -/
noncomputable def leT : WTag → WTag → wide2.Sentence
  | .addr, .addr => addrLeS
  | .addr, .ctrl => ⊤
  | .ctrl, .addr => ⊥
  | .ctrl, .ctrl => binS wmLe

/-- The initial tape, at a pair of tags: an address holds a symbol. -/
noncomputable def inpT : WTag → WTag → wide2.Sentence
  | .addr, .ctrl => inpS
  | _, _ => ⊥

/-- **The expansion of a wide-machine instance**: the address expansion
(`DescriptiveComplexity.AddrExp.addrExp`) at the vocabulary of ordinary
machines, every symbol of which is defined by a static choice on the tags
followed by one of the five sentences. -/
noncomputable def wideExp : ExpExpansion Language.wide :=
  AddrExp.addrExp Language.wide Language.turing fun {n} r τ =>
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tr => onS1 (markT wmTr (τ 0))
    | _, .start => onS1 (markT wmStart (τ 0))
    | _, .acc => onS1 (markT wmAcc (τ 0))
    | _, .blank => onS1 (markT wmBlank (τ 0))
    | _, .right => onS1 (markT wmRight (τ 0))
    | _, .le => onS2 (leT (τ 0) (τ 1))
    | _, .tsrc => onS2 (binT wmSrc (τ 0) (τ 1))
    | _, .tread => onS2 (binT wmRead (τ 0) (τ 1))
    | _, .tdst => onS2 (binT wmDst (τ 0) (τ 1))
    | _, .twrite => onS2 (binT wmWrite (τ 0) (τ 1))
    | _, .inp => onS2 (inpT (τ 0) (τ 1))

section Structure

variable (A : Type) [Language.wide.Structure A] [LinearOrder A]

/-- The expanded structure of `DescriptiveComplexity.wideExp`, at the
vocabulary of machines – equal to the expansion's own by definition, but not
syntactically, so instance search has to be handed it. -/
@[instance_reducible]
noncomputable def wideStructure : Language.turing.Structure (wideExp.Map A) :=
  AddrExp.addrStructure (L := Language.wide) A

end Structure

end Wide

end DescriptiveComplexity
