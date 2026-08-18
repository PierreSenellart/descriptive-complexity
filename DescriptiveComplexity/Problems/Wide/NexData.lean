/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Reduce
import DescriptiveComplexity.Problems.Wide.NexDef

/-!
# The data a clocked reduction runs at

A `DescriptiveComplexity.NexKernel` is an expansion, a block of relation
variables to guess and a first-order sentence to check of the guess. Packed as a
step definition whose steps are never read
(`DescriptiveComplexity.NexKernel.toStepDef`), it is the *same* record a
space-bounded reduction runs at, so everything the source side of that reduction
settles – the relativized expansion, the dimension the payload fits in, the
inventories not reading the dimension – serves here unchanged, and this file
does no more than name it and check the two facts a clocked program asks of its
data.

None of it mentions the program's file, its sweep or its clock: those are
downstream of everything here.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section KerData

variable {L : Language.{0, 0}} [L.IsRelational] (K : NexKernel L)

/-- **The record a clocked reduction runs at**: the kernel's expansion,
relativized so that the emitted formulas can name its points, and packed at a
dimension wide enough for a rule's payload. It is `srcData` at the step
definition the kernel is, so the whole address, control and evaluation layer
above `Draw.Data` reads it with nothing added. -/
noncomputable abbrev kerDt : Data (newLang L) :=
  srcData (relExp K.X) K.toStepDef

/-- **A rule's payload fits the dimension**, at the packed kernel: the
`payload_le` every emitted program carries. -/
theorem kerDt_payload_le :
    Fintype.card ((kerDt K).CtlIx ⊕ (kerDt K).SlotIx) ≤ (kerDt K).dd :=
  srcData_payload_le (relExp K.X) K.toStepDef

/-- **The encoded width is below the dimension**: one coordinate of slack, which
is what a state that carries an encoded point needs. -/
theorem kerDt_dd0_lt : (kerDt K).dd0 < (kerDt K).dd :=
  srcData_dd0_lt (relExp K.X) K.toStepDef

/-- **The block index of the packed kernel is nonempty**: the output pack was
padded by one level, so there is a block for the guess to sweep and a block for
the clock's surplus to be counted against. -/
noncomputable def kerKIx : (kerDt K).KIx :=
  srcKIx (relExp K.X) K.toStepDef

instance : Nonempty (kerDt K).KIx := ⟨kerKIx K⟩

/-- **The semantic packs of the packed kernel's machinery are definable**: the
`VarArgs` obligation a reduction owes for `Reads`, discharged by the same
family the space-bounded reduction uses – a clocked program's tower *is* the
space-bounded one. -/
theorem uVarArgsDef_kerDt (v : (kerDt K).VarIx) :
    Data.UVarArgsDef (dt := kerDt K) (Q := (kerDt K).CtlIx) v
      fun e : Env (newLang L) => (kerDt K).varArgsOf e.zero e.one v :=
  Data.uVarArgsDef_varArgsOf (dt := kerDt K) (boolEnv (newLang L)) v

/-- **The accepting predicate of a clocked program at the packed kernel is
definable**: the phase is decided when the formula is built and the bit it
conjoins is the outermost variable's verdict. -/
theorem uGDefinable_kerAccept {B PE : Type} (p : NexPh B PE) :
    UGDefinable (L := newLang L) (W := (kerDt K).SlotIx)
      fun (e : Env (newLang L)) f _ =>
        p = NexPh.acceptP ∧ ((kerDt K).varArgsOf e.zero e.one none).accBit f :=
  Data.uGDefinable_nexAccept (dt := kerDt K) (uVarArgsDef_kerDt K none) p

end KerData

end Draw

end DescriptiveComplexity
