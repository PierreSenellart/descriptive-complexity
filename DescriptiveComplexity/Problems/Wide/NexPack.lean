/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawPack
import DescriptiveComplexity.Exponential.Kernel

/-!
# A kernel, packed as the data of a wide program

The source side of the NEXPTIME reduction, in the record the machine layer is
already written against. A `DescriptiveComplexity.NexKernel` is an expansion, a
block of relation variables to guess and a first-order sentence to check of the
guess; a `DescriptiveComplexity.Draw.Data` is an expansion, a
`DescriptiveComplexity.StepDef` – a block, a step formula per variable, an
output sentence – and the packs and layout the program computes with.

**The kernel is a step definition whose steps are never read.** Put the guessed
block where the fixed-point variables go and the kernel where the output
sentence goes, and the two records are the same record: the tracks a symbol
carries are indexed by the block either way, the atoms of the sentence classify
by `DescriptiveComplexity.Draw.MatAtom` – which reads a *block*, not an
iteration – and `DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` is already
what the output evaluation of a fixed-point program computes. So the whole
address, control and evaluation layer above `Draw.Data` serves a nondeterministic
program with nothing added, and what is new is the program alone: it guesses the
tracks the iteration would have written, then runs the output evaluation once.

The step formulas of a packed kernel are `⊥`, and the only trace they leave is
in the *sizes*: the derived dimensions of
`DescriptiveComplexity.Draw.Data` are maxima over the variables, so each of
them is the kernel's own value or the (vacuous) demand of an unread step,
whichever is larger. A larger inventory costs a wider control and nothing else.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **A kernel as a step definition**: the guessed block, the kernel as the
output sentence, and step formulas that no nondeterministic program reads. -/
def NexKernel.toStepDef (K : NexKernel L) : StepDef (K.X.E.sum Language.order) where
  B := K.B
  step _ := ⊥
  out := K.ker

@[simp]
theorem NexKernel.toStepDef_B (K : NexKernel L) : K.toStepDef.B = K.B := rfl

@[simp]
theorem NexKernel.toStepDef_out (K : NexKernel L) : K.toStepDef.out = K.ker := rfl

namespace Draw

/-- **A kernel packed into a `DescriptiveComplexity.Draw.Data`**: the same
packing as a source's (`DescriptiveComplexity.Draw.Data.ofSource`), at the
step definition the kernel is. -/
noncomputable def Data.ofKernel (K : NexKernel L) {dd : ℕ} (hdd : encDim K.X ≤ dd) :
    Data L :=
  Data.ofSource K.X K.toStepDef hdd

@[simp]
theorem Data.ofKernel_X (K : NexKernel L) {dd : ℕ} (hdd : encDim K.X ≤ dd) :
    (Data.ofKernel K hdd).X = K.X := rfl

@[simp]
theorem Data.ofKernel_d (K : NexKernel L) {dd : ℕ} (hdd : encDim K.X ≤ dd) :
    (Data.ofKernel K hdd).d = K.toStepDef := rfl

@[simp]
theorem Data.ofKernel_dd (K : NexKernel L) {dd : ℕ} (hdd : encDim K.X ≤ dd) :
    (Data.ofKernel K hdd).dd = dd := rfl

/-! ### What a nondeterministic program has to decide

The evaluation the machine performs, stated where it can be read off the record:
the guess of an assignment of the block for which the **gated alternating
prefix** of the output sentence's matrix holds. A fixed-point program computes
one such prefix per stage and one for its output; a nondeterministic one
computes only the second, over tracks it guessed rather than iterated, so the
statement below is `DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` under an
existential and nothing else. -/

section Eval

variable (dt : Data L)
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {zero one : A} [LinearOrder (dt.X.Map A)]

/-- **The guess-and-check reading of the output sentence**: some assignment of
the block satisfies it exactly when some assignment passes the gated prefix of
its matrix. This is the last statement of the source side that mentions no
machine. -/
theorem Data.exists_out_iff_gateMat (hne : zero ≠ one)
    (V : Fin dt.pkOut.n → ((Fin dt.dd → A) → Prop)) :
    (∃ σ : dt.d.B.Assignment (dt.X.Map A),
        @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out) ↔
      ∃ σ : dt.d.B.Assignment (dt.X.Map A),
        altQuantFrom dt.pkOut.pol
          (gateMat (encMap dt.ly zero one) (IsEnc dt.ly zero one) dt.pkOut.pol
            fun w => @BoundedFormula.Realize _ (dt.X.Map A)
              (dt.d.B.structure₁ σ) _ _ dt.pkOut.mat default w)
          0 V :=
  exists_congr fun σ => StepDef.out_iff_gateMat dt.ly hne dt.pkOut σ V

end Eval

/-- **The kernel, read as a packed record's output sentence.** The two sides are
the same proposition: `DescriptiveComplexity.NexKernel.Holds` names the expanded
structure by `DescriptiveComplexity.SOBlock.structure`, and a packed record's
output evaluation names it by `DescriptiveComplexity.SOBlock.structure₁`, which
is that structure summed with the base's. This is what carries the source side
across `DescriptiveComplexity.Draw.Data.exists_out_iff_gateMat`. -/
theorem NexKernel.holds_iff_structure₁ (K : NexKernel L) {M : Type}
    [K.X.E.Structure M] [LinearOrder M] :
    K.Holds M ↔ ∃ σ : K.B.Assignment M,
      @Sentence.Realize _ M
        (@SOBlock.structure₁ (K.X.E.sum Language.order) K.B M
          (sumOrderStructure K.X.E M) σ) K.ker :=
  Iff.rfl

end Draw

end DescriptiveComplexity
