/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.QuantitativePull
import DescriptiveComplexity.FixedPoint

/-!
# The class FP

**FP** is the class of the *functions* computable in polynomial time. It is a
class of computations more than of counting: nothing in a function of FP has
to count anything. The library sees its natural-number-valued part, a
function from structures to numbers being what
`DescriptiveComplexity.CountingProblem` is, whether or not the number counts
solutions. This is the convention of the paper cited below, which defines FP
as the class of the functions `f : Σ* → ℕ` computable in polynomial time
(its Section 2.2), lists it among the “counting complexity classes”, and notes
that the value of a counting problem need not be a number of solutions.
Functions with other outputs (strings, structures, witnesses of a search
problem) are outside this formalization.

As a class of the library (`DescriptiveComplexity.FP`): the problems definable in
QFO(LFP), the first-order fragment of the quantitative logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive] over a Boolean layer of
least fixed points. That this logic captures FP over ordered structures is
their Theorem 4.4.

The class is closed under ordered parsimonious reductions
(`DescriptiveComplexity.FPDefinable.of_orderedParsimonious`): the least fixed
point pulls back through the interpretation as it does for PTIME
(`DescriptiveComplexity.lfpAssign_pull`), and the quantitative output as
`DescriptiveComplexity.QTerm.pull`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {C : CountingProblem L₁} {D : CountingProblem L₂}

/-- **FP is closed under ordered parsimonious reductions.**
Registered in the Lax archive as
[`Lax366625.FPClosure.FP_mem_of_orderedParsimonious`](https://laxarchive.org/lax-366625/Lax366625.FPClosure.html#s-Lax366625.FPClosure.FP_mem_of_orderedParsimonious). -/
theorem FPDefinable.of_orderedParsimonious (f : C ≤ᵖ[≤] D) (h : FPDefinable D) :
    FPDefinable C := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨⟨d.B.pull f.Tag f.dim, d.k * f.dim,
    HornProgram.pull f.toInterpretation.ordExtend d.rules,
    (d.out.pull (f.toInterpretation.ordExtend.extendSO d.B) Empty.elim).relabel
      fun p : Empty × Fin f.dim => p.1⟩, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [QLFPDef.value, QLFPDef.value, lfpAssign_pull f.toInterpretation.ordExtend d.rules]
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  rw [← lfpAssign_map (f.toInterpretation.ordExtendLEquiv A) d.rules] at e₂
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (lfpAssign d.rules))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (lfpAssign d.rules))
  have hout := QTerm.eval_equiv (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁)
    d.out ((f.toInterpretation.ordExtend.extendSO d.B).liftEnv Empty.elim
      (default : Empty × Fin f.dim → A))
  have hpull := QTerm.eval_pull (f.toInterpretation.ordExtend.extendSO d.B) (A := A) d.out
    Empty.elim (default : Empty × Fin f.dim → A)
  rw [QTerm.value, QTerm.value, QTerm.eval_relabel]
  have h1 : d.out.eval (A := f.toInterpretation.Map A) default =
      d.out.eval (⇑(e₂.comp e₁) ∘ (f.toInterpretation.ordExtend.extendSO d.B).liftEnv
        Empty.elim (default : Empty × Fin f.dim → A)) :=
    congrArg _ (Subsingleton.elim _ _)
  exact h1.trans (hout.trans (hpull.symm.trans (congrArg _ (Subsingleton.elim _ _))))

/-- FP is closed under parsimonious reductions. -/
theorem FPDefinable.of_parsimonious (f : C ≤ᵖ D) (h : FPDefinable D) : FPDefinable C :=
  h.of_orderedParsimonious f.toOrdered

end Closure

/-- **The class FP**, in its natural-number-valued part: the functions from
structures to numbers definable in QFO(LFP), i.e., computable in polynomial
time
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4). It is
closed under parsimonious reductions. -/
noncomputable def FP : CountingClass :=
  .ofMem (fun C => FPDefinable C)
    (fun f h => h.of_orderedParsimonious f)
    (fun h => ⟨fpDefinable_congr h, fpDefinable_congr fun A _ _ => (h A).symm⟩)

variable {L : Language.{0, 0}} [L.IsRelational]

theorem mem_FP_iff (C : CountingProblem L) : C ∈ FP ↔ FPDefinable C :=
  Iff.rfl

/-- The support of a problem of FP is in PTIME.
Registered in the Lax archive as
[`Lax366625.FPAndPTIME.support_mem_PTIME_of_mem_FP`](https://laxarchive.org/lax-366625/Lax366625.FPAndPTIME.html#s-Lax366625.FPAndPTIME.support_mem_PTIME_of_mem_FP). -/
theorem support_mem_PTIME_of_mem_FP {C : CountingProblem L} (h : C ∈ FP) :
    C.support ∈ PTIME :=
  support_mem_PTIME_of_fpDefinable h

/-- **No problem of FP is parsimoniously `#P`-hard, unless `NP ⊆ PTIME`.**
Registered in the Lax archive as
[`Lax366625.FPAndPTIME.NP_subset_PTIME_of_mem_FP_of_parsimoniousHard`](https://laxarchive.org/lax-366625/Lax366625.FPAndPTIME.html#s-Lax366625.FPAndPTIME.NP_subset_PTIME_of_mem_FP_of_parsimoniousHard). -/
theorem NP_subset_PTIME_of_mem_FP_of_parsimoniousHard {C : CountingProblem L} (h : C ∈ FP)
    (hard : SharpP.ParsimoniousHard C) : NP ⊆ PTIME :=
  NP_subset_PTIME_of_parsimoniousHard_of_fpDefinable hard h

end DescriptiveComplexity
