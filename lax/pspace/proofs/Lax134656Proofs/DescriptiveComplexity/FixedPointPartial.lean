/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity.IFPDefinable
end Lax134656Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree
end Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity.PFPDefinable
end Lax134656Proofs.DescriptiveComplexity.PFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity.PFPDefinableFree
end Lax134656Proofs.DescriptiveComplexity.PFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity.StepDef
end Lax134656Proofs.DescriptiveComplexity.StepDef

namespace Lax134656Proofs.DescriptiveComplexity.StepDef.PFPHolds
end Lax134656Proofs.DescriptiveComplexity.StepDef.PFPHolds

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (IFPDefinableFree PFPDefinable PFPDefinableFree)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# FO(PFP): first-order logic with a partial fixed point

The partial fixed-point logic ([Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` by *replacement* – each stage is
one application of the step formulas to the previous one – and read the
output at the first stable stage, if the iteration stabilizes at all.

## The divergence convention

`DescriptiveComplexity.StepDef.PFPHolds` requires convergence: a diverging
iteration makes the definition *false*, whatever the output sentence. The
textbook semantics instead assigns a diverging iteration the empty relations
and reads the output there; the two readings are compared precisely by
`DescriptiveComplexity.StepDef.realize_pfpValue_iff` – they agree unless the
iteration diverges *and* the output holds at the empty assignment. The
convergence-requiring convention is chosen deliberately:

* it is what makes the translation to SO(TC) direct
  (`DescriptiveComplexity.FixedPointPartialSpace`): acceptance of the walk
  *is* «some stable stage satisfying the output is reachable», with no
  divergence detection – on unordered structures, none is available;
* every definition in the textbook semantics whose output fails on the empty
  assignment means the same thing here, and conversely a definition of this
  file is read in the textbook semantics by guarding its output with «the
  state is a fixed point of the step» – the guard is first-order
  (`DescriptiveComplexity.StepDef.isFixedPtF` in
  `DescriptiveComplexity.FixedPointPartialSpace`), and it fails at the empty
  assignment of a diverging iteration, since a diverging iteration's empty
  *start* is not a fixed point.

As for IFP, there is an ordered notion (`DescriptiveComplexity.PFPDefinable`,
the setting of the capture theorem FO(≤, PFP) = PSPACE) and an order-free one
(`DescriptiveComplexity.PFPDefinableFree`, the right-hand side of the
Abiteboul–Vianu theorem), and the two must not be conflated.

## Inflation is a special case

`DescriptiveComplexity.StepDef.inflate` disjoins each variable's own atom
onto its step formula, making the *partial* iteration of the modified
definition the *inflationary* iteration of the original one. Since an
inflationary iteration always converges on finite structures, FO(IFP) is
contained in FO(PFP) (`DescriptiveComplexity.IFPDefinable.pfpDefinable`,
`DescriptiveComplexity.IFPDefinableFree.pfpDefinableFree`) – the easy
inclusion of Abiteboul–Vianu, in both its ordered and order-free forms.

## Closure properties

Same story as for IFP: closed under (ordered) first-order reductions by the
transport lemmas of `DescriptiveComplexity.FixedPointStep`
(`DescriptiveComplexity.PFPDefinable.of_orderedReduction`,
`DescriptiveComplexity.PFPDefinableFree.of_foReduction`). Closure under
complement is *not* by negating the output – divergence makes both a
definition and its output-negation false – but follows on ordered structures
from the capture theorem (`DescriptiveComplexity.FixedPointPartialSpace`)
and `PSPACE = coPSPACE`.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of a partial definition -/

/-- The value of a partial definition is isomorphism-invariant. -/
theorem pfpHolds_equiv (d : Lax535992.InflationaryFixedPoint.StepDef L) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : d.PFPHolds M ↔ d.PFPHolds N := by
  refine exists_congr fun n => ?_
  rw [d.partStage_map e n]
  refine and_congr (d.isFixedPt_next_map_iff e _).symm ?_
  exact realize_sentence_of_equiv
    (d.B.extendEquiv' (L' := L) e (d.partStage M n)) d.out

end StepDef

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (pfpHolds_equiv)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

end StepDef

/-! ### Definability, ordered and order-free -/

/-- FO(≤, PFP) definability only depends on the finite instances of a
problem. -/
theorem pfpDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax134656.PartialFixedPoint.PFPDefinable P ↔ Lax134656.PartialFixedPoint.PFPDefinable Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-! ### Closure under reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

/-- **FO(≤, PFP) definability is closed under ordered first-order
reductions**, by the same route as for IFP
(`DescriptiveComplexity.IFPDefinable.of_orderedReduction`), stage by
stage. -/
theorem PFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : Lax134656.PartialFixedPoint.PFPDefinable Q) :
    Lax134656.PartialFixedPoint.PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨d.pull f.toInterpretation.ordExtend, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [Lax134656.PartialFixedPoint.StepDef.PFPHolds, Lax134656.PartialFixedPoint.StepDef.PFPHolds]
  refine exists_congr fun n => ?_
  rw [d.partStage_map (f.toInterpretation.ordExtendLEquiv A) n,
    StepDef.partStage_pull f.toInterpretation.ordExtend d A n]
  refine and_congr ((d.isFixedPt_next_map_iff (f.toInterpretation.ordExtendLEquiv A)
    _).trans (StepDef.isFixedPt_next_pull_iff f.toInterpretation.ordExtend d _).symm) ?_
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (d.partStage (f.toInterpretation.ordExtend.Map A) n))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (d.partStage (f.toInterpretation.ordExtend.Map A) n)
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (d.partStage (f.toInterpretation.ordExtend.Map A) n)
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    Lax904597.Interpretations.FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (d.partStage (f.toInterpretation.ordExtend.Map A) n))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (d.B.mapAssign (f.toInterpretation.ordExtendLEquiv A).toEquiv
        (d.partStage (f.toInterpretation.ordExtend.Map A) n)))
  have hout := StrongHomClass.realize_sentence
    (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁) d.out
  have hpull := (f.toInterpretation.ordExtend.extendSO d.B).realize_pullSentence d.out A
  exact hout.symm.trans hpull.symm

end Closure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.PFPDefinable

export Lax134656Proofs.DescriptiveComplexity.PFPDefinable (of_orderedReduction)

end Lax134656.PartialFixedPoint.PFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

/-- FO(≤, PFP) definability is closed under plain first-order reductions,
which are in particular ordered ones. -/
theorem PFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : Lax134656.PartialFixedPoint.PFPDefinable Q) :
    Lax134656.PartialFixedPoint.PFPDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.PFPDefinable

export Lax134656Proofs.DescriptiveComplexity.PFPDefinable (of_foReduction)

end Lax134656.PartialFixedPoint.PFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

end Closure

/-! ### FO(IFP) is contained in FO(PFP) -/

section Inflate

variable {L : Language.{0, 0}}

/-- The inflationary reading of a simultaneous induction, as a partial one:
disjoin each variable's own atom onto its step formula, so that one partial
step of the result is one *inflationary* step of the original. -/
noncomputable def StepDef.inflate (d : Lax535992.InflationaryFixedPoint.StepDef L) : Lax535992.InflationaryFixedPoint.StepDef L where
  B := d.B
  step := fun i =>
    Relations.formula (varInSym L d.B i) (fun j => Term.var j) ⊔ d.step i
  out := d.out

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (inflate)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

private theorem realize_inflate_step (d : Lax535992.InflationaryFixedPoint.StepDef L) {A : Type} [L.Structure A]
    (ρ : d.B.Assignment A) (i : d.B.ι) (x : Fin (d.B.arity i) → A) :
    (@Formula.Realize _ A (d.B.structure₁ (L := L) ρ) _
      (((varInSym L d.B i).formula fun j => Term.var j) ⊔ d.step i) x) ↔
      ρ i x ∨ d.next ρ i x := by
  let := d.B.structure₁ (L := L) ρ
  rw [Formula.realize_sup, Formula.realize_rel]
  exact Iff.rfl

/-- One partial step of the inflated induction is one inflationary step of
the original. -/
theorem StepDef.next_inflate (d : Lax535992.InflationaryFixedPoint.StepDef L) {A : Type} [L.Structure A]
    (ρ : d.B.Assignment A) : d.inflate.next ρ = d.inflStep ρ := by
  funext i x
  exact propext (realize_inflate_step d ρ i x)

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (next_inflate)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

/-- The partial stages of the inflated induction are the inflationary stages
of the original. -/
theorem StepDef.partStage_inflate (d : Lax535992.InflationaryFixedPoint.StepDef L) (A : Type) [L.Structure A] (n : ℕ) :
    d.inflate.partStage A n = d.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [d.inflate.partStage_succ, d.inflStage_succ, ih, d.next_inflate]

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (partStage_inflate)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

/-- On a finite structure the inflated induction converges to the
inflationary limit, so its partial value is the inflationary value. -/
theorem StepDef.pfpHolds_inflate (d : Lax535992.InflationaryFixedPoint.StepDef L) (A : Type) [L.Structure A]
    [Finite A] : d.inflate.PFPHolds A ↔ d.IFPHolds A := by
  constructor
  · rintro ⟨n, hn, hout⟩
    rw [d.partStage_inflate A n] at hn hout
    have hfix : IsFixedPt d.inflStep (d.inflStage A n) :=
      (d.next_inflate (d.inflStage A n)).symm.trans hn
    have hlim : d.inflLimit A = d.inflStage A n := by
      funext i x
      refine propext ⟨?_, fun h => ⟨n, h⟩⟩
      rintro ⟨m, hm⟩
      rcases le_total m n with hle | hle
      · exact d.inflStage_le_of_le hle i x hm
      · have hst : d.inflStage A m = d.inflStage A n :=
          iterate_eq_of_isFixedPt hfix hle
        rwa [hst] at hm
    rw [Lax535992.InflationaryFixedPoint.StepDef.IFPHolds, hlim]
    exact hout
  · intro hout
    refine ⟨Nat.card (BAtom d.B A), ?_, ?_⟩
    · rw [d.partStage_inflate A]
      exact (d.next_inflate _).trans (d.isFixedPt_inflStep_card A)
    · rw [d.partStage_inflate A, ← d.inflLimit_eq_stage_card A]
      exact hout

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax134656Proofs.DescriptiveComplexity.StepDef (pfpHolds_inflate)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

/-- **Order-free FO(IFP) is contained in order-free FO(PFP)**: inflate the
induction. The easy inclusion of the Abiteboul–Vianu theorem. -/
theorem IFPDefinableFree.pfpDefinableFree [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax134656.PartialFixedPoint.IFPDefinableFree P) : Lax134656.PartialFixedPoint.PFPDefinableFree P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.inflate, ?_⟩
  intro A _ _ _
  exact (hd A).trans (d.pfpHolds_inflate A).symm

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.IFPDefinableFree

export Lax134656Proofs.DescriptiveComplexity.IFPDefinableFree (pfpDefinableFree)

end Lax134656.PartialFixedPoint.IFPDefinableFree

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

/-- **FO(≤, IFP) is contained in FO(≤, PFP)**: inflate the induction. -/
theorem IFPDefinable.pfpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax535992.InflationaryFixedPoint.IFPDefinable P) : Lax134656.PartialFixedPoint.PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.inflate, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.pfpHolds_inflate A).symm

end Inflate

end Lax134656Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.IFPDefinable

export Lax134656Proofs.DescriptiveComplexity.IFPDefinable (pfpDefinable)

end Lax535992.InflationaryFixedPoint.IFPDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

section Inflate

variable {L : Language.{0, 0}}

end Inflate

end Lax134656Proofs.DescriptiveComplexity


