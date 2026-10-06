/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Counting.Class
import Lax175070Proofs.DescriptiveComplexity.FixedPointStep
import Lax175070Proofs.DescriptiveComplexity.Hierarchy
import Lax175070Proofs.DescriptiveComplexity.OrderedComposition
import Lax175070Proofs.DescriptiveComplexity.RelComposition
import Lax175070Proofs.DescriptiveComplexity.SecondOrderLift
import Lax175070Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax175070Proofs.DescriptiveComplexity.SecondOrderPull
import Lax175070Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity.FOInterpretation
end Lax175070Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity.SharpPDefinable
end Lax175070Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation sumOrderStructure)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable witnessCount)
end Lax175070Proofs.DescriptiveComplexity

/-!
# Subtractive reductions

The reductions of [Durand, Hermann, Kolaitis 2005][durand2005subtractive],
which sit between the parsimonious reductions and the one-call reductions of
`DescriptiveComplexity.Counting.Reduction`, and under which `#P` is closed.

A **strong subtractive reduction** from `C` to `D`
(`DescriptiveComplexity.StrongSubtractiveReduction`) draws two instances of
`D`, the *subtrahend* and the *minuend*, such that the solutions of the first
are among those of the second and

`C A = D (minuend A) - D (subtrahend A)`.

The condition on solutions is what keeps the difference inside `#P`, and it is
about solutions, not counts. So `D` comes with a *presentation*: a second-order
block and a first-order kernel whose witnesses it counts
(`DescriptiveComplexity.StrongSubtractiveReduction.present`), which plays the
part of the relation `B` in the paper's `#·B`. The two interpretations share
their tags and their dimension, so the two instances have the same universe,
ordered the same way, and a witness of one can be compared with a witness of
the other (`DescriptiveComplexity.FOInterpretation.WitAt`).

Strong subtractive reductions do not compose, and a **subtractive reduction**
`C ≤ˢ D` (`DescriptiveComplexity.SubtractiveReducible`) is a finite chain of
steps, as in the paper. Two departures from it, both forced:

* a step is a strong subtractive reduction *or a parsimonious reduction*, in
  its most general form, relativized and ordered. The paper obtains the second
  as the special case of the first whose subtrahend has no solution, which
  needs the target to have such an instance, definably; admitting the step
  directly asks for nothing;
* the target of a strong step is presented by a first-order kernel, hence is
  itself in `#P`. The paper's relations are arbitrary, which is what lets it
  speak of the classes above `#P`; the library has no such classes yet.

`#P` is closed under subtractive reductions
(`DescriptiveComplexity.SharpPDefinable.of_subtractive`, Theorem 3.3 of the
paper): the witnesses of the minuend that are not witnesses of the subtrahend
are the witnesses of one kernel, the conjunction of the pulled kernel of the
first with the negated pulled kernel of the second. So this is the widest
notion of the library under which the class is closed, and the plain words go
to it, as on the decision side they go to reductions the classes are closed
under: `DescriptiveComplexity.CountingClass.Hard` and
`DescriptiveComplexity.CountingClass.Complete` are hardness and completeness
under subtractive reductions. Parsimonious hardness and completeness imply
them (`DescriptiveComplexity.hard_sharpP_of_parsimoniousHard`,
`DescriptiveComplexity.complete_sharpP_of_parsimoniousComplete`).
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Witnesses at an interpreted instance -/

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

/-- The assignment `ρ` is a witness of the kernel `φ` at the instance drawn by
the interpretation `I`, ordered lexicographically. The universe of that
instance is `Tag × A ^ dim` whatever `I` is, so the witnesses at two
interpretations with the same tags and dimension are comparable. -/
def FOInterpretation.WitAt (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim)
    (B : Lax904597.SecondOrder.SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] (ρ : B.Assignment (Tag × (Fin dim → A))) : Prop :=
  @Sentence.Realize ((L'.sum Language.order).sum B.lang) (I.ordExtend.Map A)
    (@sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure I.ordExtend A) (B.structure ρ)) φ

end WitAt

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax175070Proofs.DescriptiveComplexity.FOInterpretation (WitAt)

end Lax904597.Interpretations.FOInterpretation

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

end WitAt

/-! ### Strong subtractive reductions -/

/-- A **strong subtractive reduction**: the target is presented as the witness
count of a kernel, two interpretations with the same tags and dimension draw a
subtrahend and a minuend, every witness at the first is a witness at the
second, and the count of the source is the difference of the two counts. -/
structure StrongSubtractiveReduction [L.IsRelational] [L'.IsRelational]
    (C : Lax366625.CountingProblems.CountingProblem L) (D : Lax366625.CountingProblems.CountingProblem L') where
  /-- The tags used by the two interpretations. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- Tags are linearly ordered: the order of the drawn instances is the
  lexicographic one. -/
  [tagOrder : LinearOrder Tag]
  /-- The dimension of the two interpretations. -/
  dim : ℕ
  /-- The second-order block of the presentation of the target. -/
  block : Lax904597.SecondOrder.SOBlock
  /-- The first-order kernel of the presentation of the target. -/
  kernel : ((L'.sum Language.order).sum block.lang).Sentence
  /-- The target counts the witnesses of its presentation, whatever the linear
  order. -/
  present : ∀ (A : Type) [L'.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    D A = Lax366625.WitnessCounting.witnessCount block kernel A
  /-- The interpretation drawing the subtrahend. -/
  subtrahend : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpretation drawing the minuend. -/
  minuend : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Every witness at the subtrahend is a witness at the minuend. -/
  witness_le : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ρ : block.Assignment (Tag × (Fin dim → A))),
    subtrahend.WitAt block kernel A ρ → minuend.WitAt block kernel A ρ
  /-- The count of the source and the count at the subtrahend add up to the
  count at the minuend. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A + D (subtrahend.Map A) = D (minuend.Map A)

section Closure

end Closure

/-! ### Subtractive reductions -/

/-- **Subtractive reducibility**, `C ≤ˢ D`: a finite chain of steps, each a
strong subtractive reduction or a relativized ordered parsimonious
reduction. -/
inductive SubtractiveReducible : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational],
    Lax366625.CountingProblems.CountingProblem L → Lax366625.CountingProblems.CountingProblem L' → Prop
  /-- The empty chain. -/
  | refl {L : Language.{0, 0}} [L.IsRelational] (C : Lax366625.CountingProblems.CountingProblem L) :
      SubtractiveReducible C C
  /-- A strong subtractive step, then a chain. -/
  | strong {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂}
      {E : Lax366625.CountingProblems.CountingProblem L₃} (f : StrongSubtractiveReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E
  /-- A parsimonious step, then a chain. -/
  | parsimonious {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂}
      {E : Lax366625.CountingProblems.CountingProblem L₃} (f : C ≤ʳᵖ[≤] D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E

@[inherit_doc]
scoped notation:50 C:51 " ≤ˢ " D:51 => SubtractiveReducible C D

section Reducible

end Reducible

/-! ### Hardness and completeness -/

namespace CountingClass

end CountingClass

end Lax175070Proofs.DescriptiveComplexity


