/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Counting.RelClosure
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax859101.SubtractiveReductions
end Lax859101.SubtractiveReductions

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.FOInterpretation
end Lax859101Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax859101Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax859101Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax859101Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax859101Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax859101Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax859101Proofs.DescriptiveComplexity.SharpPDefinable
end Lax859101Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax859101Proofs.DescriptiveComplexity.StrongSubtractiveReduction
end Lax859101Proofs.DescriptiveComplexity.StrongSubtractiveReduction

namespace Lax859101Proofs.DescriptiveComplexity.SubtractiveReducible
end Lax859101Proofs.DescriptiveComplexity.SubtractiveReducible

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax859101.SubtractiveReductions (StrongSubtractiveReduction SubtractiveReducible)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation sumOrderStructure)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable witnessCount)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation
export Lax859101.SubtractiveReductions.FOInterpretation (WitAt ordExtend)
end Lax904597.Interpretations.FOInterpretation

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

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Witnesses at an interpreted instance -/

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

variable [Finite Tag] (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim)
  (B : Lax904597.SecondOrder.SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence)
  (A : Type) [L.Structure A] [LinearOrder A]

/-- A witness at an interpreted instance is a witness of the pulled kernel, at
the pulled assignment. -/
theorem FOInterpretation.witAt_iff_pull (ρ : B.Assignment (Tag × (Fin dim → A))) :
    I.WitAt B φ A ρ ↔
      @Sentence.Realize ((L.sum Language.order).sum (B.pull Tag dim).lang) A
        (@sumStructure (L.sum Language.order) (B.pull Tag dim).lang A _
          ((B.pull Tag dim).structure (B.pullAssign ρ)))
        ((I.ordExtend.extendSO B).pullSentence φ) := by
  let := (B.pull Tag dim).structure (B.pullAssign ρ)
  exact (@StrongHomClass.realize_sentence ((L'.sum Language.order).sum B.lang)
      ((I.ordExtend.extendSO B).Map A) (I.ordExtend.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure (I.ordExtend.extendSO B) A)
      (@sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
        (I.ordExtend.mapStructure A) (B.structure ρ)) _ _ _
      (I.ordExtend.extendSOEquiv B A ρ) φ).symm.trans
    ((I.ordExtend.extendSO B).realize_pullSentence φ A).symm

end WitAt

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (witAt_iff_pull)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

variable [Finite Tag] (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim)
  (B : Lax904597.SecondOrder.SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence)
  (A : Type) [L.Structure A] [LinearOrder A]

omit [Finite Tag] in
/-- The witness count of the kernel at the interpreted instance, ordered
lexicographically, is the number of witnesses there. -/
theorem FOInterpretation.witnessCount_map_eq_card :
    @Lax366625.WitnessCounting.witnessCount (L'.sum Language.order) B φ (I.Map A)
        (letI := I.mapLinearOrder A; Lax904597.Interpretations.sumOrderStructure L' (I.Map A)) =
      Nat.card {ρ : B.Assignment (Tag × (Fin dim → A)) // I.WitAt B φ A ρ} := by
  let := I.mapLinearOrder A
  exact (witnessCount_iso B φ (I.ordExtendLEquiv A)).symm

end WitAt

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (witnessCount_map_eq_card)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

variable [Finite Tag] (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim)
  (B : Lax904597.SecondOrder.SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence)
  (A : Type) [L.Structure A] [LinearOrder A]

omit [Finite Tag] in
/-- A witness of an order-free kernel at an interpreted instance: the order of
the instance plays no part. -/
theorem FOInterpretation.witAt_orderFreeKernel (ψ : (L'.sum B.lang).Sentence)
    (ρ : B.Assignment (Tag × (Fin dim → A))) :
    I.WitAt B (orderFreeKernel B ψ) A ρ ↔
      @Sentence.Realize (L'.sum B.lang) (I.Map A)
        (@sumStructure L' B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) ψ := by
  let s₁ : (L'.sum B.lang).Structure (I.ordExtend.Map A) :=
    @sumStructure L' B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)
  let s₂ : ((L'.sum Language.order).sum B.lang).Structure (I.ordExtend.Map A) :=
    @sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
      (Lax904597.Interpretations.FOInterpretation.mapStructure I.ordExtend A) (B.structure ρ)
  have : @LHom.IsExpansionOn _ _ (LHom.sumMap (LHom.sumInl : L' →ᴸ L'.sum Language.order)
      (LHom.id B.lang)) (I.ordExtend.Map A) s₁ s₂ :=
    @LHom.IsExpansionOn.mk _ _ _ _ s₁ s₂ (fun f _ => isEmptyElim f)
      (fun r _ => by cases r <;> rfl)
  exact @LHom.realize_onSentence _ _ (I.ordExtend.Map A) s₁ s₂
    (LHom.sumMap (LHom.sumInl : L' →ᴸ L'.sum Language.order) (LHom.id B.lang)) this ψ

end WitAt

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (witAt_orderFreeKernel)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

variable [Finite Tag] (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim)
  (B : Lax904597.SecondOrder.SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence)
  (A : Type) [L.Structure A] [LinearOrder A]

end WitAt

/-- The witness count of an order-free kernel, lifted to the ordered expansion,
is its witness count. -/
theorem witnessCount_orderFreeKernel (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] :
    Lax366625.WitnessCounting.witnessCount B (orderFreeKernel B φ) A = Lax366625.WitnessCounting.witnessCount B φ A := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun ρ => ?_)
  let := B.structure ρ
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
      (LHom.id B.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  exact LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
    (LHom.id B.lang)) φ

/-! ### Strong subtractive reductions -/

section Closure

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- With the witnesses of one predicate among those of another, the witnesses
of the second that are not witnesses of the first make up the difference. -/
theorem card_diff_add_card {α : Type} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // Q a ∧ ¬P a} + Nat.card {a // P a} = Nat.card {a // Q a} := by
  classical
  have e : {a // Q a ∧ ¬P a} ⊕ {a // P a} ≃ {a // Q a} :=
    { toFun := Sum.elim (fun a => ⟨a.1, a.2.1⟩) fun a => ⟨a.1, h a.1 a.2⟩
      invFun := fun a => if hP : P a.1 then Sum.inr ⟨a.1, hP⟩ else Sum.inl ⟨a.1, a.2, hP⟩
      left_inv := by
        rintro (⟨a, h1, h2⟩ | ⟨a, h1⟩)
        · simp [h2]
        · simp [h1]
      right_inv := fun a => by
        by_cases hP : P a.1 <;> simp [hP] }
  rw [← Nat.card_sum, Nat.card_congr e]

/-- **The source of a strong subtractive reduction is in `#P`**: it counts the
witnesses at the minuend that are not witnesses at the subtrahend, and those
are the witnesses of one kernel. -/
theorem SharpPDefinable.of_strongSubtractive (f : Lax859101.SubtractiveReductions.StrongSubtractiveReduction C D) :
    Lax366625.WitnessCounting.SharpPDefinable C := by
  let := f.tagFinite
  let := f.tagNonempty
  let := f.tagOrder
  refine ⟨f.block.pull f.Tag f.dim,
    (f.minuend.ordExtend.extendSO f.block).pullSentence f.kernel ⊓
      ∼((f.subtrahend.ordExtend.extendSO f.block).pullSentence f.kernel), ?_⟩
  intro A _ _ _ _
  have cnt : ∀ I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' f.Tag f.dim,
      D (I.Map A) = Nat.card {ρ : f.block.Assignment (f.Tag × (Fin f.dim → A)) //
        I.WitAt f.block f.kernel A ρ} := by
    intro I
    let := I.mapLinearOrder A
    have : Finite (I.Map A) := I.map_finite A
    have : Nonempty (I.Map A) := I.map_nonempty A
    rw [f.present (I.Map A)]
    exact I.witnessCount_map_eq_card f.block f.kernel A
  have hc := f.correct A
  rw [cnt f.subtrahend, cnt f.minuend, ← card_diff_add_card (f.witness_le A)] at hc
  rw [Nat.add_right_cancel hc]
  refine Nat.card_congr (Equiv.subtypeEquiv (f.block.pullAssignEquiv f.Tag f.dim A) fun ρ => ?_)
  have h1 := f.minuend.witAt_iff_pull f.block f.kernel A ρ
  have h2 := f.subtrahend.witAt_iff_pull f.block f.kernel A ρ
  let := (f.block.pull f.Tag f.dim).structure (f.block.pullAssign ρ)
  rw [Sentence.Realize, Formula.realize_inf, Formula.realize_not]
  exact and_congr h1 (not_congr h2)

end Closure

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax859101Proofs.DescriptiveComplexity.SharpPDefinable (of_strongSubtractive)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Closure

variable [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

end Closure

/-! ### Subtractive reductions -/

@[inherit_doc]
scoped notation:50 C:51 " ≤ˢ " D:51 => Lax859101.SubtractiveReductions.SubtractiveReducible C D

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- A strong subtractive reduction is a subtractive reduction. -/
theorem StrongSubtractiveReduction.subtractiveReducible (f : Lax859101.SubtractiveReductions.StrongSubtractiveReduction C D) :
    C ≤ˢ D :=
  .strong f (.refl D)

end Reducible

end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101.SubtractiveReductions.StrongSubtractiveReduction

export Lax859101Proofs.DescriptiveComplexity.StrongSubtractiveReduction (subtractiveReducible)

end Lax859101.SubtractiveReductions.StrongSubtractiveReduction

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- A relativized parsimonious reduction is a subtractive reduction. -/
theorem RelOrderedParsimoniousReduction.subtractiveReducible (f : C ≤ʳᵖ[≤] D) : C ≤ˢ D :=
  .parsimonious f (.refl D)

end Reducible

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction

export Lax859101Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction (subtractiveReducible)

end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- **Subtractive reducibility is transitive** (Proposition 3.2 of the paper):
chains concatenate. -/
theorem SubtractiveReducible.trans (h₁ : C ≤ˢ D) (h₂ : D ≤ˢ E) : C ≤ˢ E := by
  induction h₁ with
  | refl _ => exact h₂
  | strong f _ ih => exact .strong f (ih h₂)
  | parsimonious f _ ih => exact .parsimonious f (ih h₂)

end Reducible

end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101.SubtractiveReductions.SubtractiveReducible

export Lax859101Proofs.DescriptiveComplexity.SubtractiveReducible (trans)

end Lax859101.SubtractiveReductions.SubtractiveReducible

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- **`#P` is closed under subtractive reductions** (Theorem 3.3 of
[Durand, Hermann, Kolaitis 2005][durand2005subtractive]). -/
theorem SharpPDefinable.of_subtractive (h : C ≤ˢ D) (hD : Lax366625.WitnessCounting.SharpPDefinable D) :
    Lax366625.WitnessCounting.SharpPDefinable C := by
  induction h with
  | refl _ => exact hD
  | strong f _ _ => exact .of_strongSubtractive f
  | parsimonious f _ ih => exact (ih hD).of_relOrderedParsimonious f

end Reducible

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax859101Proofs.DescriptiveComplexity.SharpPDefinable (of_subtractive)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

end Reducible

/-! ### Hardness and completeness -/

namespace CountingClass

variable (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- A counting problem is **hard** for a class when every problem of the class
reduces to it by a subtractive reduction. -/
def Hard (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''), D ∈ K → D ≤ˢ C

/-- A counting problem is **complete** for a class when it belongs to it and
is hard for it, under subtractive reductions. -/
def Complete (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  C ∈ K ∧ K.Hard C

variable {K}

theorem Complete.hard {C : Lax366625.CountingProblems.CountingProblem L} (h : K.Complete C) : K.Hard C := h.2

/-- Hardness travels forward along subtractive reductions. -/
theorem Hard.of_subtractive {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}
    (f : C ≤ˢ D) (hC : K.Hard C) : K.Hard D :=
  fun E hE => (hC E hE).trans f

end CountingClass

/-- **Membership in `#P` travels backward along subtractive reductions.** -/
theorem mem_sharpP_of_subtractive [L.IsRelational] [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}
    {D : Lax366625.CountingProblems.CountingProblem L'} (h : C ≤ˢ D) (hD : D ∈ SharpP) : C ∈ SharpP :=
  SharpPDefinable.of_subtractive h hD

/-- **Parsimonious `#P`-hardness implies `#P`-hardness**: a relativized
parsimonious reduction is a subtractive reduction. -/
theorem hard_sharpP_of_parsimoniousHard [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}
    (h : SharpP.ParsimoniousHard C) : SharpP.Hard C :=
  fun D hD => (h D hD).some.subtractiveReducible

/-- A parsimoniously `#P`-complete problem is `#P`-complete. -/
theorem complete_sharpP_of_parsimoniousComplete [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}
    (h : SharpP.ParsimoniousComplete C) : SharpP.Complete C :=
  ⟨h.1, hard_sharpP_of_parsimoniousHard h.2⟩

end Lax859101Proofs.DescriptiveComplexity


