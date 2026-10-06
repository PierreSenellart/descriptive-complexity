/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Counting.Class
import Lax859101Proofs.DescriptiveComplexity.SecondOrderRelPull
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

namespace Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.SOBlock
end Lax859101Proofs.DescriptiveComplexity.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity.SharpPDefinable
end Lax859101Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
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

/-!
# `#P` is closed under relativized parsimonious reductions

Membership in `#P` travels backward along the relativized reductions
`C ≤ʳᵖ[≤] D`, those whose target universe is a definable set of tagged tuples
(`DescriptiveComplexity.SharpPDefinable.of_relOrderedParsimonious`). With the
hardness half, which holds by definition, this makes the relativized
reductions reductions of the class in the full sense.

## From a retraction to a bijection

`DescriptiveComplexity.SecondOrderRelPull` pulls a second-order sentence back
through a relativized interpretation, and observes that the transfer of
assignments is only a retraction: a relation variable of the pulled block
ranges over *all* tagged tuples, and may hold of tuples that are not points of
the target. That is harmless for deciding, and fatal for counting, every
assignment of the target being counted once per way of filling in the tuples
outside the domain.

The repair is one conjunct in the kernel,
`DescriptiveComplexity.supportSentence`: every pulled relation variable holds
only of tuples all of whose points are in the domain. On such *supported*
assignments the read-back is injective
(`DescriptiveComplexity.SOBlock.pullAssignRel_readAssignRel`), so the witnesses
of the kernel in the target are, bijectively, the supported witnesses of the
pulled kernel in the source (`DescriptiveComplexity.witnessCount_mapRel`).
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Supported assignments -/

section Supported

variable {Tag : Type} [Finite Tag] {dm : ℕ} {A : Type} [L₁.Structure A]

/-- An assignment of the pulled block is **supported** by the domain of a
relativized interpretation when each of its relations holds only of tuples all
of whose points are in the domain. -/
def SOBlock.Supported (B : Lax904597.SecondOrder.SOBlock) (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    (σ : (B.pull Tag dm).Assignment A) : Prop :=
  ∀ (p : Σ i : B.ι, Fin (B.arity i) → Tag) (x : Fin (B.arity p.1 * dm) → A), σ p x →
    ∀ k : Fin (B.arity p.1), (J.domFormula (p.2 k)).Realize fun j => x (finProdFinEquiv (k, j))

end Supported

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (Supported)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Supported

variable {Tag : Type} [Finite Tag] {dm : ℕ} {A : Type} [L₁.Structure A]

/-- A transferred assignment is supported. -/
theorem SOBlock.supported_pullAssignRel (B : Lax904597.SecondOrder.SOBlock) (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm)
    (ρ : B.Assignment (J.MapRel A)) : B.Supported J (B.pullAssignRel J ρ) :=
  fun _ _ h k => h.1 k

end Supported

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (supported_pullAssignRel)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Supported

variable {Tag : Type} [Finite Tag] {dm : ℕ} {A : Type} [L₁.Structure A]

/-- **On supported assignments the read-back is injective**: transferring the
read-back of a supported assignment returns it. -/
theorem SOBlock.pullAssignRel_readAssignRel (B : Lax904597.SecondOrder.SOBlock)
    (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm) {σ : (B.pull Tag dm).Assignment A}
    (hσ : B.Supported J σ) : B.pullAssignRel J (B.readAssignRel J σ) = σ := by
  funext p x
  obtain ⟨i, τ⟩ := p
  have hx : (fun m : Fin (B.arity i * dm) =>
      x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))) = x :=
    funext fun m => congrArg x (finProdFinEquiv.apply_symm_apply m)
  refine propext ⟨?_, fun h => ⟨hσ ⟨i, τ⟩ x h, ?_⟩⟩
  · rintro ⟨_, h⟩
    have h' : σ ⟨i, τ⟩ fun m : Fin (B.arity i * dm) =>
        x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) := h
    rwa [hx] at h'
  · change σ ⟨i, τ⟩ fun m : Fin (B.arity i * dm) =>
      x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))
    rw [hx]
    exact h

end Supported

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pullAssignRel_readAssignRel)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Supported

variable {Tag : Type} [Finite Tag] {dm : ℕ} {A : Type} [L₁.Structure A]

/-- Realization of a finite conjunction of formulas. -/
private theorem realize_iInf' {L : Language.{0, 0}} {M : Type} [L.Structure M] {α β : Type}
    [Finite β] (f : β → L.Formula α) (v : α → M) :
    (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

/-- The sentence saying that the assignment of the pulled block is supported:
for each relation variable, at each tuple it holds of, every point of the tuple
satisfies the domain formula of its tag. -/
noncomputable def supportSentence (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm) (B : Lax904597.SecondOrder.SOBlock) :
    (L₁.sum (B.pull Tag dm).lang).Sentence :=
  Formula.iInf fun p : Σ i : B.ι, Fin (B.arity i) → Tag =>
    Formula.iAlls (Fin (B.arity p.1 * dm))
      (((Relations.formula
            (Sum.inr ⟨p, rfl⟩ : (L₁.sum (B.pull Tag dm).lang).Relations (B.arity p.1 * dm))
            fun m => Term.var m).imp
          (Formula.iInf fun k : Fin (B.arity p.1) =>
            (LHom.sumInl.onFormula (J.domFormula (p.2 k))).relabel
              fun j => finProdFinEquiv (k, j))).relabel Sum.inr)

theorem realize_supportSentence (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm) (B : Lax904597.SecondOrder.SOBlock)
    (σ : (B.pull Tag dm).Assignment A) :
    @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
        (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
        (supportSentence J B) ↔ B.Supported J σ := by
  let := (B.pull Tag dm).structure σ
  rw [supportSentence, Sentence.Realize, realize_iInf']
  refine forall_congr' fun p => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel, Formula.realize_imp, realize_iInf']
  refine imp_congr ?_ (forall_congr' fun k => ?_)
  · exact Formula.realize_rel.trans Iff.rfl
  · exact Formula.realize_relabel.trans ((LHom.realize_onFormula _ _).trans Iff.rfl)

end Supported

/-! ### Witness counts through a relativized interpretation -/

section Count

variable {Tag : Type} [Finite Tag] {dm : ℕ} [L₂.IsRelational]

/-- A pulled kernel holds at an assignment of the pulled block exactly when
the kernel holds, in the interpreted structure, at its read-back. -/
theorem RelFOInterpretation.realize_pullRelSentence_iff_read
    (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm) (B : Lax904597.SecondOrder.SOBlock) (φ : (L₂.sum B.lang).Sentence)
    (A : Type) [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A) :
    @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
        (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
        ((J.extendSORel B).pullRelSentence φ) ↔
      @Sentence.Realize (L₂.sum B.lang) (J.MapRel A)
        (@sumStructure L₂ B.lang (J.MapRel A) (Lax904597.Relativized.RelFOInterpretation.mapRelStructure J A)
          (B.structure (B.readAssignRel J σ))) φ := by
  let := (B.pull Tag dm).structure σ
  exact ((J.extendSORel B).realize_pullRelSentence φ A).trans
    (@StrongHomClass.realize_sentence (L₂.sum B.lang) ((J.extendSORel B).MapRel A) (J.MapRel A)
      (Lax904597.Relativized.RelFOInterpretation.mapRelStructure (J.extendSORel B) A)
      (@sumStructure L₂ B.lang (J.MapRel A) (Lax904597.Relativized.RelFOInterpretation.mapRelStructure J A)
        (B.structure (B.readAssignRel J σ))) _ _ _
      (J.extendSORelEquivAny B A σ) φ)

end Count

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (realize_pullRelSentence_iff_read)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Count

variable {Tag : Type} [Finite Tag] {dm : ℕ} [L₂.IsRelational]

/-- **Pulling a witness count back through a relativized interpretation**: the
witnesses of a kernel in the definable structure are, bijectively, the
supported witnesses of the pulled kernel in the base structure. -/
theorem witnessCount_mapRel (J : Lax904597.Relativized.RelFOInterpretation L₁ L₂ Tag dm) (B : Lax904597.SecondOrder.SOBlock)
    (φ : (L₂.sum B.lang).Sentence) (A : Type) [L₁.Structure A] :
    Lax366625.WitnessCounting.witnessCount B φ (J.MapRel A) =
      Lax366625.WitnessCounting.witnessCount (B.pull Tag dm)
        ((J.extendSORel B).pullRelSentence φ ⊓ supportSentence J B) A := by
  have key : ∀ σ : (B.pull Tag dm).Assignment A,
      @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
          (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
          ((J.extendSORel B).pullRelSentence φ ⊓ supportSentence J B) ↔
        @Sentence.Realize (L₂.sum B.lang) (J.MapRel A)
            (@sumStructure L₂ B.lang (J.MapRel A) (Lax904597.Relativized.RelFOInterpretation.mapRelStructure J A)
              (B.structure (B.readAssignRel J σ))) φ ∧ B.Supported J σ := by
    intro σ
    have h1 := J.realize_pullRelSentence_iff_read B φ A σ
    have h2 := realize_supportSentence J B σ
    let := (B.pull Tag dm).structure σ
    rw [Sentence.Realize, Formula.realize_inf]
    exact and_congr h1 h2
  exact Nat.card_congr
    { toFun := fun ρ => ⟨B.pullAssignRel J ρ.1, (key _).mpr
        ⟨(B.readAssignRel_pullAssignRel J ρ.1).symm ▸ ρ.2, B.supported_pullAssignRel J ρ.1⟩⟩
      invFun := fun σ => ⟨B.readAssignRel J σ.1, ((key σ.1).mp σ.2).1⟩
      left_inv := fun ρ => Subtype.ext (B.readAssignRel_pullAssignRel J ρ.1)
      right_inv := fun σ => Subtype.ext (B.pullAssignRel_readAssignRel J ((key σ.1).mp σ.2).2) }

end Count

/-! ### Closure -/

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

/-- **`#P`-definability is closed under relativized ordered parsimonious
reductions.** -/
theorem SharpPDefinable.of_relOrderedParsimonious (f : C ≤ʳᵖ[≤] D) (h : Lax366625.WitnessCounting.SharpPDefinable D) :
    Lax366625.WitnessCounting.SharpPDefinable C := by
  obtain ⟨B, φ, hφ⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim,
    (f.toRelInterpretation.ordExtendRel.extendSORel B).pullRelSentence φ ⊓
      supportSentence f.toRelInterpretation.ordExtendRel B, ?_⟩
  intro A _ _ _ _
  let := f.toRelInterpretation.mapRelLinearOrder A
  have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
  have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
  rw [f.correct A, hφ (f.toRelInterpretation.MapRel A),
    ← witnessCount_mapRel f.toRelInterpretation.ordExtendRel B φ A]
  exact (witnessCount_iso B φ (f.toRelInterpretation.ordExtendRelLEquiv A)).symm

end Closure

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax859101Proofs.DescriptiveComplexity.SharpPDefinable (of_relOrderedParsimonious)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}

end Closure

end Lax859101Proofs.DescriptiveComplexity


