/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.SecondOrderLift
import Lax859101Proofs.DescriptiveComplexity.RelComposition
import Lax859101Proofs.DescriptiveComplexity.SecondOrderPull
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

namespace Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize)
end Lax859101Proofs.DescriptiveComplexity

/-!
# Pulling `∃SO[new]` definability back through an interpretation

Closure of definability in existential second-order logic with value invention
under first-order reductions (`DescriptiveComplexity.SigmaSONewDefinable.of_foReduction`),
the closure that makes RE a `DescriptiveComplexity.ComplexityClass`.

## The construction

Let `I` be the interpretation of a reduction `P ≤ᶠᵒ Q`, and let `Q` be defined
by a block `B` and a kernel `φ` read in the extended universe
`I.Map A ⊕ Fin m`. The extended universe of the *source* is `A ⊕ Fin m` – the
same number of invented values – and the point of the construction is that
the target's extended universe is **definable inside it**:

* a point of `I.Map A` is a tag `t` together with `dim` original elements;
* an invented value is an invented value.

Both are tagged tuples, so they are the universe of a *relativized*
interpretation `DescriptiveComplexity.newInterp` with tags `Tag ⊕ Unit` and
dimension `dim + 1`, whose domain formula asks, at tag `Sum.inl t`, that the
first `dim` coordinates be original, and at tag `Sum.inr ()`, that the last
coordinate be invented and the others copy it (a diagonal, so that each
invented value is *one* point). The spare coordinate of a `Sum.inl` point has
to be pinned to a single element, for which the block guesses a **canonical
element** (`DescriptiveComplexity.canonSym`), constrained to be unique by
`DescriptiveComplexity.canonGuard`; pinning it to a coordinate of the tuple
would not survive `dim = 0`, where `I.Map A` is a constant-size structure.

Everything else is machinery that already exists:

* the kernel is pulled back by the guarded pullback
  `DescriptiveComplexity.RelFOInterpretation.pullRel` of
  `DescriptiveComplexity.RelComposition`, which relativizes quantifiers to the
  definable universe and substitutes the defining formulas for atoms;
* the relation variables of `B` are pulled back exactly as in
  `DescriptiveComplexity.SecondOrderPull`, one `(k · (dim+1))`-ary variable per
  tuple of tags (`DescriptiveComplexity.SOBlock.pull`). Their assignments
  transfer in the *flipped* direction a definable universe forces:
  `DescriptiveComplexity.targetAssign` reads a guessed assignment back on the
  target's universe, `DescriptiveComplexity.sourceAssign` extends an assignment
  of the target's block by junk off the interpreted points, and the composite
  `targetAssign ∘ sourceAssign` is the identity, not merely the identity on the
  interpreted points
  (`DescriptiveComplexity.targetAssign_sourceAssign`) – which is all an
  *existential* block needs;
* the interpretation's own defining formulas quantify over `A`, so they are
  read in `A ⊕ Fin m` relativized to the original elements
  (`DescriptiveComplexity.relOld` of `DescriptiveComplexity.Relativize`).
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The pulled block -/

section Block

end Block

section Parts

end Parts

/-! ### The two vocabularies -/

/-! ### The interpretation of the target's extended universe -/

section Interp

end Interp

/-! ### Realization in the host structure -/

section Realize

end Realize

/-! ### The interpreted universe *is* the target's extended universe -/

section Universe

end Universe

/-! ### Transfer of the kernel -/

section Transfer

end Transfer

/-! ### The guarded pullback of a sentence -/

namespace RelFOInterpretation

variable {L₃ L₄ : Language.{0, 0}} {TagJ : Type} {dJ : ℕ}

variable (J : Lax904597.Relativized.RelFOInterpretation L₃ L₄ TagJ dJ) [L₄.IsRelational] [Finite TagJ]

/-- The guarded pullback of a sentence through a relativized interpretation:
an `L₃`-sentence that holds in `A` exactly when the original sentence holds in
the definable universe `J.MapRel A` (the relativized counterpart of
`DescriptiveComplexity.FOInterpretation.pullSentence`). -/
noncomputable def pullRelSentence (φ : L₄.Sentence) : L₃.Sentence :=
  (J.pullRel (φ : L₄.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → TagJ)).relabel
    fun p => (isEmptyElim p.1 : Empty)

end RelFOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (pullRelSentence)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace RelFOInterpretation

variable {L₃ L₄ : Language.{0, 0}} {TagJ : Type} {dJ : ℕ}

variable (J : Lax904597.Relativized.RelFOInterpretation L₃ L₄ TagJ dJ) [L₄.IsRelational] [Finite TagJ]

theorem realize_pullRelSentence (φ : L₄.Sentence) (A : Type) [L₃.Structure A] :
    A ⊨ J.pullRelSentence φ ↔ (J.MapRel A) ⊨ φ := by
  have h1 : A ⊨ J.pullRelSentence φ ↔
      (J.pullRel (φ : L₄.BoundedFormula Empty 0)
          (isEmptyElim : (Empty ⊕ Fin 0) → TagJ)).Realize
        ((default : Empty → A) ∘ fun p : (Empty ⊕ Fin 0) × Fin dJ => (isEmptyElim p.1 : Empty)) :=
    Formula.realize_relabel
  rw [h1, J.realize_pullRel (φ : L₄.BoundedFormula Empty 0) isEmptyElim _
    (fun b => isEmptyElim b)]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := J.MapRel A) (φ : L₄.BoundedFormula Empty 0) a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end RelFOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (realize_pullRelSentence)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace RelFOInterpretation

variable {L₃ L₄ : Language.{0, 0}} {TagJ : Type} {dJ : ℕ}

variable (J : Lax904597.Relativized.RelFOInterpretation L₃ L₄ TagJ dJ) [L₄.IsRelational] [Finite TagJ]

end RelFOInterpretation

/-! ### Reproducing an assignment of the target's block -/

section Source

end Source

/-! ### The closure theorem -/

section Closure

end Closure

end Lax859101Proofs.DescriptiveComplexity


