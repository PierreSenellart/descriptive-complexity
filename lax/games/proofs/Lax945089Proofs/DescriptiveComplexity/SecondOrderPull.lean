/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Composition
import Lax945089Proofs.DescriptiveComplexity.SecondOrder
import Mathlib.Data.Finite.Sigma
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089Proofs.DescriptiveComplexity.FOInterpretation
end Lax945089Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax945089Proofs.DescriptiveComplexity.PiSODefinable
end Lax945089Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax945089Proofs.DescriptiveComplexity.SOAtom
end Lax945089Proofs.DescriptiveComplexity.SOAtom

namespace Lax945089Proofs.DescriptiveComplexity.SOBlock
end Lax945089Proofs.DescriptiveComplexity.SOBlock

namespace Lax945089Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax945089Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax945089Proofs.DescriptiveComplexity

/-!
# Pulling second-order definability back through an interpretation

If `P ≤ᶠᵒ Q` and `Q` is `Σₖ`- (resp. `Πₖ`-) definable, then so is `P`
(`DescriptiveComplexity.SigmaSODefinable.of_foReduction`,
`DescriptiveComplexity.PiSODefinable.of_foReduction`): the levels of the polynomial
hierarchy, defined by second-order alternation, are closed under first-order
reductions.

The proof pulls the defining second-order sentence back through the
interpretation `I` underlying the reduction, block by block:

* a second-order quantifier over an `n`-ary relation on the interpreted
  universe `Tag × A^d` becomes a family of second-order quantifiers over
  `(n·d)`-ary relations on `A`, one per `n`-tuple of tags
  (`DescriptiveComplexity.SOBlock.pull`; assignments transfer bijectively via
  `DescriptiveComplexity.SOBlock.pullAssign` / `DescriptiveComplexity.SOBlock.mergeAssign`);
* the interpretation extends to the languages expanded by a block
  (`DescriptiveComplexity.FOInterpretation.extendSO`): relation variables of the block
  are interpreted by the corresponding pulled relation variables, reading the
  tag tuple off statically; interpreting-then-expanding agrees with
  expanding-then-interpreting (`DescriptiveComplexity.FOInterpretation.extendSOEquiv`);
* the first-order kernel is pulled back by
  `DescriptiveComplexity.FOInterpretation.pull` from `DescriptiveComplexity.Composition`, packaged
  at the sentence level as `DescriptiveComplexity.FOInterpretation.pullSentence`.

`DescriptiveComplexity.sorealize_pullSO` puts these together: alternating second-order
satisfaction in the interpreted structure coincides with alternating
second-order satisfaction of the pulled sentence (over the pulled blocks) in
the base structure.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Pulling back a sentence -/

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

/-- The pullback of an `L₂`-sentence through the interpretation `I`: an
`L₁`-sentence that holds in `A` exactly when the original sentence holds in
`I.Map A` (see `FOInterpretation.realize_pullSentence`). -/
noncomputable def FOInterpretation.pullSentence (φ : L₂.Sentence) : L₁.Sentence :=
  (I.pull (φ : L₂.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → Tag)).relabel
    fun p => (isEmptyElim p.1 : Empty)

end PullSentence

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax945089Proofs.DescriptiveComplexity.FOInterpretation (pullSentence)

end Lax904597.Interpretations.FOInterpretation

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

theorem FOInterpretation.realize_pullSentence (φ : L₂.Sentence) (A : Type)
    [L₁.Structure A] :
    A ⊨ I.pullSentence φ ↔ I.Map A ⊨ φ := by
  have h1 : A ⊨ I.pullSentence φ ↔
      (I.pull (φ : L₂.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → Tag)).Realize
        ((default : Empty → A) ∘ fun p : (Empty ⊕ Fin 0) × Fin d =>
          (isEmptyElim p.1 : Empty)) :=
    Formula.realize_relabel
  rw [h1, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula Empty 0) a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end PullSentence

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax945089Proofs.DescriptiveComplexity.FOInterpretation (realize_pullSentence)

end Lax904597.Interpretations.FOInterpretation

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

end PullSentence

/-! ### Pulling back a block -/

section PullBlock

end PullBlock

/-! ### Extending an interpretation along a block -/

section ExtendSO

end ExtendSO

/-! ### Pulling back an alternating second-order sentence -/

section PullSO

end PullSO

/-! ### Closure of the definability levels under FO reductions -/

section Closure

end Closure

/-! ### Pulling back atoms, guards and tag assignments

The clausal fragments (SO-Horn, SO-Krom) pull a *clause list* back through an
interpretation rather than a formula: each clause becomes one clause per static
assignment of tags to its universally quantified variables, its guard becoming
an ordinary formula pullback and its atoms becoming atoms of the pulled
relation variables. The pieces that do not depend on the shape of a clause are
collected here, and are shared by `DescriptiveComplexity.SecondOrderHornPull` and
`DescriptiveComplexity.SecondOrderKromPull`. -/

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The interpreted valuation determined by a tag assignment and a valuation
of the coordinates. -/
def tagVal (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A : Type} (t : Fin k → Tag)
    (w : Fin (k * d) → A) : Fin k → I.Map A :=
  fun p => (t p, fun j => w (finProdFinEquiv (p, j)))

omit [Finite Tag] in
/-- Splitting an interpreted valuation into its tags and its coordinates. -/
theorem tagVal_split {A : Type} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (v : Fin k → I.Map A) :
    tagVal I (fun p => (v p).1)
      (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) = v := by
  funext p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  rw [tagVal]
  exact congrArg₂ (fun (q : Fin k) (i : Fin d) => (v q).2 i)
    (congrArg Prod.fst (Equiv.symm_apply_apply _ _))
    (congrArg Prod.snd (Equiv.symm_apply_apply _ _))

section Guards

end Guards

end Clausal

end Lax945089Proofs.DescriptiveComplexity


