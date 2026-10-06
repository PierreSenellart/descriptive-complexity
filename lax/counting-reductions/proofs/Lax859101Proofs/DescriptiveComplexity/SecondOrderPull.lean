/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Composition
import Lax859101Proofs.DescriptiveComplexity.SecondOrder
import Mathlib.Data.Finite.Sigma
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax859101Proofs.DescriptiveComplexity.FOInterpretation
end Lax859101Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.PiSODefinable
end Lax859101Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax859101Proofs.DescriptiveComplexity.SOAtom
end Lax859101Proofs.DescriptiveComplexity.SOAtom

namespace Lax859101Proofs.DescriptiveComplexity.SOBlock
end Lax859101Proofs.DescriptiveComplexity.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax859101Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax859101Proofs.DescriptiveComplexity

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

namespace Lax859101Proofs.DescriptiveComplexity

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

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (pullSentence)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

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

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (realize_pullSentence)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)

end PullSentence

/-! ### Pulling back a block -/

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

/-- The pullback of a second-order quantifier block through a tagged
`d`-dimensional interpretation: an `n`-ary relation variable on the
interpreted universe `Tag × A^d` becomes one `(n·d)`-ary relation variable on
`A` per `n`-tuple of tags. -/
def SOBlock.pull (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Σ i : B.ι, Fin (B.arity i) → Tag
  arity p := B.arity p.1 * d

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pull)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- Transfer of an assignment on the interpreted universe to an assignment of
the pulled block on the base universe. -/
def SOBlock.pullAssign (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment (Tag × (Fin d → A))) :
    (B.pull Tag d).Assignment A :=
  fun p x => ρ p.1 fun k => (p.2 k, fun j => x (finProdFinEquiv (k, j)))

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pullAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- Transfer of an assignment of the pulled block on the base universe to an
assignment on the interpreted universe. -/
def SOBlock.mergeAssign (B : Lax904597.SecondOrder.SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.Assignment (Tag × (Fin d → A)) :=
  fun i y => σ ⟨i, fun k => (y k).1⟩
    fun m => (y (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (mergeAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- The two assignment transfers are inverse (in the direction needed to
biject the second-order quantifiers). -/
theorem SOBlock.pullAssign_mergeAssign (B : Lax904597.SecondOrder.SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.pullAssign (B.mergeAssign σ) = σ := by
  funext p x
  change σ p
    (fun m => x (finProdFinEquiv
      ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))) = σ p x
  exact congrArg (σ p) (funext fun m => congrArg x (Equiv.apply_symm_apply _ _))

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pullAssign_mergeAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

/-- Merging a pulled assignment gives the assignment back: the transfer
`DescriptiveComplexity.SOBlock.pullAssign` is injective, with
`DescriptiveComplexity.SOBlock.mergeAssign` as a retraction on the other side. -/
theorem SOBlock.mergeAssign_pullAssign (B : Lax904597.SecondOrder.SOBlock)
    (ρ : B.Assignment (Tag × (Fin d → A))) : B.mergeAssign (B.pullAssign ρ) = ρ := by
  funext i y
  change ρ i (fun k => ((y k).1, fun j =>
    (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).2
      (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2)) = ρ i y
  refine congrArg (ρ i) (funext fun k => ?_)
  simp only [Equiv.symm_apply_apply]

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (mergeAssign_pullAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

variable (Tag d A) in
/-- Assignments of the pulled block on the base universe correspond bijectively
to assignments of the block on the tagged tuples. This is what a pullback needs
when the assignments themselves matter and not only their existence: the states
of a walk (`DescriptiveComplexity.SecondOrderTransitiveClosurePull`), the witnesses a
counting problem counts (`DescriptiveComplexity.witnessCount_map`). -/
def SOBlock.pullAssignEquiv (B : Lax904597.SecondOrder.SOBlock) :
    B.Assignment (Tag × (Fin d → A)) ≃ (B.pull Tag d).Assignment A where
  toFun := B.pullAssign
  invFun := B.mergeAssign
  left_inv := B.mergeAssign_pullAssign
  right_inv := B.pullAssign_mergeAssign

end PullBlock

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pullAssignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

variable {Tag d} {A : Type}

end PullBlock

/-! ### Extending an interpretation along a block -/

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

/-- The relation symbol of the pulled block corresponding to a relation
variable of the original block and a tuple of tags. -/
def SOBlock.pullSym (B : Lax904597.SecondOrder.SOBlock) (Tag : Type) [Finite Tag] (d : ℕ) {n : ℕ}
    (r : B.lang.Relations n) (τ : Fin n → Tag) :
    (B.pull Tag d).lang.Relations (B.arity r.1 * d) :=
  ⟨⟨r.1, fun k => τ (Fin.cast r.2 k)⟩, rfl⟩

end ExtendSO

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax859101Proofs.DescriptiveComplexity.SOBlock (pullSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

/-- Extension of an interpretation along a second-order quantifier block: an
interpretation of the target language expanded by the block in the source
language expanded by the pulled block. Symbols of the target language keep
their defining formulas; a relation variable of the block is interpreted by
the pulled relation variable selected by the (static) tag tuple, its
argument positions decoded by `finProdFinEquiv`. -/
def FOInterpretation.extendSO (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (B : Lax904597.SecondOrder.SOBlock) :
    Lax904597.Interpretations.FOInterpretation (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) Tag d where
  relFormula {_n} R τ :=
    match R with
    | Sum.inl r => LHom.sumInl.onFormula (I.relFormula r τ)
    | Sum.inr r =>
        Relations.formula (Sum.inr (B.pullSym Tag d r τ))
          fun m => Term.var
            (Fin.cast r.2 (finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)

end ExtendSO

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (extendSO)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (B : Lax904597.SecondOrder.SOBlock) (A : Type)

variable [instA : L₁.Structure A]

/-- Interpreting and then expanding by a block agrees with expanding by the
pulled block and then interpreting through the extended interpretation: the
identity map is an isomorphism over the expanded target language, when the
block is interpreted by an assignment on the interpreted universe on one side
and by its pulled transfer on the other. -/
def FOInterpretation.extendSOEquiv (ρ : B.Assignment (I.Map A)) :
    @Language.Equiv (L₂.sum B.lang) ((I.extendSO B).Map A) (I.Map A)
      (letI := (B.pull Tag d).structure (B.pullAssign ρ)
       Lax904597.Interpretations.FOInterpretation.mapStructure (I.extendSO B) A)
      (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) :=
  letI := (B.pull Tag d).structure (B.pullAssign ρ)
  letI := B.structure ρ
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r =>
        exact (LHom.realize_onFormula LHom.sumInl
          (I.relFormula r fun i => (x i).1)).symm
      | inr r =>
        change ρ r.1 (fun j => x (Fin.cast r.2 j)) ↔
          ρ r.1 (fun k => ((x (Fin.cast r.2 k)).1,
            fun j => (x (Fin.cast r.2
                (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).2
              (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2))
        refine iff_of_eq (congrArg (ρ r.1) (funext fun k => ?_))
        simp only [Equiv.symm_apply_apply]
        exact rfl }

end ExtendSO

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (extendSOEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

variable (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) (B : Lax904597.SecondOrder.SOBlock) (A : Type)

variable [instA : L₁.Structure A]

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

section Guards

end Guards

end Clausal

end Lax859101Proofs.DescriptiveComplexity


