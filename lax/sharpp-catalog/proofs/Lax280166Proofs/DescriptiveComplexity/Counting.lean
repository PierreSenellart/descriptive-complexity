/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.OrderedComposition
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

namespace Lax280166Proofs.DescriptiveComplexity.CountingProblem
end Lax280166Proofs.DescriptiveComplexity.CountingProblem

namespace Lax280166Proofs.DescriptiveComplexity.FOInterpretation
end Lax280166Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax280166Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax280166Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax280166Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax280166Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem OrderedParsimoniousReduction ParsimoniousReduction)
end Lax280166Proofs.DescriptiveComplexity

/-!
# Counting problems and parsimonious reductions

A decision problem is an isomorphism-invariant *property* of finite structures;
a **counting problem** (`DescriptiveComplexity.CountingProblem`) is an
isomorphism-invariant *number* attached to them – the number of satisfying
assignments of a CNF formula, of proper colorings of a graph, of accepting runs
of a machine. Vocabularies, tagged interpretations and the invariance
discipline carry over unchanged from `DescriptiveComplexity.Interpretation`.

The reductions of this file are the **parsimonious** ones: a first-order
interpretation under which the two counts are *equal*,

* `DescriptiveComplexity.ParsimoniousReduction`, notation `C ≤ᵖ D`, over the bare
  vocabulary, and
* `DescriptiveComplexity.OrderedParsimoniousReduction`, notation `C ≤ᵖ[≤] D`, over
  the ordered expansion, the equation holding whatever the linear order.

They are `DescriptiveComplexity.FOReduction` and
`DescriptiveComplexity.OrderedFOReduction` with the equivalence of the `correct`
field replaced by an equation, and they compose for the same reason: the
composite interpretation is isomorphic to the twice-applied one, and a counting
problem does not distinguish isomorphic structures.

Every counting problem has a decision problem underneath, its **support**
(`DescriptiveComplexity.CountingProblem.support`): “is the count positive?”. A
parsimonious reduction between two counting problems is in particular a
first-order reduction between their supports
(`DescriptiveComplexity.ParsimoniousReduction.toFOReduction`), which is how
hardness results for counting problems yield hardness results for decision
problems.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

namespace CountingProblem

variable {L} [L.IsRelational]

@[ext]
theorem ext {C D : Lax366625.CountingProblems.CountingProblem L} (h : ∀ (A : Type) [L.Structure A], C A = D A) :
    C = D := by
  obtain ⟨c, hc⟩ := C
  obtain ⟨d, hd⟩ := D
  have : c = d := funext fun A => funext fun inst => h A
  subst this
  rfl

end CountingProblem

end Lax280166Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax280166Proofs.DescriptiveComplexity.CountingProblem (ext)

end Lax366625.CountingProblems.CountingProblem

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

namespace CountingProblem

variable {L} [L.IsRelational]

theorem support_iff (C : Lax366625.CountingProblems.CountingProblem L) (A : Type) [L.Structure A] :
    C.support A ↔ 0 < C A :=
  Iff.rfl

end CountingProblem

end Lax280166Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax280166Proofs.DescriptiveComplexity.CountingProblem (support_iff)

end Lax366625.CountingProblems.CountingProblem

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

namespace CountingProblem

variable {L} [L.IsRelational]

end CountingProblem

variable {L} {L' : Language.{0, 0}}

/-! ### Reading an interpretation over a larger source vocabulary -/

section LiftSource

variable {L₀ L₁ : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- An interpretation read over a larger source vocabulary: every defining
formula is transported along the vocabulary map. -/
def FOInterpretation.liftSource (Φ : L₀ →ᴸ L₁) (I : Lax904597.Interpretations.FOInterpretation L₀ L' Tag dim) :
    Lax904597.Interpretations.FOInterpretation L₁ L' Tag dim where
  relFormula R t := Φ.onFormula (I.relFormula R t)

end LiftSource

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax280166Proofs.DescriptiveComplexity.FOInterpretation (liftSource)

end Lax904597.Interpretations.FOInterpretation

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

variable {L} {L' : Language.{0, 0}}

section LiftSource

variable {L₀ L₁ : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- On a structure that is an expansion along the vocabulary map, the lifted
interpretation produces the same structure as the original one: the identity
on tagged tuples is an isomorphism. -/
def FOInterpretation.liftSourceLEquiv [L'.IsRelational] (Φ : L₀ →ᴸ L₁)
    (I : Lax904597.Interpretations.FOInterpretation L₀ L' Tag dim) (A : Type) [L₀.Structure A] [L₁.Structure A]
    [Φ.IsExpansionOn A] : (I.liftSource Φ).Map A ≃[L'] I.Map A where
  toEquiv := Equiv.refl _
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun {n} R x => by
    rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    exact (LHom.realize_onFormula _ _).symm

end LiftSource

end Lax280166Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax280166Proofs.DescriptiveComplexity.FOInterpretation (liftSourceLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

variable {L} {L' : Language.{0, 0}}

section LiftSource

variable {L₀ L₁ : Language.{0, 0}} {Tag : Type} {dim : ℕ}

end LiftSource

/-! ### Parsimonious reductions -/

@[inherit_doc]
scoped notation:50 C:51 " ≤ᵖ " D:51 => Lax366625.CountingProblems.ParsimoniousReduction C D

@[inherit_doc]
scoped notation:50 C:51 " ≤ᵖ[≤] " D:51 => Lax366625.CountingProblems.OrderedParsimoniousReduction C D

section Support

end Support

/-! ### Reflexivity and transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

/-- A parsimonious reduction is in particular an ordered one: lift its defining
formulas to the ordered expansion, where they ignore the order. -/
noncomputable def ParsimoniousReduction.toOrdered (g : C ≤ᵖ D) : C ≤ᵖ[≤] D :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation :=
      { relFormula := fun R t => LHom.sumInl.onFormula (g.toInterpretation.relFormula R t) }
    correct := fun A _ _ _ _ => by
      refine (g.correct A).trans (D.iso_invariant ?_)
      exact
        { toEquiv := Equiv.refl _
          map_fun' := fun f => isEmptyElim f
          map_rel' := fun {n} R x => by
            rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
            exact LHom.realize_onFormula _ _ } }

end Trans

end Lax280166Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.ParsimoniousReduction

export Lax280166Proofs.DescriptiveComplexity.ParsimoniousReduction (toOrdered)

end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

variable {L} {L' : Language.{0, 0}}

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

variable {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂} {E : Lax366625.CountingProblems.CountingProblem L₃}

end Trans

end Lax280166Proofs.DescriptiveComplexity


