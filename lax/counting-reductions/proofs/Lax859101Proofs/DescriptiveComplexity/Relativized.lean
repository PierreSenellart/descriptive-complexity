/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Ordered
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

namespace Lax859101Proofs.DescriptiveComplexity.FOInterpretation
end Lax859101Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax859101Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity.RelOrderedFOReduction
end Lax859101Proofs.DescriptiveComplexity.RelOrderedFOReduction

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation RelOrderedFOReduction)
end Lax859101Proofs.DescriptiveComplexity

/-!
# Relativized first-order interpretations (definable target universes)

An `DescriptiveComplexity.FOInterpretation` fixes the target universe to all of
`Tag × A^dim`. That is convenient for *subset*-style problems – a yes-witness
lives on part of the universe and junk elements sit isolated and unused – but
it cannot target a **spanning** problem such as HAMILTON CIRCUIT, where a
yes-witness (a tour) must visit *every* universe element: junk points with no
valid incident edges make every interpreted instance a no-instance.

The textbook remedy ([Immerman 1999][immerman1999descriptive]) is a **domain
formula**: the target universe is a *definable subset* of `Tag × A^dim`. This
file adds it as a layer *on top of* `FOInterpretation`, so that no existing
interpretation, reduction or problem file changes:

* `DescriptiveComplexity.RelFOInterpretation` extends `FOInterpretation` with a
  `domFormula : Tag → L.Formula (Fin dim)`;
* `DescriptiveComplexity.RelFOInterpretation.MapRel` is the interpreted structure carried by
  the subtype `{x : Tag × A^dim // domFormula holds of x}`;
* `DescriptiveComplexity.RelOrderedFOReduction` (notation `≤ʳᶠᵒ[≤]`) is the ordered reduction
  through such an interpretation, carrying the extra obligation
  `dom_nonempty` – a definable domain can be empty on a nonempty structure, so
  `Nonempty Tag` does not by itself guarantee a nonempty output;
* `DescriptiveComplexity.OrderedFOReduction.toRel` embeds an ordinary ordered reduction as a
  relativized one with `domFormula := ⊤`, the transparency of the whole-universe
  case being an isomorphism (`DescriptiveComplexity.FOInterpretation.toRelLEquiv`) rather than
  a definitional equality.

This is the hardness-side machinery of relativized reductions; it is what a
hardness proof for a spanning problem needs. Membership closure under
relativized reductions lives in `DescriptiveComplexity.FixedPointStepRel`, and is
not needed when membership is a direct second-order sentence.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

namespace RelFOInterpretation

variable (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

theorem relMap_mapRel [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.MapRel A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2 :=
  Iff.rfl

end RelFOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (relMap_mapRel)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

namespace RelFOInterpretation

variable (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The relativized universe of a finite structure over finite tags is
finite. -/
theorem mapRel_finite [Finite Tag] [Finite A] : Finite (I.MapRel A) :=
  Subtype.finite

end RelFOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (mapRel_finite)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

namespace RelFOInterpretation

variable (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end RelFOInterpretation

/-! ### Functoriality on isomorphisms -/

namespace RelFOInterpretation

variable [L'.IsRelational] (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim)
  {M N : Type} [L.Structure M] [L.Structure N]

/-- Relativized interpretations are functorial on `L`-isomorphisms: the domain
formula is an `L`-formula, so its truth transports, and the induced map of
subtypes is an `L'`-isomorphism. -/
def mapRelLEquiv (e : M ≃[L] N) : I.MapRel M ≃[L'] I.MapRel N where
  toFun x := ⟨(x.1.1, fun j => e (x.1.2 j)),
    (StrongHomClass.realize_formula e (I.domFormula x.1.1)).mpr x.2⟩
  invFun x := ⟨(x.1.1, fun j => e.symm (x.1.2 j)),
    (StrongHomClass.realize_formula e.symm (I.domFormula x.1.1)).mpr x.2⟩
  left_inv x := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun j => e.symm_apply_apply (x.1.2 j)⟩)
  right_inv x := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun j => e.apply_symm_apply (x.1.2 j)⟩)
  map_fun' f := isEmptyElim f
  map_rel' _ _ := by
    rw [RelFOInterpretation.relMap_mapRel, RelFOInterpretation.relMap_mapRel]
    exact StrongHomClass.realize_formula e _

end RelFOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Relativized.RelFOInterpretation

export Lax859101Proofs.DescriptiveComplexity.RelFOInterpretation (mapRelLEquiv)

end Lax904597.Relativized.RelFOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

namespace RelFOInterpretation

variable [L'.IsRelational] (I : Lax904597.Relativized.RelFOInterpretation L L' Tag dim)
  {M N : Type} [L.Structure M] [L.Structure N]

end RelFOInterpretation

/-! ### The whole-universe case is an ordinary interpretation -/

/-- Any interpretation is a relativized one whose domain formula is `⊤`: the
target universe is all of `Tag × A^dim`, as before. -/
def FOInterpretation.toRel (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) :
    Lax904597.Relativized.RelFOInterpretation L L' Tag dim :=
  { toFOInterpretation := I, domFormula := fun _ => ⊤ }

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (toRel)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- The transparency of the `⊤` domain: the relativized universe of `I.toRel`
is `L'`-isomorphic to the ordinary universe of `I`. (Not a definitional
equality – a subtype over `⊤` is not literally the product.) -/
def FOInterpretation.toRelLEquiv [L'.IsRelational] (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim)
    (A : Type) [L.Structure A] : I.Map A ≃[L'] I.toRel.MapRel A where
  toFun a := ⟨a, Formula.realize_top.mpr trivial⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_fun' f := isEmptyElim f
  map_rel' _ _ := Iff.rfl

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (toRelLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-! ### Relativized ordered reductions -/

@[inherit_doc]
scoped notation:50 P:51 " ≤ʳᶠᵒ[≤] " Q:51 => Lax904597.Relativized.RelOrderedFOReduction P Q

namespace RelOrderedFOReduction

end RelOrderedFOReduction

end Lax859101Proofs.DescriptiveComplexity


