/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.FixedPointStep
import Lax175070Proofs.DescriptiveComplexity.RelComposition
import Lax175070Proofs.DescriptiveComplexity.SecondOrderLift
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

namespace Lax175070Proofs.DescriptiveComplexity.FOReduction
end Lax175070Proofs.DescriptiveComplexity.FOReduction

namespace Lax175070Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax175070Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax175070Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax175070Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax175070Proofs.DescriptiveComplexity.RelOrderedFOReduction
end Lax175070Proofs.DescriptiveComplexity.RelOrderedFOReduction

namespace Lax175070Proofs.DescriptiveComplexity.StepDef
end Lax175070Proofs.DescriptiveComplexity.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# FO(LFP) reductions: the polynomial-time reductions of a machine-free library

A first-order reduction (`DescriptiveComplexity.FOReduction` and its ordered
and relativized variants) is computable in AC⁰; the textbook notion of
reduction for the classes from PTIME up is the *polynomial-time* one. In a
library without machines, a polynomial-time reduction is an interpretation
whose defining formulas belong to a logic capturing PTIME: Immerman's
**FO(LFP) reductions** ([Immerman 1999][immerman1999descriptive], ch. 3). This
file defines them, and embeds every first-order reduction notion of the library
into them – the statement that a first-order reduction is in particular a
polynomial-time one.

## The notion

A `DescriptiveComplexity.LFPInterpretation` is a relativized first-order
interpretation (`DescriptiveComplexity.RelFOInterpretation`) whose formulas
may read, beside the symbols of the base structure, the relations computed by a
simultaneous inflationary induction over it (`DescriptiveComplexity.StepDef`,
the library's normal form for FO(≤, IFP) = FO(LFP) = PTIME on ordered
structures). The induction is computed once, its value expands the base
structure (`DescriptiveComplexity.LFPInterpretation.expStructure`), and the
interpretation is read over the expansion. This is the clausal normal form
Immerman's reductions take: one fixed point, then first-order formulas.

Two design points.

* **The base vocabulary is a parameter.** An `LFPInterpretation L L'` reads an
  induction over `L` itself; the ordered reduction notion instantiates `L` with
  the ordered expansion `L.sum Language.order`. Keeping the base free is what
  lets the closure theorems be proved once, by an induction on quantifier
  blocks, and specialized to the ordered reading at the end.
* **The interpretation is relativized** (it carries a domain formula). The
  library's hardness travels along relativized reductions `≤ʳᶠᵒ[≤]`, and a
  relativized reduction cannot be turned into a whole-universe one – junk
  points cannot be dropped – so a polynomial-time notion that did not carry a
  domain formula would not contain the library's own hardness. Classically a
  polynomial-time reduction may output an instance of any size, and the domain
  formula is what stands for that freedom here.

`DescriptiveComplexity.LFPReduction P Q`, notation `P ≤ˡᶠᵖ Q`, is an ordered
`LFPInterpretation` mapping yes-instances exactly to yes-instances, for every
linear order on the input – order-invariance, exactly as for
`DescriptiveComplexity.OrderedFOReduction`.

## The embeddings

`DescriptiveComplexity.RelOrderedFOReduction.toLFP` (and the two variants
`OrderedFOReduction.toLFP`, `FOReduction.toLFP`) read a first-order reduction
as an FO(LFP) reduction with no induction at all: **every first-order reduction
is a polynomial-time reduction**. The converse fails, and provably so:
`DescriptiveComplexity.exists_lfpReduction_not_orderedReduction`
(`DescriptiveComplexity.FixedPointReductionStrict`) exhibits a target to which
EVEN reduces in FO(LFP) but not in FO(≤).

## What is proved elsewhere

* transitivity, `DescriptiveComplexity.LFPReduction.trans`
  (`DescriptiveComplexity.FixedPointReductionComposition`);
* closure of PTIME, NP and coNP under `≤ˡᶠᵖ`, and hardness stated with it –
  implied by the library's own hardness
  (`DescriptiveComplexity.FixedPointReductionClosure`).
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Lifting a relativized interpretation along a vocabulary map of its source -/

section LiftSource

end LiftSource

/-! ### The induction with no relation variables -/

/-! ### Interpretations reading a fixed point -/

/-- An **FO(LFP) interpretation**: a relativized first-order interpretation
whose formulas may read the value of a simultaneous inflationary induction
over the base structure. The induction `ind` is computed first (its output
sentence is not read); the interpretation `toRel` is then read over the base
vocabulary expanded by the induction's relation variables.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's
FO(LFP) reduction, the logical form of a polynomial-time reduction. -/
structure LFPInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The induction whose value the formulas may read. -/
  ind : Lax535992.InflationaryFixedPoint.StepDef L
  /-- The interpretation, over the base vocabulary expanded by the block of
  the induction. -/
  toRel : Lax904597.Relativized.RelFOInterpretation (L.sum ind.B.lang) L' Tag dim

namespace LFPInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : LFPInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The base structure expanded by the value of the induction – the structure
the interpretation is read over. -/
@[instance_reducible]
def expStructure : (L.sum I.ind.B.lang).Structure A :=
  I.ind.B.structure₁ (L := L) (I.ind.inflLimit A)

/-- The universe of the interpreted structure: the tagged tuples in the
domain, the domain formula being read over the expanded structure. -/
protected def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A

/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  Lax904597.Relativized.RelFOInterpretation.mapRelStructure I.toRel A

end LFPInterpretation

/-! ### With no induction, an FO(LFP) interpretation is a relativized one -/

section NoInduction

end NoInduction

/-! ### FO(LFP) reductions -/

variable {L L' : Language.{0, 0}}

/-- An **FO(LFP) reduction** from `P` to `Q` – a polynomial-time reduction,
in the logical form of [Immerman 1999][immerman1999descriptive]: an FO(LFP)
interpretation over the ordered expansion of the source vocabulary, mapping
yes-instances of `P` exactly to yes-instances of `Q`, for every finite linear
order on the input. As for `DescriptiveComplexity.OrderedFOReduction`, the
problem `P` does not see the order, so the reduction is order-invariant.

The interpretation is relativized, and the domain is required to be
inhabited, as in `DescriptiveComplexity.RelOrderedFOReduction`. -/
structure LFPReduction [L.IsRelational] [L'.IsRelational] (P : Lax904597.Problems.DecisionProblem L)
    (Q : Lax904597.Problems.DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying FO(LFP) interpretation, over the ordered expansion. -/
  toInterpretation : LFPInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (toInterpretation.Map A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ˡᶠᵖ " Q:51 => LFPReduction P Q

namespace LFPReduction

end LFPReduction

/-! ### Every first-order reduction is an FO(LFP) reduction -/

section Embed

end Embed

end Lax175070Proofs.DescriptiveComplexity


