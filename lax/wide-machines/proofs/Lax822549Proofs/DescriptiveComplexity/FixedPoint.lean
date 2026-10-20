/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Lax822549Proofs.DescriptiveComplexity.Iterate
import Lax822549Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax822549Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax822549Proofs.DescriptiveComplexity.Padding
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax822549Proofs.DescriptiveComplexity.Derives
end Lax822549Proofs.DescriptiveComplexity.Derives

namespace Lax822549Proofs.DescriptiveComplexity.LFPDef
end Lax822549Proofs.DescriptiveComplexity.LFPDef

namespace Lax822549Proofs.DescriptiveComplexity.LFPDefinable
end Lax822549Proofs.DescriptiveComplexity.LFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity.SigmaSOHornDefinable
end Lax822549Proofs.DescriptiveComplexity.SigmaSOHornDefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax822549Proofs.DescriptiveComplexity

/-!
# FO(LFP): first-order logic with a least fixed point

The logic FO(LFP) ([Immerman 1986][immerman1986relational]; [Vardi
1982][vardi1982complexity]), in the clausal normal form this library uses for
kernels everywhere else: a `DescriptiveComplexity.LFPDef` bundles

* a block of relation variables and a finite list of *rules* deriving them –
  the same `DescriptiveComplexity.HornClause` data as an SO-Horn program, read here as
  an inductive definition rather than a constraint;
* an arbitrary first-order *output* sentence over the input vocabulary
  expanded by those variables, evaluated at the least fixed point.

## Why the output formula is the point

The fixed point is the same object in both logics – the least model of a set
of rules. What distinguishes FO(LFP) from SO-Horn is what one is allowed to
say *about* it. An SO-Horn program can only reject models, through goal
clauses, and a goal clause tests its atoms positively; FO(LFP) evaluates an
unrestricted first-order sentence, so it may negate fixed-point atoms.

That is exactly the closure that SO-Horn lacks: `DescriptiveComplexity.LFPDefinable` is
closed under complement by negating the output
(`DescriptiveComplexity.LFPDefinable.compl`, a one-liner), whereas the corresponding
statement for SO-Horn is open – see `DescriptiveComplexity.Problems.HornSat`. The
inclusion `DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` transports every
SO-Horn definition into this logic, so PTIME as defined by the Horn fragment
sits inside FO(LFP) together with its complements.

## What is proved here, and where the equivalence is completed

`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` is one half of the equivalence
of the two formalisms: every SO-Horn definition is an FO(LFP) definition. The
other half – bringing an FO(LFP) definition back into the Horn fragment – is
the translation of `DescriptiveComplexity.FixedPointHorn`, built on the stage theory of
this file: the stages `DescriptiveComplexity.derivesIn` stabilize once the atom count is
reached (`DescriptiveComplexity.derivesIn_iff_derives_of_card_le`), so a stage indexed by
a large enough tuple stands in for the fixed point, and its *complement* can
be derived positively, one stage at a time. Together the two halves make the
notions interchangeable (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`)
and give `PiP 0 = SigmaP 0` (`DescriptiveComplexity.piP_zero_eq`).

The notion is also closed under (ordered) first-order reductions
(`DescriptiveComplexity.LFPDefinable.of_orderedReduction`), so it is class-worthy in the
sense of `DescriptiveComplexity.ComplexityClass`.

A second consumer of the stage theory is not formalized: a `Σ₁` definition,
giving `FO(LFP) ⊆ NP` directly, would *guess* a fixed point together with a
well-founded derivation order and check both first-order. The semantic key is
provided here – `DescriptiveComplexity.derives_eq_of_closed_of_wf` says that a relation
*closed* under the rules and *well-foundedly derivable* is exactly the least
fixed point, `DescriptiveComplexity.derives_step_of_depth` supplies the witnessing
order from the stages, and `DescriptiveComplexity.LFPDef.holds_iff_of_certificate`
packages this; the formulas themselves are not built. (The inclusion itself
follows by composing the translation with the Horn membership of
`DescriptiveComplexity.Problems.HornSat`.)

## The fixed point

Rather than a stage-indexed iteration, the least model is the inductive
predicate `DescriptiveComplexity.Derives`: a tuple is derived when some rule fires on
already-derived tuples. Being an inductive definition it comes with exactly the
two properties a least fixed point needs – it satisfies the rules
(`DescriptiveComplexity.lfpAssign_rule`) and it is contained in every assignment that
does (`DescriptiveComplexity.lfpAssign_least`).

Rules whose head is `none` derive nothing and are simply inert here, so an
SO-Horn program can be handed over unchanged: its goal clauses reappear in the
output formula.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The least model of a rule system -/

section Derives

end Derives

/-! ### Stages, depth, and the certificate characterization

Putting FO(LFP) back into the Horn fragment, and certifying a fixed point in
`Σ₁`, both need the same thing: a way to say
“this relation *is* the least fixed point” that a *positive* formalism can
test. Closure alone is not enough (anything larger is closed too); what pins
the least fixed point down is closure together with *well-founded
derivability* – every element derived by a rule from strictly earlier
elements. That is `DescriptiveComplexity.derives_eq_of_closed_of_wf` below, and the
stages provide the witnessing order. -/

section Stages

/-! #### Depth, and the certificate -/

/-! #### Stabilization: the stages close within `Nat.card` many rounds

On a finite structure the stages are an increasing chain of subsets of the
finitely many atoms, so they stabilize by the time the atom count is reached
(`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, the one chain
pigeonhole of the library, in `DescriptiveComplexity.Iterate`) – after that many
rounds, `DescriptiveComplexity.derivesIn` *is* the least fixed point. This is
what lets a stage indexed by a large enough tuple stand in for the fixed point
itself in `DescriptiveComplexity.FixedPointHorn`. -/

end Stages

/-! ### The fixed point transports along isomorphisms -/

section Map

end Map

/-! ### The fixed point commutes with pullbacks

The least fixed point of the pulled rules is the pullback of the least fixed
point: both inclusions are an application of leastness, since each side is
closed under the other's rules (`DescriptiveComplexity.HornProgram.pull_holds`). This is
the fixed-point half of closure of `DescriptiveComplexity.LFPDefinable` under (ordered)
first-order reductions; what remains for that closure is to pull the *output*
sentence back, through `DescriptiveComplexity.FOInterpretation.extendSO` and
`DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`, which is bookkeeping between
the three structures involved rather than mathematics. -/

section Pull

end Pull

/-! ### Definitions in FO(LFP) -/

namespace LFPDef

end LFPDef

/-! ### SO-Horn definitions are FO(LFP) definitions

A Horn program splits into its *rules* (the clauses with a head), which define
the fixed point, and its *goal clauses* (those without), which merely say that
the fixed point avoids certain configurations – a first-order statement about
it, and so exactly what an output formula can express. -/

section OfHorn

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The symbol of a relation variable of the block. -/
abbrev varSym (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) : B.lang.Relations (B.arity i) := ⟨i, rfl⟩

section Realize

end Realize

end OfHorn

/-! ### Closure under reductions -/

section Closure

end Closure

end Lax822549Proofs.DescriptiveComplexity


