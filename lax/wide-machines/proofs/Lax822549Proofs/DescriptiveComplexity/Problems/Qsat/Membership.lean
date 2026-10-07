/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax822549Proofs.DescriptiveComplexity.Problems.Qsat.Defs
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

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.QLeast
end Lax822549Proofs.DescriptiveComplexity.QLeast

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace FirstOrder.Language
export Lax134656.Qsat (qsAllVar qsIsClause qsIsVar qsNegIn qsPosIn qsPrefixLt qsat)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.Qsat (IsQAll IsQVar QLeast QPrec QsatHolds QsatMatrix QsatWf QsatWins qAdd qUpd)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# QSAT is in PSPACE

The membership half: the truth of a fully quantified Boolean formula is SO(TC)
definable, hence in `DescriptiveComplexity.PSPACE`.

The walk is the classical depth-first evaluation of the game tree, which is
where the polynomial space of PSPACE is spent: the stack is a *set* of
variables, and a set is one monadic relation variable. Four relation variables
make up a state:

* `D` (unary) – the variables already given a value, i.e., the current branch of
  the game tree; the variable played next is the `prefixLt`-least one outside
  `D` (`DescriptiveComplexity.QLeast`) and the one returned to is the greatest one inside
  it;
* `T` (unary) – the values they were given;
* `up` (nullary – a relation variable of arity `0` is a bit) – the mode:
  descending towards a leaf, or returning a value;
* `res` (nullary) – the value being returned.

No accumulator is needed, and that is what keeps the transition sentence
short: the evaluation *short-circuits*. Having returned the value `v` of the
first branch of a variable `x`, the walk pops `x` immediately when `v` already
settles the node (`v` true at an existential `x`, `v` false at a universal one)
and otherwise plays the second branch, whose value is then the value of the
node. So a value is never combined with a remembered one, and each of the four
transitions merely edits the state
(`DescriptiveComplexity.qsSpec_step_iff`).

## Why the walk computes the game value

The transition relation is *deterministic*
(`DescriptiveComplexity.qsSpec_step_unique`), and the run started at a position
`(D, τ)` in descending mode comes back to `D` in returning mode carrying
exactly `QsatWins D τ` (`DescriptiveComplexity.qsSpec_run`, by induction on the number
of variables outside `D`). Determinism turns that into an equivalence: the
returning state at `D = ∅` is a dead end, and two dead ends reachable from one
state coincide, so a walk accepting the specification has to be *the* run.

Well-formedness is checked by the source sentence, so a malformed instance –
where the prefix order is not a linear order on the variables, and neither the
next nor the last variable of a position need exist – has no starting state at
all.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Generic sentence shapes

Each shape is built over an arbitrary vocabulary and an arbitrary variable
type, so that the same builder and the same realization lemma serve the
current copy of the block, the next one, and the nesting inside a quantifier. -/

section Shapes

/-! #### Well-formedness

The prefix order is a strict linear order on the marked elements. -/

end Shapes

/-! ### The nine conjuncts of the transition sentence

One conjunct per case of the walk and per kind of component: the two unary
components are edited under a `∀ x y`, the two bits under a `∀ x`. All are
built over an arbitrary vocabulary, with the current copy of the block (`d`,
`t`, `u`, `r`) and the next one (`d'`, `t'`, `u'`, `r'`) as parameters. -/

section StepShapes

end StepShapes

/-! ### The block and the vocabularies -/

section Spec

end Spec

/-! ### Reading the specification back -/

section Reading

variable {A : Type} [Lax134656.Qsat.qsat.Structure A] [LinearOrder A]

/-! #### Splitting the connectives of a sentence

Instance search does not see through a specification's block, so the
propositional connectives of the three sentences are split by hand. -/

/-! #### The walk, read back -/

/-- Removing a variable from the quantified set. -/
def qRem (D : A → Prop) (x : A) : A → Prop := fun y => y ≠ x ∧ D y

end Reading

/-! ### The walk is the depth-first evaluation -/

section Correctness

variable {A : Type}

variable [Lax134656.Qsat.qsat.Structure A]

/-- The quantified set of a position is downward closed for the prefix order:
the variables already played are an initial segment. -/
def QDownClosed (D : A → Prop) : Prop := ∀ y z : A, Lax134656.Qsat.IsQVar y → Lax134656.Qsat.QPrec y z → D z → D y

theorem QLeast.qDownClosed_qAdd {D : A → Prop} {x : A} (hx : Lax134656.Qsat.QLeast D x)
    (hD : QDownClosed D) : QDownClosed (Lax134656.Qsat.qAdd D x) := by
  classical
  intro y z hy hyz hz
  rcases hz with hzx | hz
  · subst hzx
    by_cases hDy : D y
    · exact Or.inr hDy
    · exact absurd hyz (hx.2.2 y hy hDy)
  · exact Or.inr (hD y z hy hyz hz)

end Correctness

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.Qsat.QLeast

export Lax822549Proofs.DescriptiveComplexity.QLeast (qDownClosed_qAdd)

end Lax134656.Qsat.QLeast

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Correctness

variable {A : Type}

variable [Lax134656.Qsat.qsat.Structure A]

/-! #### The four transitions -/

variable [LinearOrder A]

/-! #### The next and the last variable exist -/

variable [Finite A]

omit [LinearOrder A] in
/-- On a finite well-formed instance a position that is not a leaf has a next
variable. -/
theorem exists_qLeast (hwf : Lax134656.Qsat.QsatWf A) {D : A → Prop} (h : ∃ z : A, Lax134656.Qsat.IsQVar z ∧ ¬D z) :
    ∃ x : A, Lax134656.Qsat.QLeast D x := by
  have : IsTrans A (Lax134656.Qsat.QPrec (A := A)) := ⟨fun a b c => hwf.trans a b c⟩
  have : Std.Irrefl (Lax134656.Qsat.QPrec (A := A)) := ⟨hwf.irrefl⟩
  obtain ⟨x, hx, hmin⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl (Lax134656.Qsat.QPrec (A := A))).has_min {z : A | Lax134656.Qsat.IsQVar z ∧ ¬D z} h
  exact ⟨x, hx.1, hx.2, fun y hy hd => hmin y ⟨hy, hd⟩⟩

/-! #### The walk is deterministic -/

/-! #### The run of the walk -/

/-! #### Correctness of the specification -/

end Correctness

end Lax822549Proofs.DescriptiveComplexity


