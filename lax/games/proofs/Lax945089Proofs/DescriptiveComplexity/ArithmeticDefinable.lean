/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Arithmetic
import Lax945089Proofs.DescriptiveComplexity.FirstOrderDefinable
import Lax945089Proofs.DescriptiveComplexity.Complexity
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

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability

namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax945089.OrderFreeFirstOrder
end Lax945089.OrderFreeFirstOrder

namespace Lax945089Proofs.DescriptiveComplexity.AC0Definable
end Lax945089Proofs.DescriptiveComplexity.AC0Definable

namespace Lax945089Proofs.DescriptiveComplexity.FODefinable
end Lax945089Proofs.DescriptiveComplexity.FODefinable

namespace Lax945089Proofs.DescriptiveComplexity.FODefinableFree
end Lax945089Proofs.DescriptiveComplexity.FODefinableFree

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.OrderFreeFirstOrder (FODefinableFree)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.FirstOrderDefinability (FODefinable)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax895169.ArithmeticLogic (AC0Definable)
end Lax945089Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax895169.ArithmeticLogic (arith)
end FirstOrder.Language

/-!
# AC⁰ definability: first-order logic with the numeric predicates

**The class AC⁰**, as a logic: a problem is `AC⁰` definable when a single
sentence over the *arithmetic* expansion of its vocabulary decides it on
nonempty finite ordered structures – first-order logic with `≤`, `+` and `×` on
the ranks of the elements (`DescriptiveComplexity.AC0Definable`). Classically
this is `FO(≤, +, ×) = FO(≤, BIT)`, and (DLOGTIME-)uniform AC⁰ ([Immerman
1999][immerman1999descriptive], Thm 1.17; [Barrington, Immerman & Straubing
1990][barrington1990uniformity]; in textbook form, [Vollmer
1999][vollmer1999introduction] Thm 4.73, with Thm 4.69 for the non-uniform
class); here, as everywhere in this library, the logic is the *definition*, and
the identification with a circuit model is a bridge that is not built – see
below.

## Why `+` and `×` rather than `BIT`

Expressively it makes no difference (the two are classically interdefinable –
a fact the literature states rather than proves: [Vollmer
1999][vollmer1999introduction] p. 163 attributes it to a 1994 e-mail of Lindell
and to [Immerman 1999][immerman1999descriptive] §1.2.1, and
`DescriptiveComplexity.LogTime` proves it), so the choice is made by a proof
obligation elsewhere: the closure of the class
under first-order reductions must define the numeric predicates of the
*interpreted* universe – lexicographically ordered tagged tuples, hence base-`n`
digits – from those of the base. For `+` and `×` that is schoolbook arithmetic
on a constant number of digits; for `BIT` it is base-`n`-to-base-2 conversion,
whose only route is to define `+` and `×` on the tuples first. So `BIT` is a
later addition, not the primitive.

## Order-invariance, and the absence of an order-free variant

The definition quantifies over structures carrying a `LinearOrder`, and requires
the equivalence for *every* linear order: the sentence sees `≤, +, ×`, the
problem does not. This is verbatim the convention of
`DescriptiveComplexity.FODefinable`, and it is not a convenience here but a
necessity: the numeric predicates are *functions of the order*
(`DescriptiveComplexity.Arithmetic`), so there is no order-free reading of this
logic to state, and no `AC0DefinableFree` in this file. Together with
`DescriptiveComplexity.LOGSPACE`, whose logic is an operator rather than a
fragment, this is the second place where the bottom of the ladder breaks the
pattern of the classes above it.

## What is proved here, and what is not

* `FO(≤) ⊆ AC⁰` (`DescriptiveComplexity.FODefinable.ac0Definable`), by transport
  along `DescriptiveComplexity.sumOrderToArith`; the inclusion is **strict**
  (`DescriptiveComplexity.exists_ac0Definable_not_foDefinable`, in
  `DescriptiveComplexity.Problems.Even`), so the numeric predicates genuinely add
  power, unconditionally and with no complexity assumption.
* Closure under complement (`DescriptiveComplexity.AC0Definable.compl`) – free,
  since the defining object is a sentence, where every class above needed an
  argument (Immerman–Szelepcsényi for NL, a determinized walk for LOGSPACE).
* **Not** here: that AC⁰ definability is closed under first-order reductions
  (the arithmetic of an interpreted universe, as above), and therefore no
  `DescriptiveComplexity.ComplexityClass` yet; and no circuit model, so no
  capture theorem. The inclusion in `DescriptiveComplexity.LOGSPACE` is proved
  separately, through the multi-head automaton, and gives every consumer that
  the missing closure lemma would.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The definition -/

/-! ### First-order definability, read arithmetically -/

/-! ### Boolean closure -/

/-! ### Terms of a relational language

Every vocabulary in this library is relational, and so is
`FirstOrder.Language.arith`: a term is a variable and nothing else. Two
consumers need to say so – the evaluator of an arithmetic formula
(`DescriptiveComplexity.HeadEvalArith`) and the translation of one into the bit
logic – so it is said here, below both. -/

/-! ### Terms of a relational language -/

section RelTerm

end RelTerm

end Lax945089Proofs.DescriptiveComplexity


