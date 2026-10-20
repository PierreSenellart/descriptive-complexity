/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Ordered
import Lax280166Proofs.DescriptiveComplexity.OrderWalk
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

namespace Lax280166Proofs.Foreign.FirstOrder.Language.arithRel
end Lax280166Proofs.Foreign.FirstOrder.Language.arithRel

namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax280166Proofs.DescriptiveComplexity
export Lax895169.ArithmeticLogic (arithStructure)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax895169.ArithmeticLogic (arith arithRel)
end FirstOrder.Language

/-!
# The numeric predicates: the arithmetic expansion of a vocabulary

The vocabulary of the bottom class of the ordered world. A finite linearly
ordered universe *is* an initial segment of `ℕ`, by the rank of an element
(`DescriptiveComplexity.orank`, the number of its strict predecessors), and this
file makes the arithmetic of that segment available to formulas: the language
`FirstOrder.Language.arith` has a binary `≤` and two **ternary** symbols
`plus` and `times`, interpreted on a finite linear order by

* `plus x y z` – `orank x + orank y = orank z`,
* `times x y z` – `orank x * orank y = orank z`.

Relations, not functions, and therefore *truncated*: a sum or product that does
not fit in the universe simply has no witness, and “`x + y` overflows” is the
first-order `¬∃z, plus x y z` (`DescriptiveComplexity.no_plus_iff_card_le`).

## Why relations of the *order*, and not a new sort of data

The numeric predicates are not extra input relations that an instance happens
to carry: they are **functions of the linear order**, computed by `orank`. Three
consequences, all of them design constraints rather than remarks.

* The canonical structure needs `[LinearOrder A] [Finite A]`, where Mathlib's
  `FirstOrder.Language.orderStructure` needs only `[LE A]`. It is still an
  `instance`; it simply does not fire on an infinite type, which is correct –
  the arithmetic of an infinite universe is not what this vocabulary means.
* There is no order-free reading of this vocabulary at all. Every logic built
  on it is intrinsically a logic of ordered structures, and the class
  `DescriptiveComplexity.AC0Definable` accordingly has no `…Free` variant,
  unlike ∃SO, `SO(LFP)` or `SO(PFP)`.
* Because the interpretation is canonical, an *interpretation* of one
  vocabulary in another does not get the numeric predicates for free: it must
  define the arithmetic of the interpreted universe, which is why the arithmetic
  analogue of `DescriptiveComplexity.FOInterpretation.ordExtend` is real work
  and not plumbing.

## The transport from the ordered expansion

`DescriptiveComplexity.sumOrderToArith` is the language map
`L.sum Language.order →ᴸ L.sum Language.arith` sending `≤` to `≤`, with its
`FirstOrder.Language.LHom.IsExpansionOn` instance, so that every FO(≤) sentence
and every FO(≤) gadget formula of this library can be read as an arithmetic one
(`DescriptiveComplexity.FODefinable.ac0Definable` is the consumer).

It is stated at the level of the *sum* rather than as a map
`Language.order →ᴸ Language.arith` lifted by `LHom.sumMap`, deliberately:
`Language.order.Structure` is not an instance in Mathlib (it would fire on every
`LE`), so the generic `sumMap` instance would have to be fed a `letI`-supplied
structure at every use site, whereas the sum-level map has both structures
available by instance search.

## What is here, and what needs it

Besides the vocabulary and its semantics: the formula builders (`aLeF`, `aLtF`,
`aPlusF`, `aTimesF`, `aMaxF`, `aMinF`) with their realization lemmas, the
overflow characterization, and one worked sentence –
`DescriptiveComplexity.evenCardSentence`, which says that the universe has an
even number of elements, by reading the parity of the rank of its greatest
element. That sentence is what separates FO(≤) from AC⁰
(`DescriptiveComplexity.Problems.Even`), and it is the smallest example of the
one thing the numeric predicates buy over a bare order: access to the *size* of
the universe, one bit at a time.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The canonical interpretation on a finite linear order -/

section Structures

end Structures

/-! ### The symbols of the arithmetic expansion of a vocabulary -/

section Symbols

end Symbols

/-! ### The numeric predicates of the arithmetic expansion -/

section ExpansionSemantics

end ExpansionSemantics

/-! ### The transport of an ordered formula into the arithmetic expansion -/

section Transport

end Transport

/-! ### Formula builders -/

section Formulas

end Formulas

/-! ### Ranks, minima and covers

The order facts every walk over the ranks needs, stated once here because both
routes to a complexity bound use them: the induction of
`DescriptiveComplexity.ArithmeticFixedPoint` and the head programs of
`DescriptiveComplexity.HeadArith`. -/

section Ranks

variable {A : Type} [LinearOrder A] [Finite A]

/-- **A rank one higher is a cover**: the converse of
`DescriptiveComplexity.orank_covBy`, which is what lets a walk step a head by
choosing the element of the next rank. -/
theorem covBy_of_orank_succ {w z : A} (h : Lax895169.BitPredicate.orank z = Lax895169.BitPredicate.orank w + 1) : w ⋖ z := by
  refine ⟨lt_of_le_of_ne (orank_le_iff.mp (by omega)) (fun he => by rw [he] at h; omega), ?_⟩
  intro e h1 h2
  have := orank_lt_orank h1
  have := orank_lt_orank h2
  omega

/-- An element of positive rank has an immediate predecessor, of the rank
below. -/
theorem exists_pred_of_orank_succ {z : A} {k : ℕ} (h : Lax895169.BitPredicate.orank z = k + 1) :
    ∃ z' : A, Lax895169.BitPredicate.orank z' = k ∧ z' < z ∧ ∀ a : A, ¬(z' < a ∧ a < z) := by
  have hk : k < Nat.card A := by
    have := orank_lt_card z
    omega
  obtain ⟨z', hz'⟩ := exists_orank_eq (A := A) hk
  have hcov : z' ⋖ z := covBy_of_orank_succ (by omega)
  exact ⟨z', hz', hcov.lt, fun a ha => hcov.2 ha.1 ha.2⟩

end Ranks

/-! ### Truncation, and the size of the universe -/

section Truncation

end Truncation

/-! ### A sentence for the parity of the universe -/

section EvenCard

end EvenCard

end Lax280166Proofs.DescriptiveComplexity


