/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Computability.REPred
import Lax624099Proofs.DescriptiveComplexity.Computability.Reduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Lax624099Proofs.DescriptiveComplexity.Hierarchy
import Lax624099Proofs.DescriptiveComplexity.Machines
import Lax624099Proofs.DescriptiveComplexity.OrderWalk
import Lax624099Proofs.DescriptiveComplexity.Ordered
import Lax624099Proofs.DescriptiveComplexity.OrderedComposition
import Lax624099Proofs.DescriptiveComplexity.Padding
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.Membership
import Lax624099Proofs.DescriptiveComplexity.Problems.Sat.Tseitin
import Lax624099Proofs.DescriptiveComplexity.SecondOrder
import Lax624099Proofs.DescriptiveComplexity.SecondOrderPull
import Lax624099Proofs.DescriptiveComplexity.Vocabulary
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltMem
import Lax624099Proofs.DescriptiveComplexity.Problems.FinSat
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax904597.Problems.DecisionProblem
export Lax624099.ConcreteInstances.DecisionProblem (toPred)
end Lax904597.Problems.DecisionProblem

/-!
# The catalog's vocabularies, presented

The vocabularies of the two problems the machine bridge is about, exhibited as
`FirstOrder.Language.FinVocab`s, and the concrete reading of
`Lax624099Proofs.DescriptiveComplexity.RE_subset_rePred` at them:

* `Lax624099Proofs.DescriptiveComplexity.halt_rePred` – the halting problem, as a set of
  concrete machine instances, is recursively enumerable in Mathlib's sense;
* `Lax624099Proofs.DescriptiveComplexity.finsat_rePred` – likewise for finite satisfiability.

Both are instances of one theorem and neither needs anything problem-specific
beyond listing the symbols of the vocabulary: this is the point of encoding
structures once for the catalog rather than once per problem.

Neither statement says *undecidable*. That reading is supplied one file over,
by `Lax624099Proofs.DescriptiveComplexity.Computability.CodeHalt`: a known-undecidable set –
Mathlib's halting problem – maps computably into concrete instances of
`Lax624099Proofs.DescriptiveComplexity.CODEHALT`, whence
`Lax624099Proofs.DescriptiveComplexity.finsat_not_computable`, Trakhtenbrot's theorem outright.
The hypothetical form kept here,
`Lax624099Proofs.DescriptiveComplexity.finsat_not_computable_of_halt`, routes the same
conclusion through the *machine* model instead; its hypothesis is supplied by
`Lax624099Proofs.DescriptiveComplexity.halt_not_computable`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **The halting problem is recursively enumerable** in Mathlib's sense, on
the concrete machine instances of `FirstOrder.Language.FinStruct`.

This is `Lax624099Proofs.DescriptiveComplexity.halt_mem_RE` – a purely logical statement, an
`∃SO[new]` definition of acceptance – read through the encoding, with no
machine model on either side. -/
theorem halt_rePred : REPred (HALT.toPred Lax624099.ConcreteInstances.turingVocab) :=
  RE_subset_rePred Lax624099.ConcreteInstances.turingVocab HALT halt_mem_RE

/-- **Finite satisfiability is recursively enumerable** in Mathlib's sense: the
easy half of Trakhtenbrot's theorem, on concrete instances. -/
theorem finsat_rePred : REPred (FINSAT.toPred Lax624099.ConcreteInstances.finsatVocab) :=
  RE_subset_rePred Lax624099.ConcreteInstances.finsatVocab FINSAT finsat_mem_RE

end Lax624099Proofs.DescriptiveComplexity


