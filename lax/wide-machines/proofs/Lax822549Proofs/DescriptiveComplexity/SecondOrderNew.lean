/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrderLift
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

namespace Lax822549Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax822549Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax822549Proofs.Foreign.FirstOrder.Language
end Lax822549Proofs.Foreign.FirstOrder.Language

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize SigmaSODefinable soLang)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Existential second-order logic with value invention

The logic `∃SO[new]` defining the class RE of recursively enumerable problems:
existential second-order logic whose relation variables range over a universe
*extended by finitely many invented values*, in the style of the
object-creating query languages of ([Abiteboul–Hull–Vianu 1995]
[abiteboul1995foundations], ch. 18).

Bounding the certificate by the instance is what keeps a second-order class
inside NP: a `Σ₁` sentence guesses relations over `A` itself, so the search
space is exponential in `|A|`. Value invention
removes exactly that bound and nothing else: the certificate is a finite
extension `A ⊕ Fin m` of the universe – with `m` *unbounded* – together with
relations over it, checked by a fixed first-order kernel. The witness is still
a finite object and the kernel is still decidable on a finite structure, so
the yes-instances are those found by an unbounded search over finite
witnesses: this is a logical definition of *recursive enumerability*, with no
machine model. (The converse inclusion, RE ⊆ `∃SO[new]`, is the
Trakhtenbrot-style encoding of an accepting run into invented values; it lives
with the machine bridge, not here.)

## The extended structure

An instance `A` and a number `m` of invented values determine an extended
structure over the vocabulary `DescriptiveComplexity.newLang L`, the base
vocabulary `L` together with one unary predicate `old`:

* its universe is `A ⊕ Fin m`;
* the symbols of `L` hold exactly where they hold in `A`, on original
  elements only – invented values are related to nothing
  (`DescriptiveComplexity.extBase`);
* `old` marks the original elements (`DescriptiveComplexity.IsOld`).

The vocabulary is relational, as every vocabulary of a
`DescriptiveComplexity.DecisionProblem` is, so invented values carry no
structure at all until the certificate's relations put some on them.

## Main definitions and results

* `DescriptiveComplexity.SigmaSONewDefinable`: definability by an `∃SO[new]`
  sentence – one existential second-order block over the extended universe and
  a first-order kernel, reusing the alternation machinery of
  `DescriptiveComplexity.SecondOrder` at a one-block list;
* `DescriptiveComplexity.extEquiv`: extended structures are functorial in the
  base isomorphism, so `∃SO[new]` expresses isomorphism-invariant properties;
* `DescriptiveComplexity.sigmaSONewDefinable_congr`: definability depends only
  on the finite instances of a problem;
* `DescriptiveComplexity.SigmaSODefinable.toNew`: `Σ₁ ⊆ ∃SO[new]`, by
  inventing nothing – the kernel is guarded by
  `DescriptiveComplexity.noNewSentence`, “every element is original”, which
  pins the number of invented values to zero. As a statement about classes this
  is `DescriptiveComplexity.NP_subset_RE`.

No alternation hierarchy is built on top of `∃SO[new]`, deliberately:
alternating second-order blocks over a *finite* extended universe are still
checked by an unbounded search over finite witnesses, so the levels would
collapse into RE rather than stack. (That collapse is a semantic remark, not a
theorem here: proving it inside the logic needs the same encoding as the
inclusion RE ⊆ `∃SO[new]`.)
-/

namespace FirstOrder

namespace Language

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- Relation symbols of the language marking the original elements inside an
extended universe. -/
inductive _root_.Lax822549Proofs.Foreign.FirstOrder.Language.oldRel : ℕ → Type
  /-- `old x`: the element `x` comes from the original structure, i.e., it is
  not an invented value. -/
  | old : Lax822549Proofs.Foreign.FirstOrder.Language.oldRel 1

end Language

end FirstOrder

namespace Lax822549Proofs.Derived

open FirstOrder FirstOrder.Language

deriving instance DecidableEq for Lax822549Proofs.Foreign.FirstOrder.Language.oldRel

end Lax822549Proofs.Derived

namespace FirstOrder

namespace Language

export Lax822549Proofs.Foreign.FirstOrder.Language (oldRel)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The one-symbol relational language marking, inside a universe extended
with invented values, the elements of the original structure. -/
protected def _root_.Lax822549Proofs.Foreign.FirstOrder.Language.oldMark : Language :=
  ⟨fun _ => Empty, Lax822549Proofs.Foreign.FirstOrder.Language.oldRel⟩

end Language

end FirstOrder

namespace Lax822549Proofs.Derived

open FirstOrder FirstOrder.Language

deriving instance IsRelational for Lax822549Proofs.Foreign.FirstOrder.Language.oldMark

end Lax822549Proofs.Derived

namespace FirstOrder

namespace Language

export Lax822549Proofs.Foreign.FirstOrder.Language (oldMark)

open Lax822549Proofs.Foreign.FirstOrder.Language in
/-- The symbol marking the original elements. -/
abbrev _root_.Lax822549Proofs.Foreign.FirstOrder.Language.oldSym : Lax822549Proofs.Foreign.FirstOrder.Language.oldMark.Relations 1 := .old

export Lax822549Proofs.Foreign.FirstOrder.Language (oldSym)

end Language

end FirstOrder

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The vocabulary of extended structures: the base vocabulary together with
the unary predicate `old` marking the elements of the original structure. -/
abbrev newLang (L : Language.{0, 0}) : Language := L.sum Lax822549Proofs.Foreign.FirstOrder.Language.oldMark

/-! ### The extended universe -/

section Extended

/-! ### Functoriality in the base structure -/

end Extended

/-! ### Definability

`SORealize` is reused at the one-block list `[B]`, so that an `∃SO[new]`
sentence is literally an `∃SO` sentence – over the extended vocabulary, read
in the extended structure. -/

section Definability

end Definability

/-! ### Inventing nothing

The `Σ₁` sentences are the `∃SO[new]` sentences that invent nothing: the
kernel is guarded by `DescriptiveComplexity.noNewSentence`, which forces the
extended universe to be the original one. -/

section NoNew

end NoNew

/-! ### `Σ₁ ⊆ ∃SO[new]` -/

end Lax822549Proofs.DescriptiveComplexity


