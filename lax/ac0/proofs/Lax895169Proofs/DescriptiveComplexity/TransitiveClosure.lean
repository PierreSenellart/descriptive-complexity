/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.Ordered
import Lax895169Proofs.DescriptiveComplexity.Complexity
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

namespace Lax485149.TransitiveClosure
end Lax485149.TransitiveClosure

namespace Lax895169Proofs.DescriptiveComplexity.TCSpec
end Lax895169Proofs.DescriptiveComplexity.TCSpec

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.TransitiveClosure (TCDefinable TCSpec)
end Lax895169Proofs.DescriptiveComplexity

/-!
# FO(TC): first-order logic with transitive closure

The logic that captures nondeterministic logarithmic space on ordered
structures ([Immerman 1987][immerman1987languages]): first-order logic extended
with a *transitive-closure* operator. If `φ(x̄, ȳ)` defines a binary relation on
`k`-tuples, then `TC[x̄, ȳ. φ](ū, v̄)` says that `v̄` is reachable from `ū` in the
`φ`-graph.

## The operator as data

As everywhere in this library, the operator is *not* added to Mathlib's
`FirstOrder.Language.BoundedFormula` as a new constructor – that would mean
redoing relabeling, substitution and realization for an extended syntax, and
losing every existing lemma. It is kept at the Lean level instead: a
`DescriptiveComplexity.TCSpec` bundles the arity `k`, a *first-order* transition
formula over the ordered expansion with two `k`-tuples of free variables, and
the two endpoint formulas; reachability itself is `Relation.ReflTransGen`,
whose induction principles then do the work in proofs. This is the same move as
`DescriptiveComplexity.HornProgram` for SO-Horn and `DescriptiveComplexity.KromProgram` for
SO-Krom.

A single application of `TC` in front of a first-order matrix is not a
restriction on ordered structures: Immerman's normal form makes every
FO(posTC) formula equivalent to one, just as a single existential block
suffices for `DescriptiveComplexity.SigmaSODefinable`. The library takes that normal
form as the *definition* (`DescriptiveComplexity.TCDefinable`), exactly as it takes
`Σ₁`-definability as the definition of NP rather than proving Fagin's theorem
against a machine.

## What this is for

`DescriptiveComplexity.NL` is already defined, by the Krom fragment
(`DescriptiveComplexity.LogSpace`), and the two coincide
(`DescriptiveComplexity.tcDefinable_iff_mem_NL`), so FO(TC) is not set up as a
second complexity class; the modes are what would make that possible, should it
become useful. A walk whose state were only a tuple of elements could not be
pulled back through an interpretation, whose tags vary from node to node, and
could not carry the finite data a translation needs (the atom index and sign of
a literal, say); carrying it in coordinates would fail on a one-element
universe. FO(TC) is here as the logic in which two things are naturally stated:

* the translation to the Krom fragment, which goes through the *complement* –
  a clausal fragment states closure and rejection, so it defines
  non-reachability head-on, exactly as `DescriptiveComplexity.unreach_mem_NL` does for
  the concrete case;
* **Immerman–Szelepcsényi**, closure of FO(TC) under complement
  (`DescriptiveComplexity.TCDefinable.compl` in
  `DescriptiveComplexity.TransitiveClosureCompl`), whose inductive-counting proof is a
  walk on configurations – a phase, a flag and eight registers, each a node or
  a count – and so lives inside a single `TC`. That theorem turns the above
  translation into an equivalence and gives `REACH ∈ NL`.

The canonical example is `DescriptiveComplexity.reach_tcDefinable` – REACH *is* a `TC`,
at arity one and with a single mode, over the edge relation between the marked
sources and the marked targets.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-! ### Specifications -/

attribute [instance] Lax485149.TransitiveClosure.TCSpec.modeFinite

namespace TCSpec

section Semantics

variable (spec : Lax485149.TransitiveClosure.TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

end Iso

end TCSpec

/-! ### FO(TC) definability -/

end Lax895169Proofs.DescriptiveComplexity


