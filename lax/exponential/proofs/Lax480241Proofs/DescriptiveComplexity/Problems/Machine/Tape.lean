/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Program
import Lax480241Proofs.DescriptiveComplexity.OrderedComposition
import Mathlib.Data.Fintype.Lattice
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax480241Proofs.DescriptiveComplexity

/-!
# The tape of the SAT machine

The layout half of `SAT ≤ᶠᵒ[≤] NTMAccept`: which tagged tuples are positions, in
what order they sit, and why there are enough of them. The program that runs on
this tape – states, symbols, transitions – is separate.

## The layout

The machine's tape is one cell per element of the instance, bracketed by two
markers, followed by filler cells that exist only to supply time:

```
  ⊢   x₁ x₂ … xₙ   ⊣   fillers…
```

`Satisfiable` assigns a truth value to *every* element (elements that are not
variables of any clause are harmless), so there is no need to single out the
variables: one cell per element is both simpler and correct.

Tags are ordered so that this is exactly the order of the interpreted universe.
That order comes for free: `DescriptiveComplexity.lexLeF` is the defining formula of
`le` – tags first, then the tuple lexicographically – and
`DescriptiveComplexity.tagTupleOrder` is already a `LinearOrder`, so the well-formedness
obligation `IsLinOrd` of `DescriptiveComplexity.TMData.WellFormed` is discharged without
a single tag-pair case.

Only the *position* tags are fixed here. The symbol, state and transition tags
of the program get higher indices, which leaves the order of the positions
undisturbed – `DescriptiveComplexity.satTagIdx` is what has to stay monotone, not the
constructor list.

## The budget

The machine needs one sweep to guess an assignment and one sweep per clause to
check it, so `(m + 1) · (n + 2)` steps for `n` elements and `m ≤ n` clauses.
Eight filler tags at dimension two give `8n²` positions on their own – no need
to count the markers and cells – and `DescriptiveComplexity.sat_budget` says that is
always more than the machine needs. The filler is over-provisioned rather than
the bound tightened: nothing downstream depends on the constant, and an
off-by-one here would only surface at the very end of the correctness proof.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

/-! ### The tags of the positions -/

/-! ### The intended positions

Stated as a plain predicate on tagged tuples, in the style of
`DescriptiveComplexity.IAdjRaw`: the interpretation's `posn` formula will be shown to
realize exactly this, and every fact proved here transfers. -/

section Positions

variable {A : Type} [LinearOrder A]

/-! ### The instance data of the machine

The order, the blank symbol and the initial tape – everything
`DescriptiveComplexity.TMData.WellFormed` asks about, which is therefore discharged here
once, before any transition exists. -/

/-- The tuple of minima: the coordinates a marker or a constant symbol is
pinned to, so that exactly one tuple carries such a tag. -/
def IsMinTup (w : Fin 2 → A) : Prop := (∀ a : A, w 0 ≤ a) ∧ ∀ a : A, w 1 ≤ a

theorem isMinTup_unique {w w' : Fin 2 → A} (h : IsMinTup w) (h' : IsMinTup w') : w = w' := by
  funext i
  fin_cases i
  · exact le_antisymm (h.1 _) (h'.1 _)
  · exact le_antisymm (h.2 _) (h'.2 _)

variable [Finite A] [Nonempty A]

theorem exists_isMinTup : ∃ w : Fin 2 → A, IsMinTup w := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  exact ⟨fun _ => m, hm, hm⟩

end Positions

/-! ### The budget -/

end Lax480241Proofs.DescriptiveComplexity


