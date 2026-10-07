/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawGeom
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

/-!
# The layout's geometry is the padding layer's, so its formulas are written

The bridge the defining formulas of the EXPSPACE reduction are read through.
`DescriptiveComplexity.Padding` already carries the shape formulas every
tagged-tuple interpretation in this library needs – a coordinate is the least
element (`DescriptiveComplexity.botF`), a tuple is canonically padded
(`DescriptiveComplexity.canonF`), two tuples are equal
(`DescriptiveComplexity.eqTupF`), they agree below a length
(`DescriptiveComplexity.agreeF`), one is the padded reading of the other
through an index map (`DescriptiveComplexity.padTupF`) – each with its
realization lemma. The EXPSPACE layout speaks of the same objects under its own
names (`DescriptiveComplexity.Draw.pad`, `DescriptiveComplexity.Draw.unpad`,
`DescriptiveComplexity.Draw.IsPad`), and this file says they are the same:

* `DescriptiveComplexity.Draw.pad_eq_pad` and
  `DescriptiveComplexity.Draw.unpad_eq_pref` – the two paddings and the two
  readings are one definition;
* `DescriptiveComplexity.Draw.isPad_iff_canon` – being canonically padded *is*
  being canonical, once the designated `zero` is the order's least element,
  which is the choice a reduction into
  `DescriptiveComplexity.DWideAcceptSpace` makes anyway (an interpretation
  cannot name an arbitrary element, and the two designated ones have to be
  `⊥` and `⊤`);
* `DescriptiveComplexity.Draw.realize_canonF_isPad` and
  `DescriptiveComplexity.Draw.realize_padTupF_pad` – the two realizations in the
  layout's own vocabulary, which is the form the eleven defining formulas will
  cite.

So the *shape* half of the interpretation is already written. What is not, and
what the remaining work is, is the **rule** half: a transition's guard and what
it writes are arbitrary functions in
`DescriptiveComplexity.Draw.Rule`, and each kit owes a syntactic counterpart –
a quantifier-free formula over the payload slots for the guard, and per-slot
“copy this slot or write this constant” for the destination and the written
symbol.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section Geometry

variable {A : Type} {c dd : ℕ}

variable [PartialOrder A]

/-- **Being canonically padded is being canonical**, once the designated
element is a least one: `IsBot` and “equal to `zero`”
are the same condition on a coordinate, by antisymmetry. -/
theorem isPad_iff_canon {zero : A} (h₀ : IsBot zero) (v : Fin dd → A) :
    IsPad c zero v ↔ _root_.Lax822549Proofs.DescriptiveComplexity.Canon c v := by
  refine forall_congr' fun j => imp_congr Iff.rfl ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
    exact fun b => h₀ b
  · exact le_antisymm (h zero) (h₀ (v j))

end Geometry

/-! ### The two realizations, in the layout's own terms -/

section Realize

variable {L : Language.{0, 0}} {A : Type} [L.Structure A] [LinearOrder A]

variable {γ : Type} {dd : ℕ} {v : γ → A}

/-- **A tuple of the interpreted universe is canonically padded**, as a
formula: `DescriptiveComplexity.canonF` read at the layout's `IsPad`, with
the least element for `zero`. This is what the defining formula of a
transition, of an accepting state and of the blank all begin with – the
condition that gives an element one spelling, and so the emitted machine its
determinism. -/
theorem realize_canonF_isPad {zero : A} (h₀ : IsBot zero) {c : ℕ}
    {x : Fin dd → γ} :
    (_root_.Lax822549Proofs.DescriptiveComplexity.canonF (L := L) c x).Realize v ↔
      IsPad c zero fun j => v (x j) :=
  _root_.Lax822549Proofs.DescriptiveComplexity.realize_canonF.trans (isPad_iff_canon h₀ _).symm

end Realize

end Draw

end Lax822549Proofs.DescriptiveComplexity


