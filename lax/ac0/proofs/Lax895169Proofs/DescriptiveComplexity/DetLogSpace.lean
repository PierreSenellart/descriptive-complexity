/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.TransitiveClosurePull
import Lax895169Proofs.DescriptiveComplexity.ImmermanSzelepcsenyi
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

namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.DeterministicTransitiveClosure (DTCDefinable)
end Lax895169Proofs.DescriptiveComplexity

/-!
# LOGSPACE, by deterministic transitive closure

**The class LOGSPACE**: the problems definable in FO(DTC)
(`DescriptiveComplexity.DTCDefinable`), first-order logic with a *deterministic*
transitive-closure operator, which captures deterministic logarithmic space on
ordered structures ([Immerman 1987][immerman1987languages]). As everywhere in
this library the capture theorem is the *definition*: the class is what the
logic defines, no machine model is involved, and no axiom is added.

It is called `LOGSPACE` rather than `L` because `L` is the name this
development gives to a first-order vocabulary in almost every file.

## Why an operator, and not a fragment of ∃SO

`DescriptiveComplexity.PTIME` is defined by the Horn fragment and
`DescriptiveComplexity.NL` by the Krom fragment of existential second-order logic
([Grädel 1992][gradel1992capturing]). There is no comparable syntactic fragment
known for deterministic logarithmic space, so this class breaks the pattern: it
is defined by an operator-as-data logic (`DescriptiveComplexity.TCSpec` read
through `DescriptiveComplexity.TCSpec.det`) rather than by the shape of a kernel.
That it is nonetheless a bona fide `DescriptiveComplexity.ComplexityClass` is the
content of `DescriptiveComplexity.TransitiveClosurePull`: FO(DTC) definability is
closed under
(ordered) first-order reductions, the walk on the interpreted structure being a
walk on the base structure with the tags carried in the mode.

## Where it sits

`L ⊆ NL` (`DescriptiveComplexity.LOGSPACE_subset_NL`) is immediate at the level of
definability – a determinized specification is a specification – followed by
the FO(TC)/SO-Krom translation of `DescriptiveComplexity.ImmermanSzelepcsenyi`.
`DescriptiveComplexity.LOGSPACE_subset_PTIME` and
`DescriptiveComplexity.LOGSPACE_subset_NP` compose that with the inclusions of NL
(proved downstream, with 2SAT).

The canonical complete problem is REACHd, deterministic reachability, in
`DescriptiveComplexity.Problems.ReachabilityDet`; its complement UNREACHd is complete
too, and with it the class is closed under complement
(`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`, in
`DescriptiveComplexity.Problems.ReachabilityDet.Complement`) – with no analogue of
Immerman–Szelepcsényi needed, a deterministic walk being witnessed not to arrive
by a step budget.

What is *not* claimed, here as for the other classes: nothing relates this
class to a machine model. `L ≠ NL` and `L = NL` are both consistent with
everything proved here, and the containment `FO(DTC) ⊆ L` on the machine side –
the half of Immerman's theorem this definition replaces – is not formalized.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class LOGSPACE**: the problems definable in FO(DTC), first-order logic
with a deterministic transitive closure, which captures deterministic
logarithmic space on ordered structures ([Immerman
1987][immerman1987languages]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`); over a relational vocabulary it is the usual
notion, `DescriptiveComplexity.hard_LOGSPACE_iff`. -/
noncomputable def LOGSPACE : ComplexityClass :=
  .ofMem (fun P => Lax485149.DeterministicTransitiveClosure.DTCDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => dtcDefinable_congr h)

/-- Membership in LOGSPACE is exactly FO(DTC) definability, by definition. -/
theorem mem_LOGSPACE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : P ∈ LOGSPACE ↔ Lax485149.DeterministicTransitiveClosure.DTCDefinable P :=
  Iff.rfl

/-- **L ⊆ NL**: a deterministic walk is a walk, and FO(TC) definability is
membership in NL (`DescriptiveComplexity.tcDefinable_iff_mem_NL`, the two
translations through the Krom fragment). -/
theorem LOGSPACE_subset_NL : LOGSPACE ⊆ NL :=
  fun _ _ P hP => (tcDefinable_iff_mem_NL P).mp (DTCDefinable.tcDefinable hP)

end Lax895169Proofs.DescriptiveComplexity


