/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.SecondOrderKromPull
import Lax480241Proofs.DescriptiveComplexity.Hierarchy
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

namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax485149.KromFragment (SigmaSOKromDefinable)
end Lax480241Proofs.DescriptiveComplexity

/-!
# NL, by the Krom fragment

**The class NL**: the problems definable in the Krom fragment SO-Krom of
existential second-order logic (`DescriptiveComplexity.SigmaSOKromDefinable`), which
captures nondeterministic logarithmic space on ordered structures ([Grädel
1992][gradel1992capturing]). This is the same move as defining `PTIME` by the
Horn fragment and NP by `Σ₁`-definability: the class is a *definition*, not an
axiom, and it is a bona fide `DescriptiveComplexity.ComplexityClass` because SO-Krom
definability is closed under (ordered) first-order reductions – the Krom shape
survives the pullback, see `DescriptiveComplexity.SecondOrderKromPull`.

NL is not a level of the polynomial hierarchy of `DescriptiveComplexity.Hierarchy`,
which is why it lives in its own file. What relates it to that hierarchy are
two theorems that are *not* free here:

* **`NL ⊆ PTIME`** has no syntactic route: a Krom kernel is not a Horn kernel
  (Horn clauses may be wide, Krom clauses may have two positive literals), so
  the inclusion is not an instance of “restrict the kernel further”. It goes
  through the complete problem instead, and is proved downstream with 2SAT
  (`DescriptiveComplexity.NL_subset_PTIME`, with `DescriptiveComplexity.NL_subset_NP` in its
  wake): 2SAT is in PTIME by a Horn program that guesses reachability in the
  implication graph and rejects, by a goal clause, the instances where a
  variable reaches its own negation and back.
* **`NL = coNL`** (Immerman–Szelepcsényi) is not the definitional duality that
  gives `PiP k` from `SigmaP k`: the complement of an SO-Krom definable problem
  is not obviously SO-Krom definable. It is a genuine theorem, and the reason
  the fixpoint logic FO(TC) is still wanted even once this fragment exists –
  the inductive-counting proof is naturally a statement about FO(TC), and that
  is where it is proved (`DescriptiveComplexity.TCDefinable.compl`), reaching this
  fragment through the two translations as `DescriptiveComplexity.NL_eq_coNL` in
  `DescriptiveComplexity.ImmermanSzelepcsenyi`.

Note that the *containment* `SO-Krom ⊆ NL` on the machine side already uses
Immerman–Szelepcsényi: satisfiability of a 2-CNF is the complement of a
reachability condition on the implication graph. Nothing in this library
depends on that, since NL is defined by the fragment rather than by a machine;
it is why the fragment is the right primitive here.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class NL**: the problems definable in the Krom fragment SO-Krom of
existential second-order logic, which captures nondeterministic logarithmic
space on ordered structures ([Grädel 1992][gradel1992capturing]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`); over a relational vocabulary it is the usual
notion, `DescriptiveComplexity.hard_NL_iff`. -/
noncomputable def NL : ComplexityClass :=
  .ofMem (fun P => Lax485149.KromFragment.SigmaSOKromDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSOKromDefinable_congr h)

end Lax480241Proofs.DescriptiveComplexity


