/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Program
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

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax480241Proofs.DescriptiveComplexity.TMData
end Lax480241Proofs.DescriptiveComplexity.TMData

namespace Lax480241Proofs.DescriptiveComplexity.TMData.UniqueFrom
end Lax480241Proofs.DescriptiveComplexity.TMData.UniqueFrom

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd TMData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# Runs of a deterministic machine, unbounded in time

The tool that makes the *converse* half of a space-bounded hardness proof free.

A reduction into `DescriptiveComplexity.DTMAcceptSpace` has to show both that a
yes-instance is accepted and that a no-instance is **not**. The second half is
usually a second induction – an invariant strong enough to rule out every run.
For a deterministic machine it is not needed: the configurations reachable from
one starting point are *linearly ordered* by reachability
(`DescriptiveComplexity.TMData.reach_total`, from Mathlib's
`Relation.ReflTransGen.total_of_right_unique` and
`DescriptiveComplexity.TMData.step_functional`), so it is enough to exhibit *one*
run, of the machine's own choosing, that ends badly.

Concretely, `DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` says: if
the initial configuration reaches a configuration that is stuck and not
accepting, and if accepting configurations are themselves stuck, then the
machine does not accept. Both side conditions are properties of the transition
table, so a reduction discharges them by inspection of its own program.

The hypothesis is not determinism but
`DescriptiveComplexity.TMData.UniqueFrom`: every configuration reachable from a
given one has at most one successor. That is what a program which **guesses in
one phase** and is deterministic after it has, and it is all the read-off lemmas
need – a reduction into a nondeterministic problem has to read its certificate
off an arbitrary accepting run, and this is what makes that a case analysis on
the guess rather than a second induction. Global determinism is the special case
(`DescriptiveComplexity.TMData.uniqueFrom_of_deterministic`).

Nothing here is about space: the statements hold for any `TMData` whose runs
are read with `Relation.ReflTransGen`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

variable (M) in
/-- **Determinism where it is used**: every configuration reachable from `c` has
at most one successor.

This is weaker than `DescriptiveComplexity.TMData.Deterministic` in exactly the
way a *guessing* program needs. A reduction into a nondeterministic problem has
to read its certificate off an arbitrary accepting run, and the way to survive
that is to guess in one phase and be deterministic everywhere after it: the
machine is then not deterministic at all, but it is unique from the
configuration the guess ends at, and every read-off below asks for no more. -/
def UniqueFrom (c : Lax904597.Machines.Config A) : Prop :=
  ∀ x y z : Lax904597.Machines.Config A, Relation.ReflTransGen M.Step c x → M.Step x y → M.Step x z → y = z

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (UniqueFrom)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- A deterministic machine is unique from anywhere. -/
theorem uniqueFrom_of_deterministic (hlin : Lax904597.Machines.IsLinOrd M.Le) (hdet : M.Deterministic)
    (c : Lax904597.Machines.Config A) : M.UniqueFrom c :=
  fun _ _ _ _ h₁ h₂ => step_functional hlin hdet h₁ h₂

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (uniqueFrom_of_deterministic)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A machine unique from `c` has one run out of `c`**: two configurations
reachable from it are reachable from one another. -/
theorem reach_total_of_uniqueFrom {c x y : Lax904597.Machines.Config A} (huniq : M.UniqueFrom c)
    (hx : Relation.ReflTransGen M.Step c x) (hy : Relation.ReflTransGen M.Step c y) :
    Relation.ReflTransGen M.Step x y ∨ Relation.ReflTransGen M.Step y x := by
  induction hx with
  | refl => exact Or.inl hy
  | @tail x' x hcx' hstep ih =>
    rcases ih with h | h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨e, he, hey⟩
      · exact Or.inr (Relation.ReflTransGen.single hstep)
      · exact Or.inl ((huniq x' e x hcx' he hstep) ▸ hey)
    · exact Or.inr (h.tail hstep)

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (reach_total_of_uniqueFrom)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- Nothing is reachable from a stuck configuration but itself. -/
theorem eq_of_reach_stuck {c d : Lax904597.Machines.Config A} (hstuck : ∀ e, ¬M.Step c e)
    (h : Relation.ReflTransGen M.Step c d) : c = d := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨e, he, -⟩
  · exact heq
  · exact absurd he (hstuck e)

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (eq_of_reach_stuck)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A run into a dead end is not an accepting one**, at a machine unique from
where the run starts. This is the form a guessing program uses: the guess phase
is the only nondeterministic one, so what has to be ruled out is an accepting run
*of the same guess*, and that is a statement about one deterministic remainder.

`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` is this with the
uniqueness supplied by global determinism and the initial configuration matched
up. -/
theorem not_acc_of_reaches_dead_of_uniqueFrom {c₀ d : Lax904597.Machines.Config A} (huniq : M.UniqueFrom c₀)
    (hreach : Relation.ReflTransGen M.Step c₀ d)
    (hdead : ∀ e, ¬M.Step d e) (hnacc : ¬M.Acc d.state)
    (hsink : ∀ e : Lax904597.Machines.Config A, M.Acc e.state → ∀ e', ¬M.Step e e')
    {c : Lax904597.Machines.Config A} (hr : Relation.ReflTransGen M.Step c₀ c) (hacc : M.Acc c.state) :
    False := by
  rcases reach_total_of_uniqueFrom huniq hreach hr with h | h
  · exact hnacc ((eq_of_reach_stuck hdead h) ▸ hacc)
  · exact hnacc ((eq_of_reach_stuck (hsink c hacc) h) ▸ hacc)

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (not_acc_of_reaches_dead_of_uniqueFrom)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A deterministic machine that runs into a dead end does not accept.**

The run exhibited by `hreach` is *the* run, so an accepting configuration would
have to lie on it – before the dead end, and then it would have to be the dead
end itself since an accepting configuration is stuck, or after it, and then it
would be the dead end because nothing follows a dead end. Either way the dead
end is accepting, which it is not. -/
theorem not_acceptsSpace_of_reaches_dead (hwf : M.WellFormed) (hdet : M.Deterministic)
    {c₀ d : Lax904597.Machines.Config A} (hinit : M.IsInit c₀) (hreach : Relation.ReflTransGen M.Step c₀ d)
    (hdead : ∀ e, ¬M.Step d e) (hnacc : ¬M.Acc d.state)
    (hsink : ∀ e : Lax904597.Machines.Config A, M.Acc e.state → ∀ e', ¬M.Step e e') :
    ¬M.AcceptsSpace := by
  rintro ⟨c₀', c, hinit', hr, hacc⟩
  obtain rfl : c₀' = c₀ := isInit_unique hwf hdet.1 hinit' hinit
  exact not_acc_of_reaches_dead_of_uniqueFrom
    (uniqueFrom_of_deterministic hwf.1 hdet _) hreach hdead hnacc hsink hr hacc

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (not_acceptsSpace_of_reaches_dead)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-! ### A machine that never halts

The other way a no-instance is discharged, and the one a machine with no clock
needs: instead of *one* run that ends badly, an unbounded *chain* of runs that
never ends. A halted configuration is reached in a fixed number of steps, so a
chain whose `n`-th link costs at least `n` of them reaches none. -/

omit [Finite A] in
/-- **The positive half**, for symmetry: a run from the initial configuration
to an accepting one is exactly what acceptance in bounded space asks for. -/
theorem acceptsSpace_of_reaches_acc {c₀ d : Lax904597.Machines.Config A} (hinit : M.IsInit c₀)
    (hreach : Relation.ReflTransGen M.Step c₀ d) (hacc : M.Acc d.state) :
    M.AcceptsSpace :=
  ⟨c₀, d, hinit, hreach, hacc⟩

end TMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax480241Proofs.DescriptiveComplexity.TMData (acceptsSpace_of_reaches_acc)

end Lax904597.Machines.TMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

end TMData

end Lax480241Proofs.DescriptiveComplexity


