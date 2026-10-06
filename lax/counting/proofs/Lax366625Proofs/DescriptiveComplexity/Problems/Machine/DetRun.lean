/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.Program
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

namespace Lax366625Proofs.DescriptiveComplexity.TMData
end Lax366625Proofs.DescriptiveComplexity.TMData

namespace Lax366625Proofs.DescriptiveComplexity.TMData.UniqueFrom
end Lax366625Proofs.DescriptiveComplexity.TMData.UniqueFrom

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd TMData)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
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

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (UniqueFrom)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- A deterministic machine is unique from anywhere. -/
theorem uniqueFrom_of_deterministic (hlin : Lax904597.Machines.IsLinOrd M.Le) (hdet : M.Deterministic)
    (c : Lax904597.Machines.Config A) : M.UniqueFrom c :=
  fun _ _ _ _ h₁ h₂ => step_functional hlin hdet h₁ h₂

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (uniqueFrom_of_deterministic)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (reach_total_of_uniqueFrom)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

omit [Finite A] in
/-- **A deterministic machine has one run**: two configurations reachable from
the same starting point are reachable from one another. -/
theorem reach_total (hlin : Lax904597.Machines.IsLinOrd M.Le) (hdet : M.Deterministic) {c x y : Lax904597.Machines.Config A}
    (hx : Relation.ReflTransGen M.Step c x) (hy : Relation.ReflTransGen M.Step c y) :
    Relation.ReflTransGen M.Step x y ∨ Relation.ReflTransGen M.Step y x :=
  reach_total_of_uniqueFrom (uniqueFrom_of_deterministic hlin hdet c) hx hy

end TMData

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (reach_total)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax366625Proofs.DescriptiveComplexity.TMData (eq_of_reach_stuck)

end Lax904597.Machines.TMData

namespace Lax366625Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : Lax904597.Machines.TMData A}

/-! ### A machine that never halts

The other way a no-instance is discharged, and the one a machine with no clock
needs: instead of *one* run that ends badly, an unbounded *chain* of runs that
never ends. A halted configuration is reached in a fixed number of steps, so a
chain whose `n`-th link costs at least `n` of them reaches none. -/

end TMData

end Lax366625Proofs.DescriptiveComplexity


