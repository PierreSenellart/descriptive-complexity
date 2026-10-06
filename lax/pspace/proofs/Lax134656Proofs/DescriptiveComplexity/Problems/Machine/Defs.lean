/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Machines
import Lax134656Proofs.DescriptiveComplexity.Interpretation
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc TMBlank TMData TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax134656Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing turingRel)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

/-!
# Machine acceptance as a decision problem

The vocabulary of the machine bridge, and the problem the bridge is about: a
nondeterministic Turing machine is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.NTMAccept`, an ordinary iso-invariant problem of the catalog.
The semantics it reads is `DescriptiveComplexity.TMData`, defined without a vocabulary
in `DescriptiveComplexity.Machines`.

## The vocabulary

`FirstOrder.Language.turing` carries, following design decision (a) of the
plan, **no relation of arity above two**: a transition is an *element* `τ` of
the universe with four binary attributes `tsrc`/`tread`/`tdst`/`twrite` and a
unary mark `right`, rather than a single 5-ary symbol. An
`FOInterpretation` supplies one defining formula per tuple of tags, so a 5-ary
symbol would mean `|Tag|⁵` formula cases; keeping every symbol binary keeps the
reductions of stages 3 and 4 in the regime the rest of the catalog lives in.

Positions are both tape cells and time steps (design decision (b)), so the
budget of `DescriptiveComplexity.TMData.Accepts` is unary by construction and no
arithmetic is needed anywhere.

## Well-formedness

Being a linear order is not automatic for a relation symbol, so – exactly as
`DescriptiveComplexity.IsLinOrd` for Knapsack, and `WidthAtMostThree` for 3SAT – it is
folded into the yes-instances, together with the other promises of
`DescriptiveComplexity.TMData.WellFormed`. All of them are first-order, so the `Σ₁`
kernel of the membership proof can check them.

## Why there are no state and symbol sorts

The vocabulary marks positions (`posn`) and transitions (`tr`) and nothing else.
Sorts of states and of symbols are omitted because nothing in the semantics or
in the membership proof reads them: a junk element is harmless as a state, since
it is reachable only through a transition, and a reduction controls which
elements it marks accepting. Should a construction want them, adding a unary
symbol is a local change to this file and to the well-formedness predicate.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax904597.Machines.turing.Structure A]

end Shorthands

/-! ### The problem -/

section Problem

variable {A B : Type} [Lax904597.Machines.turing.Structure A] [Lax904597.Machines.turing.Structure B]

/-- **An isomorphism makes the two machines agree.** Every symbol of the
vocabulary transports, which is all `DescriptiveComplexity.TMData.Agree` asks for. -/
theorem agree_of_equiv (e : A ≃[Lax904597.Machines.turing] B) :
    (Lax904597.Machines.tmData B).Agree e.symm.toEquiv (Lax904597.Machines.tmData A) := by
  have h1 : ∀ (r : Lax904597.Machines.turing.Relations 1) (b : B),
      (RelMap r ![b] : Prop) ↔ RelMap r ![(e.symm b : A)] := fun r b => by
    have h := relMap_equiv₁ e r (e.symm b)
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h
    exact h.symm
  have h2 : ∀ (r : Lax904597.Machines.turing.Relations 2) (b b' : B),
      (RelMap r ![b, b'] : Prop) ↔ RelMap r ![(e.symm b : A), (e.symm b' : A)] := fun r b b' => by
    have h := relMap_equiv₂ e r (e.symm b) (e.symm b')
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b,
      show (e (e.symm b') : B) = b' from e.toEquiv.apply_symm_apply b'] at h
    exact h.symm
  exact ⟨fun b => h1 Lax904597.Machines.tmPosn b, fun b b' => h2 Lax904597.Machines.tmLe b b', fun b => h1 Lax904597.Machines.tmTr b,
    fun b => h1 Lax904597.Machines.tmStart b, fun b => h1 Lax904597.Machines.tmAcc b, fun b => h1 Lax904597.Machines.tmBlank b, fun b => h1 Lax904597.Machines.tmRight b,
    fun b b' => h2 Lax904597.Machines.tmSrc b b', fun b b' => h2 Lax904597.Machines.tmRead b b', fun b b' => h2 Lax904597.Machines.tmDst b b',
    fun b b' => h2 Lax904597.Machines.tmWrite b b', fun b b' => h2 Lax904597.Machines.tmInp b b'⟩

/-- **Machine acceptance in bounded space**: the same question as
`DescriptiveComplexity.NTMAccept` with the step bound dropped. Nothing else
changes – the tape is indexed by the positions, so the space a machine may use
is bounded by construction and a reduction of dimension `d` buys `nᵈ` cells
exactly as it buys `nᵈ` steps – but a run may now visit exponentially many
configurations, so acceptance is reachability in the configuration graph. -/
def NTMAcceptSpace : Lax904597.Problems.DecisionProblem Lax904597.Machines.turing where
  Holds := fun A inst => @Lax904597.Machines.TMData.WellFormed A (Lax904597.Machines.tmData A) ∧ @Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace A (Lax904597.Machines.tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed h.acceptsSpace).symm

/-- **Deterministic machine acceptance in bounded space**, with determinism
folded into the yes-instances as in `DescriptiveComplexity.DTMAccept`. That this
problem and `DescriptiveComplexity.NTMAcceptSpace` are complete for the same class
is the content of `PSPACE = NPSPACE`. -/
def DTMAcceptSpace : Lax904597.Problems.DecisionProblem Lax904597.Machines.turing where
  Holds := fun A inst => @Lax904597.Machines.TMData.WellFormed A (Lax904597.Machines.tmData A) ∧
    @Lax535992.DeterministicMachines.TMData.Deterministic A (Lax904597.Machines.tmData A) ∧ @Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace A (Lax904597.Machines.tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)).symm

end Problem

end Lax134656Proofs.DescriptiveComplexity


