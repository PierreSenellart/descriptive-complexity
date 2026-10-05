/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.Machines
import Lax535992Proofs.DescriptiveComplexity.Interpretation
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc TMBlank TMData TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing turingRel)
end FirstOrder.Language

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

namespace Lax535992Proofs.DescriptiveComplexity

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

/-- **Deterministic machine acceptance.** The same question with the extra
promise `DescriptiveComplexity.TMData.Deterministic` folded into the yes-instances,
exactly as the Horn condition is folded into `DescriptiveComplexity.HORNSAT`: the
table is functional, so the run is unique – the shape a least fixed point can
compute, which is what puts this problem in PTIME. -/
def DTMAccept : Lax904597.Problems.DecisionProblem Lax904597.Machines.turing where
  Holds := fun A inst => @Lax904597.Machines.TMData.WellFormed A (Lax904597.Machines.tmData A) ∧
    @Lax535992.DeterministicMachines.TMData.Deterministic A (Lax904597.Machines.tmData A) ∧ @Lax904597.Machines.TMData.Accepts A (Lax904597.Machines.tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed (and_congr h.deterministic h.accepts)).symm

end Problem

end Lax535992Proofs.DescriptiveComplexity


