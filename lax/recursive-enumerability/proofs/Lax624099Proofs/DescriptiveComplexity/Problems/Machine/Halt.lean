/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.MachinesUnbounded
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.Halting.TMData
end Lax624099.Halting.TMData

namespace Lax904597.Machines.TMData
export Lax624099.Halting.TMData (AcceptsU)
end Lax904597.Machines.TMData

/-!
# HALT: the halting problem as a decision problem

*Does the machine described by the instance accept its input, in any number of
steps whatever, using as much tape as it likes?*

`Lax624099Proofs.DescriptiveComplexity.HALT` is the third acceptance notion of the same machine
data, beside `Lax624099Proofs.DescriptiveComplexity.NTMAccept` (a run bounded by the number of
positions, hence in NP) and `Lax624099Proofs.DescriptiveComplexity.NTMAcceptSpace` (a run of any
length on a tape indexed by the positions, hence in PSPACE). Dropping *both*
bounds leaves a certificate – the run – that is still a finite object but that
no function of the instance bounds, which is exactly the step from `Σ₁` to
`∃SO[new]`, and so from NP to RE.

The vocabulary, the machine record `Lax624099Proofs.DescriptiveComplexity.TMData` and its
well-formedness are reused unchanged; the tape is the unbounded strip of pages
of `Lax624099Proofs.DescriptiveComplexity.MachinesUnbounded`, whose docstring explains why the
cells are named by a page and an offset rather than by an integer. Acceptance
is nondeterministic, as for `Lax624099Proofs.DescriptiveComplexity.NTMAccept`: the membership
certificate guesses a run in any case.

## What this problem is for

Membership `HALT ∈ RE` is the *easy* half of the RE machine bridge, and it is
the half that pays: FINSAT is already RE-hard
(`Lax624099Proofs.DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`), so a proof that
the halting problem is `∃SO[new]`-definable yields a first-order reduction from
it to finite satisfiability with no further work – Trakhtenbrot's theorem in the
form it is usually stated. RE-*hardness* of `HALT`, the converse half, is the
machine bridge itself (`Lax624099Proofs.DescriptiveComplexity.halt_RE_hard`, in
`Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltHard`): with membership it makes
the halting problem RE-complete (`Lax624099Proofs.DescriptiveComplexity.halt_RE_complete`) and
undecidable (`Lax624099Proofs.DescriptiveComplexity.halt_not_computable`), stating “RE is the
class of semi-decidable problems” at the machine model as
`Lax624099Proofs.DescriptiveComplexity.mem_RE_iff_rePred` states it at the code model.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Problem

variable {A B : Type} [Lax904597.Machines.turing.Structure A] [Lax904597.Machines.turing.Structure B]

/-- **HALT**: does the machine described by the instance accept, with no bound
on the length of its run and none on the tape it uses? The well-formedness
promises of `Lax624099Proofs.DescriptiveComplexity.TMData.WellFormed` are folded into the
yes-instances, as for the two bounded acceptance problems. -/
def HALT : Lax904597.Problems.DecisionProblem Lax904597.Machines.turing where
  Holds := fun A inst => @Lax904597.Machines.TMData.WellFormed A (Lax904597.Machines.tmData A) ∧ @Lax624099.Halting.TMData.AcceptsU A (Lax904597.Machines.tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed h.acceptsU).symm

@[simp]
theorem halt_holds_iff (A : Type) [Lax904597.Machines.turing.Structure A] :
    HALT A ↔ (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).AcceptsU :=
  Iff.rfl

end Problem

end Lax624099Proofs.DescriptiveComplexity


