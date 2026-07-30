/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesUnbounded
import DescriptiveComplexity.Problems.Machine.Defs

/-!
# HALT: the halting problem as a decision problem

*Does the machine described by the instance accept its input, in any number of
steps whatever, using as much tape as it likes?*

`DescriptiveComplexity.HALT` is the third acceptance notion of the same machine
data, beside `DescriptiveComplexity.NTMAccept` (a run bounded by the number of
positions, hence in NP) and `DescriptiveComplexity.NTMAcceptSpace` (a run of any
length on a tape indexed by the positions, hence in PSPACE). Dropping *both*
bounds leaves a certificate – the run – that is still a finite object but that
no function of the instance bounds, which is exactly the step from `Σ₁` to
`∃SO[new]`, and so from NP to RE.

The vocabulary, the machine record `DescriptiveComplexity.TMData` and its
well-formedness are reused unchanged; the tape is the unbounded strip of pages
of `DescriptiveComplexity.MachinesUnbounded`, whose docstring explains why the
cells are named by a page and an offset rather than by an integer. Acceptance
is nondeterministic, as for `DescriptiveComplexity.NTMAccept`: the membership
certificate guesses a run in any case.

## What this problem is for

Membership `HALT ∈ RE` is the *easy* half of the RE machine bridge, and it is
the half that pays: FINSAT is already RE-hard
(`DescriptiveComplexity.finsat_hard_of_sigmaSONewDefinable`), so a proof that
the halting problem is `∃SO[new]`-definable yields a first-order reduction from
it to finite satisfiability with no further work – Trakhtenbrot's theorem in the
form it is usually stated. RE-*hardness* of `HALT`, the converse half, is the
machine bridge itself (`DescriptiveComplexity.halt_RE_hard`, in
`DescriptiveComplexity.Problems.Machine.HaltHard`): with membership it makes
the halting problem RE-complete (`DescriptiveComplexity.halt_RE_complete`) and
undecidable (`DescriptiveComplexity.halt_not_computable`), stating “RE is the
class of semi-decidable problems” at the machine model as
`DescriptiveComplexity.mem_RE_iff_rePred` states it at the code model.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Problem

variable {A B : Type} [Language.turing.Structure A] [Language.turing.Structure B]

/-- **HALT**: does the machine described by the instance accept, with no bound
on the length of its run and none on the tape it uses? The well-formedness
promises of `DescriptiveComplexity.TMData.WellFormed` are folded into the
yes-instances, as for the two bounded acceptance problems. -/
def HALT : DecisionProblem Language.turing where
  Holds := fun A inst => @TMData.WellFormed A (tmData A) ∧ @TMData.AcceptsU A (tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed h.acceptsU).symm

@[simp]
theorem halt_holds_iff (A : Type) [Language.turing.Structure A] :
    HALT A ↔ (tmData A).WellFormed ∧ (tmData A).AcceptsU :=
  Iff.rfl

end Problem

end DescriptiveComplexity
