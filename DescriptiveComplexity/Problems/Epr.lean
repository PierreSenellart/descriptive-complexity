/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Epr.Defs
import DescriptiveComplexity.Problems.Epr.Small
import DescriptiveComplexity.Problems.Epr.Membership

/-!
# EPR, the umbrella

Satisfiability of an `∃*∀*` sentence – the Bernays–Schönfinkel–Ramsey class:
the instance encoding and its semantics
(`DescriptiveComplexity.Problems.Epr.Defs`), the small-model property
(`DescriptiveComplexity.Problems.Epr.Small`) and the membership in NEXPTIME
(`DescriptiveComplexity.Problems.Epr.Membership`).

The two halves of the membership are the two halves of the classical argument:
a satisfiable `∃*∀*` sentence has a model on the instance itself, and checking
such a model is one `Σ₁` sentence read over an expansion whose points are the
*relations* on the instance – an assignment of the universal variables being one
of them. Hardness is not formalized yet.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- **Satisfiability of an `∃*∀*` sentence is in NEXPTIME.** -/
theorem epr_mem_NEXPTIME : EPR ∈ NEXPTIME := Epr.epr_mem_NEXPTIME

end DescriptiveComplexity
