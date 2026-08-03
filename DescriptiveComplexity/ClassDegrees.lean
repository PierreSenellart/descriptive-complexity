/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Degree
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.Taut
import DescriptiveComplexity.Problems.HornSat
import DescriptiveComplexity.Problems.TwoSat
import DescriptiveComplexity.Problems.FinSat

/-!
# The logically defined classes are the degrees of their complete problems

Each class of this library with a complete problem `Q₀` *is* the degree of `Q₀`
(`DescriptiveComplexity.ComplexityClass.below`, the file
`DescriptiveComplexity.Degree`): `NP = below SAT`, `coNP = below TAUT`,
`PTIME = below HORNSAT`, `NL = below TwoSAT` and `RE = below FINSAT`. This is
the sanity check that the degree construction is the right one – and a theorem
rather than a tautology, since the two sides are defined completely
differently: on the left a logic, on the right a closure under reductions.

The payoff is that “`Q₀`-hardness is `𝒞`-hardness” stops being folklore: since
the classes are *equal*, so are their hardness predicates, whichever way a
given hardness proof was obtained.

Each proof supplies `DescriptiveComplexity.ComplexityClass.eq_below_of_complete`
with the class's own hardness discharge, which delivers the *non-relativized*
reduction `≤ᶠᵒ[≤]` that the equality needs – cofinal hardness on its own yields
only `≤ʳᶠᵒ[≤]`. This is why the statement cannot be proved generically, for an
arbitrary class and an arbitrary complete problem of it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **NP is the degree of SAT**: a problem is in NP exactly when it reduces to
SAT (Cook–Levin, read as an equality of classes). -/
theorem NP_eq_below_sat : NP = .below SAT :=
  ComplexityClass.eq_below_of_complete SAT sat_mem_NP
    (fun Q hQ => sat_hard_of_sigmaSODefinable Q hQ) fun _ => Iff.rfl

/-- **coNP is the degree of TAUT**. -/
theorem coNP_eq_below_taut : coNP = .below TAUT :=
  ComplexityClass.eq_below_of_complete TAUT taut_mem_coNP
    (fun Q hQ => taut_hard_of_piSODefinable Q hQ) fun _ => Iff.rfl

/-- **PTIME is the degree of HORN-SAT**. -/
theorem PTIME_eq_below_hornSat : PTIME = .below HORNSAT :=
  ComplexityClass.eq_below_of_complete HORNSAT hornSat_mem_PTIME
    (fun Q hQ => hornSat_hard_of_sigmaSOHornDefinable Q hQ) fun _ => Iff.rfl

/-- **NL is the degree of 2SAT**. -/
theorem NL_eq_below_twoSat : NL = .below TwoSAT :=
  ComplexityClass.eq_below_of_complete TwoSAT twoSat_mem_NL
    (fun Q hQ => twoSat_hard_of_sigmaSOKromDefinable Q hQ) fun _ => Iff.rfl

/-- **RE is the degree of FINSAT**: Trakhtenbrot's theorem, read as an equality
of classes. -/
theorem RE_eq_below_finsat : RE = .below FINSAT :=
  ComplexityClass.eq_below_of_complete FINSAT finsat_mem_RE
    (fun Q hQ => FinSat.finsat_hard_of_sigmaSONewDefinable Q hQ) fun _ => Iff.rfl

end DescriptiveComplexity
