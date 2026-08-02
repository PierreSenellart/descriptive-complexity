/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.FixedPointPartialMachine

/-!
# Abiteboul–Vianu, the ordered case

On *ordered* structures, the inflationary and partial fixed-point logics have
the same expressive power exactly when polynomial time and polynomial space
coincide ([Abiteboul–Vianu 1989][abiteboul1989fixpoint]) – a corollary of the
two capture theorems, FO(≤, IFP) = PTIME
(`DescriptiveComplexity.ifpDefinable_iff_mem_PTIME`) and FO(≤, PFP) = PSPACE
(`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`), and mathematically
content-free once they are in place: each side of the equivalence is rewritten
through its capture.

The theorem proper – the same statement for the *order-free* logics
`DescriptiveComplexity.IFPDefinableFree` and
`DescriptiveComplexity.PFPDefinableFree`, where no capture is available and
the equivalence with `P = PSPACE` is the celebrated content – is the
Abiteboul–Vianu item of `ROADMAP.md` §4, with `ABITEBOUL-VIANU.md` (phases
F–G: the `≡ᵏ`-invariant layer) as its worked plan. This file is the honest
ordered milestone on that route, and the natural stopping point of the
capture half: it makes the remaining gap exactly «the unordered case».
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **Abiteboul–Vianu, ordered case**: the inflationary and partial
fixed-point logics agree on ordered structures exactly when `PTIME = PSPACE`.
A corollary of the two capture theorems; see the module docstring for what it
does *not* say (the unordered statement). -/
theorem ifpDefinable_eq_pfpDefinable_iff_ptime_eq_pspace :
    (∀ {L : Language.{0, 0}} (P : DecisionProblem L),
        IFPDefinable P ↔ PFPDefinable P) ↔ PTIME = PSPACE := by
  constructor
  · intro h
    have hMem : ∀ {L : Language.{0, 0}} (P : DecisionProblem L),
        SigmaSOHornDefinable P ↔ SOTCDefinable P := by
      intro L P
      constructor
      · intro hp
        exact ((h P).mp (SigmaSOHornDefinable.lfpDefinable hp).ifpDefinable).sotcDefinable
      · intro hp
        refine (lfpDefinable_iff_sigmaSOHornDefinable P).mp ((h P).mpr ?_).lfpDefinable
        exact (pfpDefinable_iff_mem_PSPACE P).mpr hp
    refine ComplexityClass.ext (fun P => hMem P) fun P => ?_
    constructor
    · intro hh L' _ S hS L'' Q hQ
      exact hh S hS Q ((hMem Q).mpr hQ)
    · intro hh L' _ S hS L'' Q hQ
      exact hh S hS Q ((hMem Q).mp hQ)
  · intro h L P
    constructor
    · exact IFPDefinable.pfpDefinable
    · intro hp
      have hspace : P ∈ PSPACE := mem_PSPACE_of_pfpDefinable hp
      have htime : SigmaSOHornDefinable P := by
        rw [← h] at hspace
        exact hspace
      exact (SigmaSOHornDefinable.lfpDefinable htime).ifpDefinable

end DescriptiveComplexity
