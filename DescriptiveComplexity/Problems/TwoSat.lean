/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.TwoSat.Defs
import DescriptiveComplexity.Problems.TwoSat.Membership
import DescriptiveComplexity.Problems.TwoSat.Hardness

/-!
# 2SAT is NL-complete

The width-two restriction of SAT (`DescriptiveComplexity.TwoSAT`) is complete for
`DescriptiveComplexity.NL`, the class defined by the Krom fragment of existential
second-order logic (`DescriptiveComplexity.SigmaSOKromDefinable`). This is the NL-level
analogue of HORN-SAT for PTIME and of SAT for NP, and like them it is
machine-free: both halves are first-order constructions over the fragment that
*defines* the class.

* Membership (`DescriptiveComplexity.twoSat_mem_NL`,
  `DescriptiveComplexity.Problems.TwoSat.Membership`): a Krom program that guesses the
  truth assignment and reads each input clause through a covering pair of
  occurrences. The width promise of 2SAT and the absence of an empty clause are
  enforced by *guards*, which are first-order over the input vocabulary – a
  promise costs one goal clause and no second-order machinery.
* Hardness (`DescriptiveComplexity.twoSat_hard_of_sigmaSOKromDefinable`,
  `DescriptiveComplexity.Problems.TwoSat.Hardness`): the Krom discharge, emitting one
  propositional 2-clause per clause of the program and per instantiation of its
  universally quantified variables satisfying its guard. The output is
  width-two by construction, exactly as the Horn discharge's output is Horn.

One thing is deliberately *not* claimed, as for HORN-SAT: **Grädel's capture
theorem against machines is not formalized.** That SO-Krom captures
nondeterministic logarithmic space on ordered structures ([Grädel
1992][gradel1992capturing]) has a direction that simulates a machine, and lies
outside a machine-model-free library; note also that its *easy* direction, `2SAT
∈ NL`, already needs Immerman–Szelepcsényi, since 2-satisfiability is the
complement of a reachability condition on the implication graph. So
`DescriptiveComplexity.NL` is *defined* as SO-Krom definability, exactly as
`DescriptiveComplexity.PTIME` is defined as SO-Horn definability.

Two consequences of this completeness theorem are not proved yet, both waiting
on 2SAT being placed in a *larger* class: `NL ⊆ PTIME` needs a Horn program for
implication-graph reachability (the inclusion has no syntactic route, a Krom
kernel not being a Horn kernel), and `NL ⊆ NP` needs the `Σ₁` definition of
2SAT. See `ROADMAP.md`.
-/

namespace DescriptiveComplexity

/-- **2SAT is NL-hard**, machine-free: every SO-Krom definable problem admits an
ordered first-order reduction to it. -/
theorem twoSat_NL_hard : NL.Hard TwoSAT :=
  (hard_NL_iff TwoSAT).mpr fun Q hQ =>
    (twoSat_hard_of_sigmaSOKromDefinable Q hQ).map OrderedFOReduction.toRel

/-- **2SAT is NL-complete.** Membership is `DescriptiveComplexity.twoSat_mem_NL` – the
Krom program that guesses a truth assignment and enforces the width promise by
a guard; hardness is `DescriptiveComplexity.twoSat_NL_hard`, the Krom discharge. This
is the NL-level analogue of the Cook–Levin theorem, and like it machine-free. -/
theorem TwoSAT_NL_complete : NL.Complete TwoSAT :=
  ⟨twoSat_mem_NL, twoSat_NL_hard⟩

end DescriptiveComplexity
