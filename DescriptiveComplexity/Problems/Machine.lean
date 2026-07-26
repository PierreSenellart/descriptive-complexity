/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Problems.Machine.Walk
import DescriptiveComplexity.Problems.Machine.Membership

/-!
# Machine acceptance (the machine bridge, in progress)

Umbrella file for `DescriptiveComplexity.NTMAccept`, the problem “does this
nondeterministic Turing machine accept its input within as many steps as there
are positions?”, with the machine carried by the instance.

The point of the problem is the bridge described in `MACHINE.md`: every class in
this library is a definition in logic and every completeness theorem is
discharged by a first-order reduction, so that these classes really are *the*
NP and *the* P is, as the development stands, a citation. Proving `NTMAccept`
NP-complete closes that gap from inside the framework.

What is here so far is stage 1 of that plan: the semantics
(`DescriptiveComplexity.Machines`), the vocabulary, the problem and its
isomorphism-invariance, and the bridge
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` between an `ℕ`-indexed run and
one indexed by the position elements – which is the form a first-order kernel
can talk about, and where the unary time bound is cashed in. Still to come, in
order:

* `NTMAccept ∈ NP` – guess that walk as three relations indexed by the
  positions and check the tableau clauses first-order (*in progress*, see
  `DescriptiveComplexity.Problems.Machine.Membership`);
* `SAT ≤ᶠᵒ[≤] NTMAccept` – a bespoke machine built inside a SAT instance;
* and the two characterizations `mem_NP_iff_le_ntmAccept` and its `PTIME`
  analogue.

As with any complexity-theoretic statement, these results are about finite
structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/
