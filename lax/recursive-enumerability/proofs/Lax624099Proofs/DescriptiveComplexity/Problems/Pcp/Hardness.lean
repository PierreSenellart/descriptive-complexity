/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Problems.Pcp.Hardness.Interp
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.Halt
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

/-!
# The halting problem reduces to Post's correspondence problem

**`Lax624099Proofs.DescriptiveComplexity.halt_ordered_fo_reduction_pcp`**: the classical
computation-history dominoes, as an ordered first-order reduction
`HALT ≤ᶠᵒ[≤] PCP`. The machine of the instance is *data*, so the reduction
writes one rule domino per combination of transition attributes, the copy and
bookkeeping dominoes beside them, and the initial configuration – the input
page between two endmarkers, with a boot letter in the state slot – as the one
long word of the start domino.

The construction is layered below this file:

* `Problems/Pcp/Hardness/History.lean` – dominoes decide derivability, for any
  string-rewriting system with nonempty rule sides;
* `Problems/Pcp/Hardness/ConfigWord.lean` – the rewriting system of a machine
  on the unbounded tape: derivability of the halting word is acceptance;
* `Problems/Pcp/Hardness/Draw.lean` – the elements and word tables of the
  drawn PCP instance;
* `Problems/Pcp/Hardness/Match.lean` – an instance reading as the drawing has
  a match exactly when the machine accepts;
* `Problems/Pcp/Hardness/Interp.lean` – the defining formulas realize the
  drawing.

With `Lax624099Proofs.DescriptiveComplexity.pcp_mem_RE` this makes PCP RE-complete as soon as
`HALT` is RE-hard, which is `Lax624099Proofs.DescriptiveComplexity.halt_RE_hard`
(`Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltHard`).
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open scoped Lax624099Proofs.DescriptiveComplexity

/-- **`HALT ≤ᶠᵒ[≤] PCP`**: the computation-history dominoes of the machine
described by the instance. -/
noncomputable def halt_ordered_fo_reduction_pcp : HALT ≤ᶠᵒ[≤] PCP where
  Tag := HaltPcp.PTag
  dim := 5
  toInterpretation := HaltPcp.haltPcpInterp
  correct A _ _ _ _ := (HaltPcp.pcp_map_iff A).symm

end Lax624099Proofs.DescriptiveComplexity


