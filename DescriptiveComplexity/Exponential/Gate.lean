/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Simulate
import DescriptiveComplexity.Exponential.Trivialize
import DescriptiveComplexity.Exponential.Reach
import DescriptiveComplexity.HeadCapture

/-!
# The gate: `PSPACE = NL.exp`

The check on `DescriptiveComplexity.ComplexityClass.exp` at the one level where
this library independently knows the answer, in **both** directions.
`DescriptiveComplexity.PSPACE_subset_NL_exp` is the easy half: an
`DescriptiveComplexity.SOTCSpec` *is* the graph REACH reads on the expansion
whose points are its states. This file closes the converse, so that the operator
is pinned rather than merely bounded.

## The route

Nondeterministic logarithmic space read over an expanded universe is *machine*
space, and the machine is the one the library already captures
(`DescriptiveComplexity.tcDefinable_iff_automaton`): a finite control with `k`
two-way heads, each holding one point of the expansion. Three steps:

1. the walk witnessing `Q ∈ NL` is carried to the **trivialized** expansion
   (`DescriptiveComplexity.ExpExpansion.relSpec`), where every tagged assignment
   is a point and the old universe survives as a mark — so that a head's
   `succ` is the plain binary increment and never has to skip anything;
2. that walk is compiled into a two-way multi-head automaton
   (`DescriptiveComplexity.accepts_drvP`), whose tests are **quantifier-free by
   fiat**;
3. the automaton is simulated by a walk over the *base*
   (`DescriptiveComplexity.ExpExpansion.autoSpec`), a configuration being one
   assignment of one block.

Nothing in the chain evaluates a quantifier ranging over the expanded universe,
which is exactly the obstruction the translation lemma names.

## What is and is not a corollary

`LOGSPACE.exp ⊆ PSPACE` follows by monotonicity. The reverse inclusion does
**not**: `DescriptiveComplexity.SOTCDefinable.expDefinable` draws the graph of a
walk and then asks REACH of it, and REACH is not known to this library to be in
`DescriptiveComplexity.LOGSPACE`. `LOGSPACE.exp = PSPACE` would need the walk of
the expansion to be *functional* — a deterministic reachability argument, i.e.
Savitch read one exponential up — and is not claimed here.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- **`NL.exp ⊆ PSPACE`**: a problem that nondeterministic logarithmic space
decides over an exponentially larger definable universe is decided by a
polynomial-space walk over the base. The machine of the expansion holds `k` of
its points, a point is an assignment of a block, so a configuration of that
machine is one assignment of one block – a state of an
`DescriptiveComplexity.SOTCSpec`. -/
theorem NL_exp_subset_PSPACE : NL.exp ⊆ PSPACE := by
  rintro L _ P ⟨X, Q, hQ, hX⟩
  obtain ⟨spec, hspec⟩ := (tcDefinable_iff_mem_NL Q).mpr hQ
  refine ⟨ExpExpansion.autoSpec ((drvP (ExpExpansion.relSpec X spec)).compile false), ?_⟩
  intro A _ _ _ _
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  refine (hX A).trans ((hspec (X.Map A)).trans ?_)
  refine (ExpExpansion.accepts_relSpec (X := X) (spec := spec)).symm.trans ?_
  refine (accepts_drvP (ExpExpansion.relSpec X spec) (X.trivialize.Map A)).symm.trans ?_
  exact (ExpExpansion.accepts_autoSpec _ ExpExpansion.trivialize_domHolds).symm

/-- **`PSPACE = NL.exp`**: polynomial space *is* nondeterministic logarithmic
space read one exponential up. Both inclusions are theorems – the easy one is
`DescriptiveComplexity.PSPACE_subset_NL_exp` – so the exponential operator is
pinned at this level, not merely bounded. -/
theorem PSPACE_eq_NL_exp : PSPACE = NL.exp := by
  have hmem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (R : DecisionProblem L₀),
      SOTCDefinable R ↔ ExpDefinable NL R :=
    fun R => ⟨fun h => PSPACE_subset_NL_exp h, fun h => NL_exp_subset_PSPACE h⟩
  exact ComplexityClass.ext (fun R => hmem R) fun R => cofinalHard_congr_mem hmem R

/-- **`LOGSPACE.exp ⊆ PSPACE`**, by monotonicity. The reverse inclusion is not
claimed; see the module docstring. -/
theorem LOGSPACE_exp_subset_PSPACE : LOGSPACE.exp ⊆ PSPACE :=
  fun _ _ _ h => NL_exp_subset_PSPACE (ComplexityClass.exp_mono LOGSPACE_subset_NL h)

/-- **`NL.exp ⊆ EXPTIME` sharpened**: read through the gate, the inclusion
`DescriptiveComplexity.NL_exp_subset_EXPTIME` is just `PSPACE ⊆ EXPTIME`. -/
theorem NL_exp_eq_PSPACE : NL.exp = PSPACE :=
  PSPACE_eq_NL_exp.symm

end DescriptiveComplexity
