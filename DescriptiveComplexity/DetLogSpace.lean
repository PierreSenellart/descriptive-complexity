/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosurePull
import DescriptiveComplexity.ImmermanSzelepcsenyi

/-!
# LOGSPACE, by deterministic transitive closure

**The class LOGSPACE**: the problems definable in FO(DTC)
(`DescriptiveComplexity.DTCDefinable`), first-order logic with a *deterministic*
transitive-closure operator, which captures deterministic logarithmic space on
ordered structures ([Immerman 1987][immerman1987languages]). As everywhere in
this library the capture theorem is the *definition*: the class is what the
logic defines, no machine model is involved, and no axiom is added.

It is called `LOGSPACE` rather than `L` because `L` is the name this
development gives to a first-order vocabulary in almost every file.

## Why an operator, and not a fragment of ∃SO

`DescriptiveComplexity.PTIME` is defined by the Horn fragment and
`DescriptiveComplexity.NL` by the Krom fragment of existential second-order logic
([Grädel 1992][gradel1992capturing]). There is no comparable syntactic fragment
known for deterministic logarithmic space, so this class breaks the pattern: it
is the first one here defined by an operator-as-data logic
(`DescriptiveComplexity.TCSpec` read through
`DescriptiveComplexity.TCSpec.det`) rather than by the shape of a kernel. That it is
nonetheless a bona fide `DescriptiveComplexity.ComplexityClass` is the content of
`DescriptiveComplexity.TransitiveClosurePull`: FO(DTC) definability is closed under
(ordered) first-order reductions, the walk on the interpreted structure being a
walk on the base structure with the tags carried in the mode.

## Where it sits

`L ⊆ NL` (`DescriptiveComplexity.LOGSPACE_subset_NL`) is immediate at the level of
definability – a determinized specification is a specification – followed by
the FO(TC)/SO-Krom translation of `DescriptiveComplexity.ImmermanSzelepcsenyi`.
Composing with `DescriptiveComplexity.NL_subset_PTIME` (proved downstream, with
2SAT) places it inside polynomial time as well.

The canonical complete problem is REACHd, deterministic reachability, in
`DescriptiveComplexity.Problems.ReachabilityDet`.

What is *not* claimed, here as for the other classes: nothing relates this
class to a machine model. `L ≠ NL` and `L = NL` are both consistent with
everything proved here, and the containment `FO(DTC) ⊆ L` on the machine side –
the half of Immerman's theorem this definition replaces – is not formalized.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class LOGSPACE**: the problems definable in FO(DTC), first-order logic
with a deterministic transitive closure, which captures deterministic
logarithmic space on ordered structures ([Immerman
1987][immerman1987languages]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`); over a relational vocabulary it is the usual
notion, `DescriptiveComplexity.hard_LOGSPACE_iff`. -/
noncomputable def LOGSPACE : ComplexityClass where
  Mem P := DTCDefinable P
  Hard P := CofinalHard (fun Q => DTCDefinable Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  hard_of_relOrderedReduction f hP := CofinalHard.of_relOrderedReduction f hP
  mem_congr_finite h := dtcDefinable_congr h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-- Membership in LOGSPACE is exactly FO(DTC) definability, by definition. -/
theorem mem_LOGSPACE_iff (P : DecisionProblem L) : P ∈ LOGSPACE ↔ DTCDefinable P :=
  Iff.rfl

/-- Over a relational vocabulary, LOGSPACE-hardness is the usual notion: every
FO(DTC) definable problem reduces to `P`. -/
theorem hard_LOGSPACE_iff [L.IsRelational] (P : DecisionProblem L) :
    LOGSPACE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        DTCDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- **L ⊆ NL**: a deterministic walk is a walk, and FO(TC) definability is
membership in NL (`DescriptiveComplexity.tcDefinable_iff_mem_NL`, the two
translations through the Krom fragment). -/
theorem LOGSPACE_subset_NL : LOGSPACE ⊆ NL :=
  fun _ P hP => (tcDefinable_iff_mem_NL P).mp (DTCDefinable.tcDefinable hP)

end DescriptiveComplexity
