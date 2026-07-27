/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderKromPull
import DescriptiveComplexity.Hierarchy

/-!
# NL, by the Krom fragment

**The class NL**: the problems definable in the Krom fragment SO-Krom of
existential second-order logic (`DescriptiveComplexity.SigmaSOKromDefinable`), which
captures nondeterministic logarithmic space on ordered structures ([Grädel
1992][gradel1992capturing]). This is the same move as defining `PTIME` by the
Horn fragment and NP by `Σ₁`-definability: the class is a *definition*, not an
axiom, and it is a bona fide `DescriptiveComplexity.ComplexityClass` because SO-Krom
definability is closed under (ordered) first-order reductions – the Krom shape
survives the pullback, see `DescriptiveComplexity.SecondOrderKromPull`.

NL is not a level of the polynomial hierarchy of `DescriptiveComplexity.Hierarchy`,
which is why it lives in its own file. What relates it to that hierarchy are
two theorems that are *not* free here:

* **`NL ⊆ PTIME`** has no syntactic route: a Krom kernel is not a Horn kernel
  (Horn clauses may be wide, Krom clauses may have two positive literals), so
  the inclusion is not an instance of "restrict the kernel further". It goes
  through the complete problem instead, and is proved downstream with 2SAT
  (`DescriptiveComplexity.NL_subset_PTIME`, with `DescriptiveComplexity.NL_subset_NP` in its
  wake): 2SAT is in PTIME by a Horn program that guesses reachability in the
  implication graph and rejects, by a goal clause, the instances where a
  variable reaches its own negation and back.
* **`NL = coNL`** (Immerman–Szelepcsényi) is not the definitional duality that
  gives `PiP k` from `SigmaP k`: the complement of an SO-Krom definable problem
  is not obviously SO-Krom definable. It is a genuine theorem, and the reason
  the fixpoint logic FO(TC) is still wanted even once this fragment exists –
  the inductive-counting proof is naturally a statement about FO(TC), and that
  is where it is proved (`DescriptiveComplexity.TCDefinable.compl`), reaching this
  fragment through the two translations as `DescriptiveComplexity.NL_eq_coNL` in
  `DescriptiveComplexity.ImmermanSzelepcsenyi`.

Note that the *containment* `SO-Krom ⊆ NL` on the machine side already uses
Immerman–Szelepcsényi: satisfiability of a 2-CNF is the complement of a
reachability condition on the implication graph. Nothing in this library
depends on that, since NL is defined by the fragment rather than by a machine;
it is why the fragment is the right primitive here.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class NL**: the problems definable in the Krom fragment SO-Krom of
existential second-order logic, which captures nondeterministic logarithmic
space on ordered structures ([Grädel 1992][gradel1992capturing]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`); over a relational vocabulary it is the usual
notion, `DescriptiveComplexity.hard_NL_iff`. -/
noncomputable def NL : ComplexityClass where
  Mem P := SigmaSOKromDefinable P
  Hard P := CofinalHard (fun Q => SigmaSOKromDefinable Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  hard_of_relOrderedReduction f hP := CofinalHard.of_relOrderedReduction f hP
  mem_congr_finite h := sigmaSOKromDefinable_congr h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-- Membership in NL is exactly SO-Krom definability, by definition. -/
theorem mem_NL_iff (P : DecisionProblem L) : P ∈ NL ↔ SigmaSOKromDefinable P :=
  Iff.rfl

/-- Over a relational vocabulary, NL-hardness is the usual notion: every
SO-Krom definable problem reduces to `P`. -/
theorem hard_NL_iff [L.IsRelational] (P : DecisionProblem L) :
    NL.Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        SigmaSOKromDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- coNL, the complement class of NL. That it coincides with NL is
Immerman–Szelepcsényi, *not* proved here (see the module docstring). -/
noncomputable abbrev coNL : ComplexityClass := NL.compl

end DescriptiveComplexity
