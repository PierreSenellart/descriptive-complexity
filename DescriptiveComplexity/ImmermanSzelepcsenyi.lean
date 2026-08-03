/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureCompl
import DescriptiveComplexity.KromTransitiveClosure
import DescriptiveComplexity.Problems.Reachability

/-!
# Immerman–Szelepcsényi: `NL = coNL`

**The theorem** ([Immerman 1988][immerman1988nondeterministic], [Szelepcsényi
1988][szelepcsenyi1988method]): nondeterministic logarithmic space is closed
under complement. In this library the class NL is *defined* by the Krom
fragment of existential second-order logic
(`DescriptiveComplexity.NL`), and the theorem is assembled from three pieces:

* `DescriptiveComplexity.TCDefinable.compl` – FO(TC) is closed under complement, the
  content of the theorem, proved by the inductive-counting machine of
  `DescriptiveComplexity.InductiveCounting` run inside a single transitive closure
  (`DescriptiveComplexity.TransitiveClosureCompl`);
* the two translations between the Krom fragment and FO(TC), which say that
  SO-Krom definability is FO(TC) definability *of the complement*
  (`DescriptiveComplexity.sigmaSOKromDefinable_iff_tcDefinable_compl`);
* the definitional duality between a class and its complement class.

Three consequences are recorded here beyond `NL = coNL` itself: NL *is* FO(TC)
(`DescriptiveComplexity.tcDefinable_iff_mem_NL`), which the two translations alone
could not say; the Krom fragment is closed under complement, which no
inspection of clauses could give; and `REACH ∈ NL`
(`DescriptiveComplexity.reach_mem_NL`), the membership a clausal fragment cannot state
directly because it defines non-reachability head-on.
-/

namespace DescriptiveComplexity

open FirstOrder Language

variable {L : Language.{0, 0}}

/-! ### FO(TC) is closed under complement -/

/-- **Immerman–Szelepcsényi**: on finite ordered structures, the complement of
an FO(TC) definable problem is FO(TC) definable.

The specification of the complement is the inductive-counting machine: its
modes are the control states (a phase, one flag and the mode of each of eight
registers) and its tuples hold the eight registers side by side, so that
counting the nodes of every layer of the given walk – and certifying, at the
last layer, that no accepting node was ever counted in – is itself one walk. -/
theorem TCDefinable.compl [L.IsRelational] {P : DecisionProblem L} (h : TCDefinable P) :
    TCDefinable Pᶜ := by
  classical
  obtain ⟨spec, hspec⟩ := h
  letI : LinearOrder (spec.pad).Mode :=
    LinearOrder.lift' (Finite.equivFin (spec.pad).Mode) (Equiv.injective _)
  refine ⟨TCCompl.complSpec (spec.pad), ?_⟩
  intro A _ _ _ _
  rw [TCCompl.complSpec_accepts_iff]
  exact not_congr ((hspec A).trans (spec.pad_accepts_iff A).symm)

/-- Complementation is a bijection of the FO(TC) definable problems. -/
theorem tcDefinable_compl_iff [L.IsRelational] (P : DecisionProblem L) :
    TCDefinable Pᶜ ↔ TCDefinable P := by
  refine ⟨fun h => ?_, TCDefinable.compl⟩
  have h2 := h.compl
  rwa [DecisionProblem.compl_compl] at h2

/-! ### `NL = coNL` -/

/-- **NL is FO(TC)**: a problem is in NL exactly when it is FO(TC) definable.
The two translations against the Krom fragment give this only up to a
complement; Immerman–Szelepcsényi removes it. -/
theorem tcDefinable_iff_mem_NL [L.IsRelational] (P : DecisionProblem L) : TCDefinable P ↔ P ∈ NL :=
  ((tcDefinable_compl_iff P).symm).trans (mem_NL_iff_tcDefinable_compl P).symm

/-- **The Krom fragment is closed under complement**: a statement about a
clausal fragment that no inspection of its clauses provides – it is
Immerman–Szelepcsényi, read through the translations to FO(TC). -/
theorem sigmaSOKromDefinable_compl_iff [L.IsRelational] (P : DecisionProblem L) :
    SigmaSOKromDefinable Pᶜ ↔ SigmaSOKromDefinable P := by
  rw [sigmaSOKromDefinable_iff_tcDefinable_compl, sigmaSOKromDefinable_iff_tcDefinable_compl,
    DecisionProblem.compl_compl, tcDefinable_compl_iff]

/-- **`NL = coNL`** ([Immerman 1988][immerman1988nondeterministic],
[Szelepcsényi 1988][szelepcsenyi1988method]): nondeterministic logarithmic
space is closed under complement. -/
theorem NL_eq_coNL : NL = coNL := by
  refine ComplexityClass.ext (fun P => (sigmaSOKromDefinable_compl_iff P).symm) fun P => ?_
  constructor
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sigmaSOKromDefinable_compl_iff Q).mp hQ)
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sigmaSOKromDefinable_compl_iff Q).mpr hQ)

/-- Membership in NL is closed under complement. -/
theorem mem_NL_compl_iff [L.IsRelational] (P : DecisionProblem L) : Pᶜ ∈ NL ↔ P ∈ NL :=
  sigmaSOKromDefinable_compl_iff P

/-! ### REACH is in NL -/

/-- **`REACH ∈ NL`**: directed reachability belongs to nondeterministic
logarithmic space. The Krom fragment defines *non*-reachability head-on – a
clausal fragment states closure and rejection – so this membership is exactly
what Immerman–Szelepcsényi adds. -/
theorem reach_mem_NL : REACH ∈ NL := (tcDefinable_iff_mem_NL REACH).mp reach_tcDefinable

end DescriptiveComplexity
