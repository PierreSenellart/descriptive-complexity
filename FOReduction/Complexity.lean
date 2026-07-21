/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.ThreeColToSat
import FOReduction.SatToThreeCol

/-!
# Abstract complexity classes, the polynomial hierarchy, and NP-completeness

Complexity classes are introduced *abstractly*: a `ComplexityClass` assigns to
decision problems (over arbitrary vocabularies) a membership predicate and a
hardness predicate, and is required to be closed under (ordered) first-order
reductions — membership downward (`P ≤ᶠᵒ Q` and `Q ∈ 𝒞` give `P ∈ 𝒞`),
hardness upward (`P ≤ᶠᵒ Q` and `P` `𝒞`-hard give `Q` `𝒞`-hard). Since FO
reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, every class from
LOGSPACE up is closed in this sense, so this is a mild requirement. Note that
closure must be part of the *definition* of a complexity class rather than an
axiom quantified over all classes: arbitrary collections of problems need not
be closed, and the quantified axiom would be inconsistent.

The polynomial hierarchy is then posited abstractly, as axioms about a family
of classes (all these axioms hold in the trivial model where every class
contains every problem, so they are jointly consistent):

* `FirstOrder.SigmaP k` and `FirstOrder.PiP k`: the levels `Σₖᵖ` and `Πₖᵖ`,
  with `PTIME`, `NP` and `coNP` as abbreviations for `Σ₀ᵖ`, `Σ₁ᵖ` and `Π₁ᵖ`;
* `FirstOrder.piP_zero_eq`: `Π₀ᵖ = Σ₀ᵖ` (both are PTIME);
* the four level inclusions `Σₖᵖ ∪ Πₖᵖ ⊆ Σₖ₊₁ᵖ ∩ Πₖ₊₁ᵖ`;
* `FirstOrder.mem_piP_iff`: `Πₖᵖ` consists of the complements of `Σₖᵖ`
  problems (`DecisionProblem.compl`, notation `Pᶜ`);
* `FirstOrder.SAT_NP_complete`: the Cook–Levin theorem — SAT is the
  archetypical NP-complete problem (its NP-hardness holds under ordered FO
  reductions, Immerman, "Descriptive Complexity", ch. 3).

`FirstOrder.PH` is *defined* from the levels, and closure under FO reductions
is proved for it. If NP is one day defined (e.g. via Fagin's theorem,
`NP = ESO`), the axioms above become proof obligations.

From the two reductions of this library we then *derive*, with no machine
model anywhere:

* `FirstOrder.threeCol_mem_NP : ThreeCol ∈ NP` (via `ThreeCol ≤ᶠᵒ SAT`);
* `FirstOrder.threeCol_NP_hard : NP.Hard ThreeCol` (via `SAT ≤ᶠᵒ[≤] ThreeCol`);
* `FirstOrder.threeCol_NP_complete : NP.Complete ThreeCol`.
-/

namespace FirstOrder

open Language

/-- An abstract complexity class: a collection of decision problems (its
`Mem`bership predicate) together with a `Hard`ness predicate, closed under
(ordered) first-order reductions. Both predicates are left completely
abstract; the closure requirements are sound for every class containing
LOGSPACE, since (ordered) FO reductions are computable in AC⁰. -/
structure ComplexityClass where
  /-- The problems belonging to the class. Use the notation `P ∈ 𝒞`. -/
  Mem : ∀ {L : Language.{0, 0}}, DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to ("`𝒞`-hard"). -/
  Hard : ∀ {L : Language.{0, 0}}, DecisionProblem L → Prop
  /-- Membership travels backward along FO reductions. -/
  mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Mem Q → Mem P
  /-- Hardness travels forward along FO reductions. -/
  hard_of_foReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Hard P → Hard Q
  /-- Membership travels backward along ordered FO reductions. -/
  mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P
  /-- Hardness travels forward along ordered FO reductions. -/
  hard_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Complexity classes speak about *finite* instances only: membership does
  not depend on the behavior of a problem on infinite structures. -/
  mem_congr_finite : ∀ {L : Language.{0, 0}} {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)
  /-- Hardness, too, only depends on the finite instances of a problem. -/
  hard_congr_finite : ∀ {L : Language.{0, 0}} {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Hard P ↔ Hard Q)

/-- `P ∈ 𝒞`: the problem `P` belongs to the complexity class `𝒞`. (This
overloads the `∈` notation; the `Membership` class cannot be used here since
the element type `DecisionProblem L` is not determined by `ComplexityClass`.) -/
scoped notation:50 P:51 " ∈ " C:51 => ComplexityClass.Mem C P

namespace ComplexityClass

/-- Inclusion of complexity classes. -/
instance : HasSubset ComplexityClass :=
  ⟨fun C D => ∀ ⦃L : Language.{0, 0}⦄ ⦃P : DecisionProblem L⦄, C.Mem P → D.Mem P⟩

variable (C : ComplexityClass) {L : Language.{0, 0}}

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def Complete (P : DecisionProblem L) : Prop :=
  P ∈ C ∧ C.Hard P

theorem Complete.mem {P : DecisionProblem L} (h : C.Complete P) : P ∈ C := h.1

theorem Complete.hard {P : DecisionProblem L} (h : C.Complete P) : C.Hard P := h.2

end ComplexityClass

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
protected def DecisionProblem.compl {L : Language.{0, 0}} (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

instance {L : Language.{0, 0}} : Compl (DecisionProblem L) :=
  ⟨DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} (P : DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

/-! ### The polynomial hierarchy, axiomatized -/

/-- The `Σₖᵖ` levels of the polynomial hierarchy, as abstract classes. -/
axiom SigmaP : ℕ → ComplexityClass

/-- The `Πₖᵖ` levels of the polynomial hierarchy, as abstract classes. -/
axiom PiP : ℕ → ComplexityClass

/-- Polynomial time: the zeroth level of the hierarchy. -/
noncomputable abbrev PTIME : ComplexityClass := SigmaP 0

/-- NP is `Σ₁ᵖ`. -/
noncomputable abbrev NP : ComplexityClass := SigmaP 1

/-- coNP is `Π₁ᵖ`. -/
noncomputable abbrev coNP : ComplexityClass := PiP 1

/-- The zeroth levels coincide: `Π₀ᵖ = Σ₀ᵖ = PTIME`. -/
axiom piP_zero_eq : PiP 0 = PTIME

/-- `Σₖᵖ ⊆ Σₖ₊₁ᵖ`. -/
axiom sigmaP_subset_sigmaP_succ (k : ℕ) : SigmaP k ⊆ SigmaP (k + 1)

/-- `Σₖᵖ ⊆ Πₖ₊₁ᵖ`. -/
axiom sigmaP_subset_piP_succ (k : ℕ) : SigmaP k ⊆ PiP (k + 1)

/-- `Πₖᵖ ⊆ Σₖ₊₁ᵖ`. -/
axiom piP_subset_sigmaP_succ (k : ℕ) : PiP k ⊆ SigmaP (k + 1)

/-- `Πₖᵖ ⊆ Πₖ₊₁ᵖ`. -/
axiom piP_subset_piP_succ (k : ℕ) : PiP k ⊆ PiP (k + 1)

/-- `Πₖᵖ` consists of the complements of the `Σₖᵖ` problems. -/
axiom mem_piP_iff (k : ℕ) {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ PiP k ↔ Pᶜ ∈ SigmaP k

/-- The polynomial hierarchy: union of all the levels. Unlike the levels, it
is *defined*, and its closure under FO reductions is proved from that of the
levels. A problem is PH-hard if it is hard for every level. -/
noncomputable def PH : ComplexityClass where
  Mem P := ∃ k, (SigmaP k).Mem P
  Hard P := ∀ k, (SigmaP k).Hard P
  mem_of_foReduction h := fun ⟨k, hk⟩ => ⟨k, (SigmaP k).mem_of_foReduction h hk⟩
  hard_of_foReduction h hP k := (SigmaP k).hard_of_foReduction h (hP k)
  mem_of_orderedReduction h := fun ⟨k, hk⟩ => ⟨k, (SigmaP k).mem_of_orderedReduction h hk⟩
  hard_of_orderedReduction h hP k := (SigmaP k).hard_of_orderedReduction h (hP k)
  mem_congr_finite h := exists_congr fun k => (SigmaP k).mem_congr_finite h
  hard_congr_finite h := forall_congr' fun k => (SigmaP k).hard_congr_finite h

theorem sigmaP_subset_PH (k : ℕ) : SigmaP k ⊆ PH :=
  fun _ _ hP => ⟨k, hP⟩

theorem piP_subset_PH (k : ℕ) : PiP k ⊆ PH :=
  fun _ _ hP => ⟨k + 1, piP_subset_sigmaP_succ k hP⟩

/-- `PTIME ⊆ NP`. -/
theorem PTIME_subset_NP : PTIME ⊆ NP :=
  sigmaP_subset_sigmaP_succ 0

/-- `PTIME ⊆ coNP`. -/
theorem PTIME_subset_coNP : PTIME ⊆ coNP :=
  sigmaP_subset_piP_succ 0

/-- A problem's complement is in coNP iff the problem is in NP. -/
theorem compl_mem_coNP_iff {L : Language.{0, 0}} (P : DecisionProblem L) :
    Pᶜ ∈ coNP ↔ P ∈ NP := by
  rw [mem_piP_iff, DecisionProblem.compl_compl]

/-! ### SAT is NP-complete (Cook–Levin, axiomatized) and consequences -/

/-- The Cook–Levin theorem, as an axiom: SAT is the archetypical NP-complete
problem. Its NP-hardness holds even under (ordered) first-order reductions
(Immerman), consistently with the abstract closure properties.

Like every statement about complexity classes, this is a statement about the
*finite* CNF structures only: by `ComplexityClass.mem_congr_finite` and
`ComplexityClass.hard_congr_finite`, membership and hardness are unaffected
by the behavior of `SAT` on infinite structures. -/
axiom SAT_NP_complete : NP.Complete SAT

/-- SAT is in NP. -/
theorem sat_mem_NP : SAT ∈ NP :=
  SAT_NP_complete.mem

/-- SAT is NP-hard. -/
theorem sat_NP_hard : NP.Hard SAT :=
  SAT_NP_complete.hard

/-- The complement of SAT (essentially, propositional entailment of `⊥`) is
in coNP. -/
theorem sat_compl_mem_coNP : SATᶜ ∈ coNP :=
  (compl_mem_coNP_iff SAT).mpr sat_mem_NP

/-- 3-colorability is in NP: it FO-reduces to SAT, which is in NP. -/
theorem threeCol_mem_NP : ThreeCol ∈ NP :=
  NP.mem_of_foReduction threeCol_fo_reduction_sat sat_mem_NP

/-- 3-colorability is NP-hard: SAT, which is NP-hard, reduces to it by an
ordered FO reduction. -/
theorem threeCol_NP_hard : NP.Hard ThreeCol :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_threeCol sat_NP_hard

/-- **3-colorability is NP-complete**, derived from the two first-order
reductions of this library and the Cook–Levin axiom — with no machine model
anywhere. As with any complexity-theoretic statement, this is about finite
graphs only (`ComplexityClass.mem_congr_finite`/`hard_congr_finite`). -/
theorem threeCol_NP_complete : NP.Complete ThreeCol :=
  ⟨threeCol_mem_NP, threeCol_NP_hard⟩

end FirstOrder
