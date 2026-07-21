/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.SecondOrderLift
import FOReduction.SecondOrderPull
import FOReduction.SecondOrderOrdered

/-!
# The polynomial hierarchy, defined by second-order alternation

The levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy for `k ≥ 1` — in
particular `NP = Σ₁ᵖ` and `coNP = Π₁ᵖ` — are *defined* here as
`ComplexityClass`es, via Fagin's and Stockmeyer's theorems: membership is
second-order definability with `k` alternating quantifier blocks
(`FirstOrder.SigmaSODefinable` / `FirstOrder.PiSODefinable`), and the closure
of membership under (ordered) FO reductions is provided by the pullback
theorems of `FOReduction.SecondOrderPull` and
`FOReduction.SecondOrderOrdered`.

Hardness is defined *cofinally*: `P` is hard when every problem of the class
reduces (by an ordered FO reduction) to every relational problem that `P`
itself reduces to. For a problem over a relational vocabulary this is
equivalent to the usual "everything in the class reduces to `P`"
(`FirstOrder.hard_sigmaP_succ_iff`, `FirstOrder.hard_piP_succ_iff`), and the
formulation makes hardness travel forward along reductions even through
non-relational vocabularies.

Level 0 — `PTIME` — remains axiomatized (`FirstOrder.PTIME`): no known
order-free logic captures polynomial time (the Chandra–Harel/Gurevich
problem), and the Immerman–Vardi characterization `P = FO(LFP)` on ordered
structures would require formalizing least fixed points and a built-in order.
Two axioms relate it to the defined levels: closure under complement
(`FirstOrder.PTIME_mem_compl`) and `PTIME ⊆ NP`
(`FirstOrder.PTIME_sigmaSODefinable`, the machine-model-dependent half of
Fagin's theorem). All three axioms hold e.g. of the empty class, so they are
jointly consistent; they of course also hold of actual polynomial time.

The level inclusions, the duality `Πₖᵖ = co-Σₖᵖ` and the class `PH` — all
axioms in earlier versions of this development — are now theorems, with their
former names (`FirstOrder.sigmaP_subset_sigmaP_succ`,
`FirstOrder.mem_piP_iff`, …).
-/

namespace FirstOrder

open Language

variable {L : Language.{0, 0}}

/-! ### Congruence of definability in the problem -/

/-- `Σₖ`-definability only depends on the finite instances of a problem. -/
theorem sigmaSODefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (k : ℕ) :
    SigmaSODefinable k P ↔ SigmaSODefinable k Q := by
  constructor <;> rintro ⟨Bs, hk, φ, hφ⟩ <;> refine ⟨Bs, hk, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- `Πₖ`-definability only depends on the finite instances of a problem. -/
theorem piSODefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (k : ℕ) :
    PiSODefinable k P ↔ PiSODefinable k Q := by
  constructor <;> rintro ⟨Bs, hk, φ, hφ⟩ <;> refine ⟨Bs, hk, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- An ordered FO reduction can be transported along an agreement of the
source problems on finite structures. -/
def OrderedFOReduction.congrSource {L' : Language.{0, 0}} [L'.IsRelational]
    {P P' : DecisionProblem L} {S : DecisionProblem L'}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) (g : P ≤ᶠᵒ[≤] S) :
    P' ≤ᶠᵒ[≤] S :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation := g.toInterpretation
    correct := fun A _ _ _ _ => (h A).symm.trans (g.correct A) }

/-! ### Cofinal hardness -/

/-- Hardness for a collection of problems, cofinally: every problem of the
collection reduces to every relational problem that `P` reduces to. For `P`
over a relational vocabulary this is the usual notion (see
`FirstOrder.hard_sigmaP_succ_iff`); this formulation is closed under
reductions out of arbitrary vocabularies. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}}, DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (P ≤ᶠᵒ[≤] S) →
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''), Mem Q → Nonempty (Q ≤ᶠᵒ[≤] S)

theorem CofinalHard.of_foReduction
    {Mem : ∀ {L₀ : Language.{0, 0}}, DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : P ≤ᶠᵒ Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q := by
  intro L' _ S hQS L'' R hR
  exact hP S (hQS.map fun g => f.trans_ordered g) R hR

theorem CofinalHard.of_orderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}}, DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : P ≤ᶠᵒ[≤] Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q := by
  intro L' _ S hQS L'' R hR
  exact hP S (hQS.map fun g => f.trans g) R hR

theorem CofinalHard.congr
    {Mem : ∀ {L₀ : Language.{0, 0}}, DecisionProblem L₀ → Prop}
    {L₁ : Language.{0, 0}} {P P' : DecisionProblem L₁}
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ P' A)
    (hP : CofinalHard Mem P) : CofinalHard Mem P' := by
  intro L' _ S hS L'' R hR
  exact hP S (hS.map fun g => g.congrSource fun A _ _ => (h A).symm) R hR

/-! ### The levels of the hierarchy -/

/-- The class `Σₖ₊₁ᵖ`, defined by second-order definability with `k + 1`
alternating blocks starting existentially. -/
noncomputable def sigmaLevel (k : ℕ) : ComplexityClass where
  Mem P := SigmaSODefinable (k + 1) P
  Hard P := CofinalHard (fun Q => SigmaSODefinable (k + 1) Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  mem_congr_finite h := sigmaSODefinable_congr h _
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-- The class `Πₖ₊₁ᵖ`, defined by second-order definability with `k + 1`
alternating blocks starting universally. -/
noncomputable def piLevel (k : ℕ) : ComplexityClass where
  Mem P := PiSODefinable (k + 1) P
  Hard P := CofinalHard (fun Q => PiSODefinable (k + 1) Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  mem_congr_finite h := piSODefinable_congr h _
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-! ### Level 0: polynomial time, axiomatized -/

/-- Polynomial time, as an abstract complexity class. It remains axiomatized:
no known order-free logic captures PTIME (Chandra–Harel/Gurevich), and the
ordered Immerman–Vardi characterization `P = FO(LFP)` is out of scope for
now. The axioms `PTIME`, `FirstOrder.PTIME_mem_compl` and
`FirstOrder.PTIME_sigmaSODefinable` are jointly consistent: all hold of the
class with no members and trivial hardness. -/
axiom PTIME : ComplexityClass

/-- PTIME is closed under complement (axiom). -/
axiom PTIME_mem_compl {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ PTIME ↔ Pᶜ ∈ PTIME

/-- Polynomial-time problems are existential-second-order definable — the
inclusion `PTIME ⊆ NP`, by the machine-model-dependent half of Fagin's
theorem (axiom). -/
axiom PTIME_sigmaSODefinable {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ PTIME → SigmaSODefinable 1 P

/-! ### The hierarchy -/

/-- The `Σₖᵖ` levels of the polynomial hierarchy: `PTIME` at level 0
(axiomatized), second-order definability with `k` alternations above. -/
noncomputable def SigmaP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => sigmaLevel k

/-- The `Πₖᵖ` levels of the polynomial hierarchy. -/
noncomputable def PiP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => piLevel k

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
noncomputable abbrev NP : ComplexityClass := SigmaP 1

/-- coNP is `Π₁ᵖ`: the universal-second-order definable problems. -/
noncomputable abbrev coNP : ComplexityClass := PiP 1

/-- The zeroth levels coincide: `Π₀ᵖ = Σ₀ᵖ = PTIME`. -/
theorem piP_zero_eq : PiP 0 = PTIME := rfl

/-- `Πₖᵖ` consists of the complements of the `Σₖᵖ` problems: by the
complement axiom for PTIME at level 0, by the quantifier duality
`FirstOrder.piSODefinable_iff_compl` above. -/
theorem mem_piP_iff (k : ℕ) {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ PiP k ↔ Pᶜ ∈ SigmaP k := by
  cases k with
  | zero => exact PTIME_mem_compl P
  | succ k => exact piSODefinable_iff_compl (k + 1) P

/-- `Σₖᵖ ⊆ Σₖ₊₁ᵖ`: the Fagin axiom at level 0, padding above. -/
theorem sigmaP_subset_sigmaP_succ (k : ℕ) : SigmaP k ⊆ SigmaP (k + 1) := by
  cases k with
  | zero => exact fun _ P hP => PTIME_sigmaSODefinable P hP
  | succ k => exact fun _ P hP => SigmaSODefinable.succ hP

/-- `Σₖᵖ ⊆ Πₖ₊₁ᵖ`. -/
theorem sigmaP_subset_piP_succ (k : ℕ) : SigmaP k ⊆ PiP (k + 1) := by
  cases k with
  | zero =>
    exact fun _ P hP => (piSODefinable_iff_compl 1 P).mpr
      (PTIME_sigmaSODefinable Pᶜ ((PTIME_mem_compl P).mp hP))
  | succ k => exact fun _ P hP => SigmaSODefinable.piSucc hP

/-- `Πₖᵖ ⊆ Σₖ₊₁ᵖ`. -/
theorem piP_subset_sigmaP_succ (k : ℕ) : PiP k ⊆ SigmaP (k + 1) := by
  cases k with
  | zero => exact fun _ P hP => PTIME_sigmaSODefinable P hP
  | succ k => exact fun _ P hP => PiSODefinable.sigmaSucc hP

/-- `Πₖᵖ ⊆ Πₖ₊₁ᵖ`. -/
theorem piP_subset_piP_succ (k : ℕ) : PiP k ⊆ PiP (k + 1) := by
  cases k with
  | zero =>
    exact fun _ P hP => (piSODefinable_iff_compl 1 P).mpr
      (PTIME_sigmaSODefinable Pᶜ ((PTIME_mem_compl P).mp hP))
  | succ k => exact fun _ P hP => PiSODefinable.succ hP

/-- The polynomial hierarchy: union of all the levels. A problem is PH-hard
if it is hard for every level. -/
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

/-! ### Hardness over relational vocabularies -/

/-- Over a relational vocabulary, cofinal `Σₖ₊₁ᵖ`-hardness is the usual
notion: every `Σₖ₊₁`-definable problem reduces to `P`. -/
theorem hard_sigmaP_succ_iff [L.IsRelational] (k : ℕ) (P : DecisionProblem L) :
    (SigmaP (k + 1)).Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        SigmaSODefinable (k + 1) Q → Nonempty (Q ≤ᶠᵒ[≤] P) := by
  constructor
  · intro h L'' Q hQ
    exact h P ⟨(FOReduction.refl P).toOrdered⟩ Q hQ
  · intro h L' _ S hS L'' Q hQ
    exact ⟨(h Q hQ).some.trans hS.some⟩

/-- Over a relational vocabulary, cofinal `Πₖ₊₁ᵖ`-hardness is the usual
notion: every `Πₖ₊₁`-definable problem reduces to `P`. -/
theorem hard_piP_succ_iff [L.IsRelational] (k : ℕ) (P : DecisionProblem L) :
    (PiP (k + 1)).Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        PiSODefinable (k + 1) Q → Nonempty (Q ≤ᶠᵒ[≤] P) := by
  constructor
  · intro h L'' Q hQ
    exact h P ⟨(FOReduction.refl P).toOrdered⟩ Q hQ
  · intro h L' _ S hS L'' Q hQ
    exact ⟨(h Q hQ).some.trans hS.some⟩

end FirstOrder
