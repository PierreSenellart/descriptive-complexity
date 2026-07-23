/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderLift
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.SecondOrderOrdered
import DescriptiveComplexity.SecondOrderHornPull

/-!
# The polynomial hierarchy, defined by second-order alternation

The levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy for `k ≥ 1` – in
particular `NP = Σ₁ᵖ` and `coNP = Π₁ᵖ` – are *defined* here as
`ComplexityClass`es, via Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: membership is
second-order definability with `k` alternating quantifier blocks
(`DescriptiveComplexity.SigmaSODefinable` / `DescriptiveComplexity.PiSODefinable`), and the closure
of membership under (ordered) FO reductions is provided by the pullback
theorems of `DescriptiveComplexity.SecondOrderPull` and
`DescriptiveComplexity.SecondOrderOrdered`.

Hardness is defined *cofinally*: `P` is hard when every problem of the class
reduces (by an ordered FO reduction) to every relational problem that `P`
itself reduces to. For a problem over a relational vocabulary this is
equivalent to the usual “everything in the class reduces to `P`”
(`DescriptiveComplexity.cofinalHard_iff`, with per-class specializations
`DescriptiveComplexity.hard_sigmaP_succ_iff`, `DescriptiveComplexity.hard_piP_succ_iff` and
`DescriptiveComplexity.hard_PTIME_iff`), and the formulation makes hardness travel
forward along reductions even through non-relational vocabularies.

Level 0 is `DescriptiveComplexity.PTIME`, polynomial time, *defined* here as
definability in the Horn fragment SO-Horn of existential second-order logic
([Grädel 1992][gradel1992capturing]) – the same move as defining NP by
`Σ₁`-definability, and equally a definition rather than an axiom: the library
declares **no axioms**, every theorem depending on nothing beyond Lean's
standard `propext`, `Classical.choice` and `Quot.sound` (check with
`#print axioms`). The order-free characterization of PTIME is the
Chandra–Harel/Gurevich problem and is not needed here: SO-Horn definability,
like ordered FO reductions, is stated over ordered structures.

**What level 0 does and does not give.** It is a genuine class, closed under
(ordered) FO reductions by the shape-preserving pullback of
`DescriptiveComplexity.SecondOrderHornPull`, and `Πₖᵖ` is the complements of `Σₖᵖ` at
*every* level (`DescriptiveComplexity.mem_piP_iff`) – at level 0 by definition, above
it by the quantifier duality.

All four inclusions of level 0 into level 1 are proved – `PTIME ⊆ NP`,
`PTIME ⊆ coNP` and their complements (`DescriptiveComplexity.PTIME_subset_NP`,
`DescriptiveComplexity.PTIME_subset_coNP`, `DescriptiveComplexity.coPTIME_subset_NP`,
`DescriptiveComplexity.coPTIME_subset_coNP`); they live downstream with HORN-SAT, since
they go through the Horn discharge and, for the two crossing ones, through the
certificate of Horn *un*satisfiability of
`DescriptiveComplexity.Problems.HornSat.Unsat`.

That the two zeroth levels *coincide* – `PiP 0 = SigmaP 0`, polynomial time
closed under complement – is proved downstream, as
`DescriptiveComplexity.piP_zero_eq`: it is Grädel's capture theorem at level 0, and
its route is the logic-to-logic equivalence of SO-Horn with FO(LFP)
(`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`, in
`DescriptiveComplexity.FixedPointHorn`), a full logic being closed under negation by
construction; no machine model is involved.

The level inclusions above 0, the duality `Πₖᵖ = co-Σₖᵖ` and the class `PH` are
all proved (`DescriptiveComplexity.sigmaP_subset_sigmaP_succ`,
`DescriptiveComplexity.mem_piP_iff`…).
-/

namespace DescriptiveComplexity

open FirstOrder

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
`DescriptiveComplexity.hard_sigmaP_succ_iff`); this formulation is closed under
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

/-- **Over a relational vocabulary, cofinal hardness is the usual notion**:
every problem of the collection reduces to `P` itself. This holds whatever the
collection is – the proof only uses reflexivity and transitivity of reductions
– so the specializations to the individual classes below
(`DescriptiveComplexity.hard_sigmaP_succ_iff`, `DescriptiveComplexity.hard_piP_succ_iff`,
`DescriptiveComplexity.hard_PTIME_iff`) are corollaries by definitional unfolding.

The left-to-right direction is what a *user* of a hardness result needs, to
extract an actual reduction; it is where relationality of `P` is used, to
instantiate the cofinal quantifier at `P` itself. -/
theorem cofinalHard_iff [L.IsRelational]
    (Mem : ∀ {L₀ : Language.{0, 0}}, DecisionProblem L₀ → Prop) (P : DecisionProblem L) :
    CofinalHard Mem P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        Mem Q → Nonempty (Q ≤ᶠᵒ[≤] P) := by
  constructor
  · intro h L'' Q hQ
    exact h P ⟨(FOReduction.refl P).toOrdered⟩ Q hQ
  · intro h L' _ S hS L'' Q hQ
    exact ⟨(h Q hQ).some.trans hS.some⟩

/-! ### The complement of a class -/

/-- The *complement* of a complexity class: the problems whose complement
belongs to it – the “co-” operator. Closure under reductions is inherited,
since a reduction complements (`DescriptiveComplexity.FOReduction.compl`). -/
noncomputable def ComplexityClass.compl (C : ComplexityClass) : ComplexityClass where
  Mem P := C.Mem Pᶜ
  Hard P := CofinalHard (fun Q => C.Mem Qᶜ) P
  mem_of_foReduction f h := C.mem_of_foReduction f.compl h
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := C.mem_of_orderedReduction f.compl h
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  mem_congr_finite h := C.mem_congr_finite fun A _ _ => not_congr (h A)
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

@[simp]
theorem ComplexityClass.mem_compl (C : ComplexityClass) {L : Language.{0, 0}}
    (P : DecisionProblem L) : P ∈ C.compl ↔ Pᶜ ∈ C :=
  Iff.rfl

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

/-! ### Polynomial time, by the Horn fragment -/

/-- **The class PTIME**: the problems definable in the Horn fragment SO-Horn of
existential second-order logic ([Grädel 1992][gradel1992capturing]), which
captures polynomial time on ordered structures. It is a bona fide
`DescriptiveComplexity.ComplexityClass` because SO-Horn definability is closed under
(ordered) first-order reductions – the Horn shape survives the pullback, see
`DescriptiveComplexity.SecondOrderHornPull`.

This is level 0 of the hierarchy below (`DescriptiveComplexity.SigmaP`,
`DescriptiveComplexity.PiP`), and it has a complete problem, HORN-SAT
(`DescriptiveComplexity.HORNSAT_PTIME_complete`). That the class is closed under
complement – `PiP 0 = SigmaP 0` – is `DescriptiveComplexity.piP_zero_eq`, through the
equivalence with FO(LFP). -/
noncomputable def PTIME : ComplexityClass where
  Mem P := SigmaSOHornDefinable P
  Hard P := CofinalHard (fun Q => SigmaSOHornDefinable Q) P
  mem_of_foReduction f h := h.of_foReduction f
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := h.of_orderedReduction f
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  mem_congr_finite h := sigmaSOHornDefinable_congr h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-! ### The hierarchy -/

/-- The `Σₖᵖ` levels of the polynomial hierarchy: polynomial time at level 0
(`DescriptiveComplexity.PTIME`, defined by the Horn fragment SO-Horn), second-order
definability with `k` alternations above. -/
noncomputable def SigmaP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => sigmaLevel k

/-- The `Πₖᵖ` levels of the polynomial hierarchy; level 0 is *co*-polynomial
time, the complements of the SO-Horn definable problems. That this coincides
with `DescriptiveComplexity.PTIME` is the closure of polynomial time under complement,
`DescriptiveComplexity.piP_zero_eq` – see the module docstring. -/
noncomputable def PiP : ℕ → ComplexityClass
  | 0 => PTIME.compl
  | k + 1 => piLevel k

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
noncomputable abbrev NP : ComplexityClass := SigmaP 1

/-- coNP is `Π₁ᵖ`: the universal-second-order definable problems. -/
noncomputable abbrev coNP : ComplexityClass := PiP 1

/-- **`Πₖᵖ` consists of the complements of the `Σₖᵖ` problems**, at every
level: by definition at level 0, and by the quantifier duality
`DescriptiveComplexity.piSODefinable_iff_compl` above from level 1 on.

(That moreover `PiP 0 = SigmaP 0` – polynomial time closed under complement –
is `DescriptiveComplexity.piP_zero_eq`: complementing a Horn program needs its least
model computed inside the fragment, which is what the translation from FO(LFP)
provides.) -/
theorem mem_piP_iff (k : ℕ) {L : Language.{0, 0}} (P : DecisionProblem L) :
    P ∈ PiP k ↔ Pᶜ ∈ SigmaP k := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact piSODefinable_iff_compl (k + 1) P

/-- `Σₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`, by padding. (The level-0 inclusions are proved downstream
with HORN-SAT, which their proofs go through: `DescriptiveComplexity.PTIME_subset_NP`
and friends.) -/
theorem sigmaP_subset_sigmaP_succ (k : ℕ) : SigmaP (k + 1) ⊆ SigmaP (k + 2) :=
  fun _ _ hP => SigmaSODefinable.succ hP

/-- `Σₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
theorem sigmaP_subset_piP_succ (k : ℕ) : SigmaP (k + 1) ⊆ PiP (k + 2) :=
  fun _ _ hP => SigmaSODefinable.piSucc hP

/-- `Πₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`. -/
theorem piP_subset_sigmaP_succ (k : ℕ) : PiP (k + 1) ⊆ SigmaP (k + 2) :=
  fun _ _ hP => PiSODefinable.sigmaSucc hP

/-- `Πₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
theorem piP_subset_piP_succ (k : ℕ) : PiP (k + 1) ⊆ PiP (k + 2) :=
  fun _ _ hP => PiSODefinable.succ hP

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

/-- `Πₖ₊₁ᵖ ⊆ PH`. (At level 0 this is
`DescriptiveComplexity.piP_zero_subset_PH`, which needs `PTIME ⊆ NP` and so lives
downstream, with HORN-SAT.) -/
theorem piP_subset_PH (k : ℕ) : PiP (k + 1) ⊆ PH :=
  fun _ _ hP => ⟨k + 2, piP_subset_sigmaP_succ k hP⟩

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
        SigmaSODefinable (k + 1) Q → Nonempty (Q ≤ᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- Over a relational vocabulary, cofinal `Πₖ₊₁ᵖ`-hardness is the usual
notion: every `Πₖ₊₁`-definable problem reduces to `P`. -/
theorem hard_piP_succ_iff [L.IsRelational] (k : ℕ) (P : DecisionProblem L) :
    (PiP (k + 1)).Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        PiSODefinable (k + 1) Q → Nonempty (Q ≤ᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- Over a relational vocabulary, cofinal PTIME-hardness is the usual notion:
every SO-Horn definable problem reduces to `P`. -/
theorem hard_PTIME_iff [L.IsRelational] (P : DecisionProblem L) :
    PTIME.Hard P ↔
      ∀ {L'' : Language.{0, 0}} (Q : DecisionProblem L''),
        SigmaSOHornDefinable Q → Nonempty (Q ≤ᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

end DescriptiveComplexity
