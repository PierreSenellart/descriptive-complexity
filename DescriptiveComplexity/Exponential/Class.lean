/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Pull
import DescriptiveComplexity.Hierarchy

/-!
# The exponential of a complexity class

`DescriptiveComplexity.ComplexityClass.exp` reads a class over the *expanded*
universe: `P ∈ C.exp` when there is an exponential expansion `X` and a problem
`Q ∈ C` such that `P` holds of `A` exactly when `Q` holds of `X.Map A`. Since
the expanded universe of a size-`n` structure has `2^(n^a)` points, a resource
bound read there is one exponential higher than the same bound read on `A`.
This is the succinctness upgrade – trivial properties of circuit-described
graphs become NP-complete ([Galperin–Wigderson 1983][galperin1983succinct]),
NP-complete properties become NEXPTIME-complete ([Papadimitriou–Yannakakis
1986][papadimitriou1986note]), and the general statement is [Veith
1998][veith1998succinct] – stated as an *operator* rather than as a theorem
about one problem at a time.

The operator is applied to an **abstract** `DescriptiveComplexity.ComplexityClass`,
and that is the whole point of the design: the complement equalities, the
inclusions and the completeness transfers of the exponential classes are then
inherited from their polynomial-level counterparts instead of being reproved.

That `ExpDefinable C` is closed under (ordered) first-order reductions – so
that `C.exp` is a class at all – is
`DescriptiveComplexity.ExpExpansion.pullOrdered`: an interpretation followed by
an expansion is an expansion. Nothing about `C` is used, which is why the
closure holds at an arbitrary class.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### Cofinal hardness only sees the membership predicate -/

/-- Cofinal hardness depends on the membership predicate only up to pointwise
equivalence. Needed to compare the hardness halves of two classes built by
`DescriptiveComplexity.ComplexityClass.ofMem` from equivalent membership
predicates, as `DescriptiveComplexity.ComplexityClass.exp_compl` does. -/
theorem cofinalHard_congr_mem
    {Mem Mem' : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    (h : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀), Mem Q ↔ Mem' Q)
    {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    CofinalHard Mem P ↔ CofinalHard Mem' P := by
  constructor
  · intro hP L' _ S hS L'' _ Q hQ
    exact hP S hS Q ((h Q).mpr hQ)
  · intro hP L' _ S hS L'' _ Q hQ
    exact hP S hS Q ((h Q).mp hQ)

/-! ### Definability over an expanded universe -/

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- **Definability over an expanded universe**: the problem `P` is `C`-definable
one exponential up when some exponential expansion `X` turns it into a problem
of `C` – `P` holds of `A` exactly when a fixed `Q ∈ C` holds of `X.Map A`. -/
def ExpDefinable (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), C.Mem Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

variable {C : ComplexityClass} {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- Definability over an expanded universe only depends on the finite instances
of a problem. -/
theorem expDefinable_congr {P P' : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) :
    ExpDefinable C P ↔ ExpDefinable C P' := by
  constructor <;> rintro ⟨X, R, hR, hX⟩ <;> refine ⟨X, R, hR, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hX A)
  · exact (h A).trans (hX A)

/-- **Closure under ordered first-order reductions**: the interpretation of the
reduction, followed by the expansion witnessing `Q`, is again an expansion. -/
theorem ExpDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : ExpDefinable C Q) :
    ExpDefinable C P := by
  obtain ⟨X, R, hR, hX⟩ := h
  letI := f.tagFinite
  letI := f.tagNonempty
  letI : LinearOrder f.Tag := finiteLinearOrder f.Tag
  -- The pulled expansion has the same expanded vocabulary as `X`, but
  -- `pullOrdered` is not reducible, so the expanded structure has to be offered
  -- to instance search by hand.
  letI hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      X.E.Structure ((X.pullOrdered f.toInterpretation).Map A) :=
    fun A => X.pullOrderedStructure f.toInterpretation A
  refine ⟨X.pullOrdered f.toInterpretation, R, hR, ?_⟩
  intro A _ _ _ _
  letI := f.toInterpretation.mapLinearOrder A
  haveI := f.toInterpretation.map_finite A
  haveI := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hX (f.toInterpretation.Map A)).trans
    (R.iso_invariant (X.pullOrderedLEquiv f.toInterpretation A)))

/-- Closure under first-order reductions. -/
theorem ExpDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : ExpDefinable C Q) :
    ExpDefinable C P :=
  h.of_orderedReduction f.toOrdered

/-! ### The exponential of a class -/

/-- **The exponential of a complexity class**: the problems that become members
of `C` when read over an exponentially larger, definable universe. Hardness is
cofinal hardness for that membership predicate, as for every class of this
library. -/
noncomputable def ComplexityClass.exp (C : ComplexityClass) : ComplexityClass :=
  .ofMem (fun P => ExpDefinable C P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => expDefinable_congr h)

@[simp]
theorem ComplexityClass.mem_exp (C : ComplexityClass) (P : DecisionProblem L) :
    P ∈ C.exp ↔ ExpDefinable C P :=
  Iff.rfl

/-- The exponential is monotone. -/
theorem ComplexityClass.exp_mono {C D : ComplexityClass} (h : C ⊆ D) : C.exp ⊆ D.exp := by
  rintro L₀ _ P ⟨X, R, hR, hX⟩
  exact ⟨X, R, h hR, hX⟩

/-- **The exponential commutes with complementation**: complementing before or
after the expansion is the same thing, since the expansion is applied to the
*instance* and complementation to the *answer*.

This is what makes `EXPTIME = coEXPTIME` and `EXPSPACE = coEXPSPACE`
consequences of the corresponding polynomial-level facts rather than theorems
in their own right. -/
theorem ComplexityClass.exp_compl (C : ComplexityClass) : C.compl.exp = C.exp.compl := by
  have hmem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (R : DecisionProblem L₀),
      ExpDefinable C.compl R ↔ ExpDefinable C Rᶜ := by
    intro L₀ _ R
    constructor
    · rintro ⟨X, S, hS, hX⟩
      exact ⟨X, Sᶜ, hS, fun A _ _ _ _ => not_congr (hX A)⟩
    · rintro ⟨X, S, hS, hX⟩
      refine ⟨X, Sᶜ, by simpa using hS, fun A _ _ _ _ => ?_⟩
      exact not_not.symm.trans (not_congr (hX A))
  exact ComplexityClass.ext (fun R => hmem R) fun R => cofinalHard_congr_mem hmem R

end DescriptiveComplexity
