/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax564036.Difference
end Lax564036.Difference

namespace Lax564036Proofs.DescriptiveComplexity.DPDefinable
end Lax564036Proofs.DescriptiveComplexity.DPDefinable

namespace Lax564036Proofs.DescriptiveComplexity.DecisionProblem
end Lax564036Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax564036Proofs.DescriptiveComplexity.FOInterpretation
end Lax564036Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.Difference (DPDefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

/-!
# DP, the class of differences of NP problems

**The class DP** ([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]):
the problems that are the conjunction of an NP problem and a coNP one –
equivalently, the *difference* `S \ U` of two NP problems, taking `U := Tᶜ`.
Logically, and this is how the class is defined here
(`DescriptiveComplexity.DPDefinable`), it is definability by a conjunction of a `Σ₁`
and a `Π₁` sentence.

DP is not a level of the polynomial hierarchy, and not the same thing as
`NP ∩ coNP`: the conjunction is of *two different* problems, whereas
`P ∈ NP ∩ coNP` asks one problem to have both kinds of definition. It sits
just above NP and coNP and inside the second level of the hierarchy:
`NP ∪ coNP ⊆ DP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` (`DescriptiveComplexity.NP_subset_DP`,
`DescriptiveComplexity.coNP_subset_DP`, `DescriptiveComplexity.DP_subset_sigmaP_two`,
`DescriptiveComplexity.DP_subset_piP_two`). The lower bounds conjoin the tautology
to the other side; the upper bounds merge `(∃X. φ) ∧ (∀Y. ψ)` into the single
alternation `∃X ∀Y. (φ ∧ ψ)`, which is sound in both block orders because
neither kernel mentions the other's variables.

The canonical DP-complete problem, SAT-UNSAT ([Papadimitriou & Yannakakis
1984][papadimitriou1984complexity]), lives in
`DescriptiveComplexity.Problems.SatUnsat`: its hardness runs the Cook–Levin
discharge of the `Σ₁` half and that of the complement of the `Π₁` half side by
side into one paired-CNF instance.

## Why closure needs the order-elimination lemma

A `DescriptiveComplexity.ComplexityClass` must be closed under reductions, and for DP
this is not inherited from the two levels it is built out of. Pulling a
definition back through an *ordered* reduction produces a sentence over the
ordered expansion, correct for every linear order; the existing closure
theorems then remove the order because the problem they are given is
order-invariant. Here the two halves are not: only their conjunction is, so
`S (I≼.Map A)` really does depend on the order `≼`.

The way out is to let the two halves disagree about the order and quantify it
in opposite directions – existentially on the `Σ` side
(`DescriptiveComplexity.DecisionProblem.comapExOrd`) and universally on the `Π` side
(`DescriptiveComplexity.DecisionProblem.comapAllOrd`). Their conjunction is still
equivalent to the pullback: for the forward direction every order works for
both halves, and backwards the order witnessing the existential is one of
those the universal covers. Each half is then definable at its level by
`DescriptiveComplexity.sigmaSODefinable_of_orderPull` and
`DescriptiveComplexity.piSODefinable_of_orderPull`, which are exactly the
order-elimination construction stated for a sentence rather than for a
reduction.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Pulling a problem back along an interpretation -/

/-- The problem pulled back along an interpretation: its yes-instances are the
structures whose image is a yes-instance of `Q`. It is a decision problem
because interpretations are functorial on isomorphisms
(`DescriptiveComplexity.FOInterpretation.mapLEquiv`). -/
def DecisionProblem.comap [L.IsRelational] [L'.IsRelational] {Tag : Type} {dim : ℕ}
    (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (Q : Lax904597.Problems.DecisionProblem L') : Lax904597.Problems.DecisionProblem L where
  Holds A _ := Q (I.Map A)
  iso_invariant e := Q.iso_invariant (I.mapLEquiv e)

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax564036Proofs.DescriptiveComplexity.DecisionProblem (comap)

end Lax904597.Problems.DecisionProblem

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- The tautological reduction: the pullback of `Q` reduces to `Q`, by the
very interpretation it was pulled back along. -/
def FOInterpretation.comapReduction [L.IsRelational] [L'.IsRelational] {Tag : Type} {dim : ℕ}
    [Finite Tag] [Nonempty Tag] (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim)
    (Q : Lax904597.Problems.DecisionProblem L') : Q.comap I ≤ᶠᵒ Q where
  Tag := Tag
  dim := dim
  toInterpretation := I
  correct _ := Iff.rfl

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax564036Proofs.DescriptiveComplexity.FOInterpretation (comapReduction)

end Lax904597.Interpretations.FOInterpretation

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Transporting an order along an isomorphism

The two order-quantified pullbacks below are decision problems, and proving it
means moving a linear order from one structure to an isomorphic one. -/

section OrderTransport

variable {A B : Type} [L.Structure A] [L.Structure B]

/-- The linear order transported along an isomorphism: `b ≤ b'` when the
preimages compare. -/
@[instance_reducible]
noncomputable def transportOrder (e : A ≃[L] B) (lo : LinearOrder A) : LinearOrder B :=
  letI := lo
  LinearOrder.lift' e.symm e.symm.injective

/-- An isomorphism of `L`-structures is one of the ordered expansions, once
the order of the target is the transported one. -/
def orderedEquivOfTransport (e : A ≃[L] B) (lo : LinearOrder A) :
    letI := lo
    letI := transportOrder e lo
    A ≃[L.sum Language.order] B :=
  letI := lo
  letI := transportOrder e lo
  { toEquiv := e.toEquiv
    map_fun' := fun {_n} f x =>
      match f with
      | Sum.inl g => e.map_fun' g x
      | Sum.inr g => nomatch g
    map_rel' := fun {n} r x =>
      match n, r with
      | _, Sum.inl s => e.map_rel' s x
      | _, Sum.inr .le => by
        change e (x 0) ≤ e (x 1) ↔ x 0 ≤ x 1
        change e.symm (e (x 0)) ≤ e.symm (e (x 1)) ↔ x 0 ≤ x 1
        rw [e.symm_apply_apply, e.symm_apply_apply] }

end OrderTransport

/-! ### The two order-quantified pullbacks -/

section OrderedComap

variable [L'.IsRelational] {Tag : Type} {dim : ℕ}
  (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim) (Q : Lax904597.Problems.DecisionProblem L')

private theorem exOrd_iso {A B : Type} [L.Structure A] [L.Structure B] (e : A ≃[L] B)
    (h : ∃ lo : LinearOrder A,
      letI := lo
      Q (I.Map A)) :
    ∃ lo : LinearOrder B,
      letI := lo
      Q (I.Map B) := by
  obtain ⟨lo, hQ⟩ := h
  let := lo
  let := transportOrder e lo
  exact ⟨transportOrder e lo,
    (Q.iso_invariant (I.mapLEquiv (orderedEquivOfTransport e lo))).mp hQ⟩

/-- The pullback of `Q` along an *ordered* interpretation, with the order
quantified existentially: some linear order on the instance sends it to a
yes-instance of `Q`. -/
def DecisionProblem.comapExOrd [L.IsRelational] : Lax904597.Problems.DecisionProblem L where
  Holds A _ := ∃ lo : LinearOrder A,
    letI := lo
    Q (I.Map A)
  iso_invariant e := ⟨exOrd_iso I Q e, exOrd_iso I Q e.symm⟩

end OrderedComap

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax564036Proofs.DescriptiveComplexity.DecisionProblem (comapExOrd)

end Lax904597.Problems.DecisionProblem

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section OrderedComap

variable [L'.IsRelational] {Tag : Type} {dim : ℕ}
  (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim) (Q : Lax904597.Problems.DecisionProblem L')

/-- The pullback of `Q` along an *ordered* interpretation, with the order
quantified universally: every linear order on the instance sends it to a
yes-instance of `Q`. -/
def DecisionProblem.comapAllOrd [L.IsRelational] : Lax904597.Problems.DecisionProblem L where
  Holds A _ := ∀ lo : LinearOrder A,
    letI := lo
    Q (I.Map A)
  iso_invariant e := by
    constructor
    · intro h lo
      let := lo
      let := transportOrder e.symm lo
      exact (Q.iso_invariant (I.mapLEquiv (orderedEquivOfTransport e.symm lo))).mpr (h _)
    · intro h lo
      let := lo
      let := transportOrder e lo
      exact (Q.iso_invariant (I.mapLEquiv (orderedEquivOfTransport e lo))).mpr (h _)

end OrderedComap

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax564036Proofs.DescriptiveComplexity.DecisionProblem (comapAllOrd)

end Lax904597.Problems.DecisionProblem

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

section OrderedComap

variable [L'.IsRelational] {Tag : Type} {dim : ℕ}
  (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag dim) (Q : Lax904597.Problems.DecisionProblem L')

end OrderedComap

variable [L.IsRelational]

/-! ### DP definability -/

/-- DP definability only depends on the finite instances of a problem. -/
theorem dpDefinable_congr {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax564036.Difference.DPDefinable P ↔ Lax564036.Difference.DPDefinable Q := by
  constructor <;> rintro ⟨S, T, hS, hT, hST⟩ <;> refine ⟨S, T, hS, hT, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hST A)
  · exact (h A).trans (hST A)

/-! ### Closure under reductions -/

/-- DP definability is closed under first-order reductions: both halves are
pulled back along the interpretation. -/
theorem DPDefinable.of_foReduction [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    {Q : Lax904597.Problems.DecisionProblem L'} (f : P ≤ᶠᵒ Q) (h : Lax564036.Difference.DPDefinable Q) : Lax564036.Difference.DPDefinable P := by
  obtain ⟨S, T, hS, hT, hST⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨S.comap f.toInterpretation, T.comap f.toInterpretation,
    hS.of_foReduction (f.toInterpretation.comapReduction S),
    hT.of_foReduction (f.toInterpretation.comapReduction T), ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans (hST _)

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.Difference.DPDefinable

export Lax564036Proofs.DescriptiveComplexity.DPDefinable (of_foReduction)

end Lax564036.Difference.DPDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

variable [L.IsRelational]

/-- DP definability is closed under *ordered* first-order reductions. This is
where the two halves have to be allowed to disagree about the order: the `Σ`
half asks for some linear order, the `Π` half for all of them, and their
conjunction is again the pullback. -/
theorem DPDefinable.of_orderedReduction [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    {Q : Lax904597.Problems.DecisionProblem L'} (f : P ≤ᶠᵒ[≤] Q) (h : Lax564036.Difference.DPDefinable Q) : Lax564036.Difference.DPDefinable P := by
  obtain ⟨S, T, hS, hT, hST⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨DecisionProblem.comapExOrd f.toInterpretation S,
    DecisionProblem.comapAllOrd f.toInterpretation T, ?_, ?_, ?_⟩
  · obtain ⟨Bs, hk, φ, hφ⟩ := hS
    refine sigmaSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
      (by simpa [pullBlocks] using hk)
      (pullSO Bs (L.sum Language.order) L' f.toInterpretation φ) ?_
    intro A _ _ _
    refine exists_congr fun lo => ?_
    let := lo
    have := f.toInterpretation.map_finite A
    have := f.toInterpretation.map_nonempty A
    exact (hφ (f.toInterpretation.Map A)).trans
      (sorealize_pullSO f.toInterpretation A Bs φ true)
  · obtain ⟨Bs, hk, φ, hφ⟩ := hT
    refine piSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
      (by simpa [pullBlocks] using hk)
      (pullSO Bs (L.sum Language.order) L' f.toInterpretation φ) ?_
    intro A _ _ _
    refine forall_congr' fun lo => ?_
    let := lo
    have := f.toInterpretation.map_finite A
    have := f.toInterpretation.map_nonempty A
    exact (hφ (f.toInterpretation.Map A)).trans
      (sorealize_pullSO f.toInterpretation A Bs φ false)
  · intro A _ _ _
    constructor
    · intro hP
      refine ⟨⟨finiteLinearOrder A, ?_⟩, fun lo => ?_⟩
      · let := finiteLinearOrder A
        have := f.toInterpretation.map_finite A
        have := f.toInterpretation.map_nonempty A
        exact ((hST _).mp ((f.correct A).mp hP)).1
      · let := lo
        have := f.toInterpretation.map_finite A
        have := f.toInterpretation.map_nonempty A
        exact ((hST _).mp ((f.correct A).mp hP)).2
    · rintro ⟨⟨lo, hS'⟩, hT'⟩
      let := lo
      have := f.toInterpretation.map_finite A
      have := f.toInterpretation.map_nonempty A
      exact (f.correct A).mpr ((hST _).mpr ⟨hS', hT' lo⟩)

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.Difference.DPDefinable

export Lax564036Proofs.DescriptiveComplexity.DPDefinable (of_orderedReduction)

end Lax564036.Difference.DPDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

variable [L.IsRelational]

/-! ### DP inside the second level

The `Σ` half's guess and the `Π` half's challenge become the two blocks of a
single alternation. The two kernels live over different expansions of the
vocabulary, so each is transported into the doubly expanded one: the head
kernel by `DescriptiveComplexity.soLangEmbed`, the other by
`DescriptiveComplexity.soLangLift` along `LHom.sumInl`, which is an expansion on a
sum structure. -/

section Merge

variable {P : Lax904597.Problems.DecisionProblem L}

private theorem eq_singleton_of_length_one {Bs : List Lax904597.SecondOrder.SOBlock} (h : Bs.length = 1) :
    ∃ B, Bs = [B] := by
  cases Bs with
  | nil => simp at h
  | cons B t =>
    cases t with
    | nil => exact ⟨B, rfl⟩
    | cons _ _ => simp at h

/-- **DP ⊆ Σ₂ᵖ**: `(∃X. φ) ∧ (∀Y. ψ)` is the single alternation
`∃X ∀Y. (φ ∧ ψ)`. Nothing has to be guessed twice – the `Π` kernel does not
mention `X`, which is what makes the conjunction slide inside both
quantifiers. -/
theorem DPDefinable.sigmaSODefinable_two (h : Lax564036.Difference.DPDefinable P) : Lax904597.SecondOrder.SigmaSODefinable 2 P := by
  obtain ⟨S, T, hS, hT, hST⟩ := h
  obtain ⟨Bs₁, hk1, φ, hφ⟩ := hS
  obtain ⟨Bs₂, hk2, ψ, hψ⟩ := hT
  obtain ⟨B₁, rfl⟩ := eq_singleton_of_length_one hk1
  obtain ⟨B₂, rfl⟩ := eq_singleton_of_length_one hk2
  refine ⟨[B₁, B₂], rfl,
    (soLangEmbed [B₂] (L.sum B₁.lang)).onSentence φ ⊓
      (soLangLift [B₂] L (L.sum B₁.lang) LHom.sumInl).onSentence ψ, ?_⟩
  intro A instA _ _
  refine (hST A).trans ?_
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨ρ₁, hρ₁⟩ := (hφ A).mp hs
    let := B₁.structure ρ₁
    refine ⟨ρ₁, (sorealize_inf_embed [B₂] (L.sum B₁.lang) A _ φ _ false).mpr ⟨hρ₁, ?_⟩⟩
    exact (sorealize_soLangLift [B₂] L (L.sum B₁.lang) LHom.sumInl A instA _
      (LHom.sumInl_isExpansionOn A) ψ false).mpr ((hψ A).mp ht)
  · rintro ⟨ρ₁, hρ₁⟩
    let := B₁.structure ρ₁
    obtain ⟨hf, hg⟩ := (sorealize_inf_embed [B₂] (L.sum B₁.lang) A _ φ _ false).mp hρ₁
    refine ⟨(hφ A).mpr ⟨ρ₁, hf⟩, (hψ A).mpr ?_⟩
    exact (sorealize_soLangLift [B₂] L (L.sum B₁.lang) LHom.sumInl A instA _
      (LHom.sumInl_isExpansionOn A) ψ false).mp hg

end Merge

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.Difference.DPDefinable

export Lax564036Proofs.DescriptiveComplexity.DPDefinable (sigmaSODefinable_two)

end Lax564036.Difference.DPDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

variable [L.IsRelational]

section Merge

variable {P : Lax904597.Problems.DecisionProblem L}

/-- **DP ⊆ Π₂ᵖ**, the same merge with the blocks in the other order:
`∀Y ∃X. (φ ∧ ψ)`. Recovering the `Σ` half from it uses that a block always has
*some* assignment – the constantly true one will do. -/
theorem DPDefinable.piSODefinable_two (h : Lax564036.Difference.DPDefinable P) : Lax904597.SecondOrder.PiSODefinable 2 P := by
  obtain ⟨S, T, hS, hT, hST⟩ := h
  obtain ⟨Bs₁, hk1, φ, hφ⟩ := hS
  obtain ⟨Bs₂, hk2, ψ, hψ⟩ := hT
  obtain ⟨B₁, rfl⟩ := eq_singleton_of_length_one hk1
  obtain ⟨B₂, rfl⟩ := eq_singleton_of_length_one hk2
  refine ⟨[B₂, B₁], rfl,
    (soLangEmbed [B₁] (L.sum B₂.lang)).onSentence ψ ⊓
      (soLangLift [B₁] L (L.sum B₂.lang) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  refine (hST A).trans ?_
  constructor
  · rintro ⟨hs, ht⟩ ρ₂
    let := B₂.structure ρ₂
    refine (sorealize_inf_embed [B₁] (L.sum B₂.lang) A _ ψ _ true).mpr ⟨(hψ A).mp ht ρ₂, ?_⟩
    exact (sorealize_soLangLift [B₁] L (L.sum B₂.lang) LHom.sumInl A instA _
      (LHom.sumInl_isExpansionOn A) φ true).mpr ((hφ A).mp hs)
  · intro hall
    have hs : S A := by
      let := B₂.structure (fun _ _ => True : B₂.Assignment A)
      obtain ⟨-, hg⟩ := (sorealize_inf_embed [B₁] (L.sum B₂.lang) A _ ψ _ true).mp
        (hall (fun _ _ => True))
      exact (hφ A).mpr ((sorealize_soLangLift [B₁] L (L.sum B₂.lang) LHom.sumInl A instA _
        (LHom.sumInl_isExpansionOn A) φ true).mp hg)
    exact ⟨hs, (hψ A).mpr fun ρ₂ =>
      ((sorealize_inf_embed [B₁] (L.sum B₂.lang) A _ ψ _ true).mp (hall ρ₂)).1⟩

end Merge

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.Difference.DPDefinable

export Lax564036Proofs.DescriptiveComplexity.DPDefinable (piSODefinable_two)

end Lax564036.Difference.DPDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

variable [L.IsRelational]

section Merge

variable {P : Lax904597.Problems.DecisionProblem L}

end Merge

/-! ### The class -/

/-- **The class DP** ([Papadimitriou & Yannakakis
1984][papadimitriou1984complexity]): the conjunctions of an NP condition and a
coNP one. Hardness is stated cofinally, as for the other classes of this
library (`DescriptiveComplexity.CofinalHard`). -/
noncomputable def DP : ComplexityClass :=
  .ofMem (fun P => Lax564036.Difference.DPDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => dpDefinable_congr h)

/-- Membership in DP is exactly DP definability, by definition. -/
theorem mem_DP_iff (P : Lax904597.Problems.DecisionProblem L) : P ∈ DP ↔ Lax564036.Difference.DPDefinable P :=
  Iff.rfl

/-! ### NP and coNP inside DP

Both inclusions take the other half of the conjunction to be trivial: an NP
condition alone is an NP condition conjoined with the tautology, and dually. -/

/-- The trivially true problem, the unit of conjunction. -/
def DecisionProblem.triv (L : Language.{0, 0}) [L.IsRelational] : Lax904597.Problems.DecisionProblem L where
  Holds _ _ := True
  iso_invariant _ := Iff.rfl

end Lax564036Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax564036Proofs.DescriptiveComplexity.DecisionProblem (triv)

end Lax904597.Problems.DecisionProblem

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

variable [L.IsRelational]

/-- A one-variable block, to carry the tautological kernel of the trivial
problem: a `Σ₁` or `Π₁` witness needs a block to quantify, even an idle one. -/
private def trivBlock : Lax904597.SecondOrder.SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The trivial problem is `Σ₁`-definable: guess nothing, check nothing. -/
theorem sigmaSODefinable_triv : Lax904597.SecondOrder.SigmaSODefinable 1 (DecisionProblem.triv L) := by
  refine ⟨[trivBlock], rfl, ⊤, ?_⟩
  intro A _ _ _
  refine ⟨fun _ => ⟨fun _ _ => True, ?_⟩, fun _ => trivial⟩
  exact fun h => h

/-- The trivial problem is `Π₁`-definable. -/
theorem piSODefinable_triv : Lax904597.SecondOrder.PiSODefinable 1 (DecisionProblem.triv L) := by
  refine ⟨[trivBlock], rfl, ⊤, ?_⟩
  intro A _ _ _
  refine ⟨fun _ _ => ?_, fun _ => trivial⟩
  exact fun h => h

/-- **NP ⊆ DP**: an NP condition is itself a DP condition, conjoined with the
tautology. -/
theorem NP_subset_DP : NP ⊆ DP := by
  intro L _ P hP
  exact ⟨P, DecisionProblem.triv L, hP, piSODefinable_triv,
    fun A _ _ _ => ⟨fun h => ⟨h, trivial⟩, And.left⟩⟩

/-- **coNP ⊆ DP**, the mirror image. -/
theorem coNP_subset_DP : coNP ⊆ DP := by
  intro L _ P hP
  exact ⟨DecisionProblem.triv L, P, sigmaSODefinable_triv, hP,
    fun A _ _ _ => ⟨fun h => ⟨trivial, h⟩, And.right⟩⟩

/-- **DP ⊆ Σ₂ᵖ**, as an inclusion of classes. -/
theorem DP_subset_sigmaP_two : DP ⊆ SigmaP 2 :=
  fun _ _ _ hP => DPDefinable.sigmaSODefinable_two ((mem_DP_iff _).mp hP)

/-- **DP ⊆ Π₂ᵖ**, as an inclusion of classes: DP sits inside the second level
of the hierarchy from both sides. -/
theorem DP_subset_piP_two : DP ⊆ PiP 2 :=
  fun _ _ _ hP => DPDefinable.piSODefinable_two ((mem_DP_iff _).mp hP)

/-- Over a relational vocabulary, DP-hardness is the usual notion: every
DP-definable problem reduces to `P`. -/
theorem hard_DP_iff (P : Lax904597.Problems.DecisionProblem L) :
    DP.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
        Lax564036.Difference.DPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

end Lax564036Proofs.DescriptiveComplexity


