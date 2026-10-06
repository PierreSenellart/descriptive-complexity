/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.SecondOrderPull
import Lax175070Proofs.DescriptiveComplexity.SecondOrderLift
import Lax175070Proofs.DescriptiveComplexity.OrderedComposition
import Mathlib.Tactic.FinCases
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity.PiSODefinable
end Lax175070Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax175070Proofs.DescriptiveComplexity.SOBlock
end Lax175070Proofs.DescriptiveComplexity.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax175070Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable soLang)
end Lax175070Proofs.DescriptiveComplexity

/-!
# Closure of second-order definability under ordered FO reductions

If `P ≤ᶠᵒ[≤] Q` and `Q` is `Σₖ₊₁`- (resp. `Πₖ₊₁`-) definable, then so is `P`
(`DescriptiveComplexity.SigmaSODefinable.of_orderedReduction`,
`DescriptiveComplexity.PiSODefinable.of_orderedReduction`).

Pulling the defining sentence back through the interpretation
(`DescriptiveComplexity.SecondOrderPull`) yields a sentence over the *ordered*
expansion `L.sum Language.order` – correct for every linear order on the
input, by order-invariance of the reduction. The order is then eliminated by
re-quantifying it inside the first second-order block:

* the first block is extended with one binary relation variable, the order
  (`DescriptiveComplexity.SOBlock.withOrder`);
* the sentence is transported along the language morphism
  `DescriptiveComplexity.orderElimLHom` mapping the order symbol to the new variable;
* it is guarded by the first-order sentence `DescriptiveComplexity.linearGuard` stating
  that the variable is a linear order – as a conjunct if the block is
  existential (`Σₖ₊₁`), as a premise if it is universal (`Πₖ₊₁`).

Correctness of the guard uses `DescriptiveComplexity.linearOrderOfGuard` to promote a
guarded relation variable to an actual `LinearOrder` instance, and the
order-invariance clause of `OrderedFOReduction.correct` to connect different
choices of the order. This requires at least one second-order block to
piggyback on, whence the level `k + 1`.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Adding an order variable to a block -/

/-- The block `B` extended with one extra binary relation variable, used to
re-quantify the order of an ordered reduction. -/
def SOBlock.withOrder (B : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock where
  ι := Unit ⊕ B.ι
  arity := Sum.elim (fun _ => 2) B.arity

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (withOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order variable of the extended block. -/
def SOBlock.orderSym (B : Lax904597.SecondOrder.SOBlock) : B.withOrder.lang.Relations 2 :=
  ⟨Sum.inl (), rfl⟩

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (orderSym)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The order variable, as a relation symbol of the expanded language. -/
abbrev ordVarSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) :
    (L.sum B.withOrder.lang).Relations 2 :=
  Sum.inr B.orderSym

variable {A : Type}

/-- The assignment of the original block variables underlying an assignment
of the extended block. -/
def SOBlock.restPart (B : Lax904597.SecondOrder.SOBlock) (ρ : B.withOrder.Assignment A) : B.Assignment A :=
  fun i => ρ (Sum.inr i)

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (restPart)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-- The assignment of the extended block determined by a binary relation (for
the order variable) and an assignment of the original block. -/
def SOBlock.joinOrder (B : Lax904597.SecondOrder.SOBlock) (R : (Fin 2 → A) → Prop) (ρ : B.Assignment A) :
    B.withOrder.Assignment A :=
  fun p => match p with
    | Sum.inl _ => R
    | Sum.inr i => ρ i

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax175070Proofs.DescriptiveComplexity.SOBlock (joinOrder)

end Lax904597.SecondOrder.SOBlock

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

/-! ### The linear-order guard -/

section Guard

variable (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock)

/-- `x ≤ y` for the order variable, as a formula over the expanded
language. -/
private def leVF {α : Type} (x y : α) : (L.sum B.withOrder.lang).Formula α :=
  Relations.formula₂ (ordVarSym L B) (Term.var x) (Term.var y)

/-- The order variable is reflexive. -/
private noncomputable def reflS : (L.sum B.withOrder.lang).Sentence :=
  (leVF L B (Sum.inr 0) (Sum.inr 0)).iAlls (Fin 1)

/-- The order variable is transitive. -/
private noncomputable def transS : (L.sum B.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 3)
    (leVF L B (Sum.inr 0) (Sum.inr 1) ⊓ leVF L B (Sum.inr 1) (Sum.inr 2) ⟹
      leVF L B (Sum.inr 0) (Sum.inr 2))

/-- The order variable is antisymmetric. -/
private noncomputable def antisymmS : (L.sum B.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
    (leVF L B (Sum.inr 0) (Sum.inr 1) ⊓ leVF L B (Sum.inr 1) (Sum.inr 0) ⟹
      Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- The order variable is total. -/
private noncomputable def totalS : (L.sum B.withOrder.lang).Sentence :=
  (leVF L B (Sum.inr 0) (Sum.inr 1) ⊔ leVF L B (Sum.inr 1) (Sum.inr 0)).iAlls (Fin 2)

/-- The guard sentence: the order variable is (reflexive, transitive,
antisymmetric and total, i.e.,) a linear order. -/
noncomputable def linearGuard : (L.sum B.withOrder.lang).Sentence :=
  reflS L B ⊓ (transS L B ⊓ (antisymmS L B ⊓ totalS L B))

/-- Realization of the guard: the four linear-order axioms for the relation
assigned to the order variable. -/
theorem realize_linearGuard (instA : L.Structure A) (ρ : B.withOrder.Assignment A) :
    @Sentence.Realize _ A
        (@sumStructure L B.withOrder.lang A instA (B.withOrder.structure ρ))
        (linearGuard L B) ↔
      ((∀ a : A, ρ (Sum.inl ()) ![a, a]) ∧
        ((∀ a b c : A, ρ (Sum.inl ()) ![a, b] → ρ (Sum.inl ()) ![b, c] →
            ρ (Sum.inl ()) ![a, c]) ∧
          ((∀ a b : A, ρ (Sum.inl ()) ![a, b] → ρ (Sum.inl ()) ![b, a] → a = b) ∧
            (∀ a b : A, ρ (Sum.inl ()) ![a, b] ∨ ρ (Sum.inl ()) ![b, a])))) := by
  let := instA
  let := B.withOrder.structure ρ
  have hsub : ∀ (w : Fin 2 → A),
      RelMap (L := L.sum B.withOrder.lang) (M := A) (ordVarSym L B) w ↔
        ρ (Sum.inl ()) w := fun w => Iff.rfl
  simp only [linearGuard, reflS, transS, antisymmS, totalS, leVF, Sentence.Realize,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr, hsub]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩
  · exact ⟨fun h a b c hab hbc => h ![a, b, c] ⟨hab, hbc⟩,
      fun h i hp => h (i 0) (i 1) (i 2) hp.1 hp.2⟩
  · exact ⟨fun h a b hab hba => h ![a, b] ⟨hab, hba⟩,
      fun h i hp => h (i 0) (i 1) hp.1 hp.2⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩

end Guard

/-! ### Promoting a guarded order variable to a linear order -/

private theorem vec_eta₂ (w : Fin 2 → A) : ![w 0, w 1] = w := by
  funext j
  fin_cases j <;> simp

/-- A binary relation variable satisfying the guard axioms determines a
linear order (decidability by choice). -/
@[instance_reducible]
noncomputable def linearOrderOfGuard (r : (Fin 2 → A) → Prop)
    (hrefl : ∀ a : A, r ![a, a])
    (htrans : ∀ a b c : A, r ![a, b] → r ![b, c] → r ![a, c])
    (hantisymm : ∀ a b : A, r ![a, b] → r ![b, a] → a = b)
    (htotal : ∀ a b : A, r ![a, b] ∨ r ![b, a]) : LinearOrder A where
  le a b := r ![a, b]
  le_refl := hrefl
  le_trans := htrans
  le_antisymm := hantisymm
  le_total := htotal
  toDecidableLE := fun _ _ => Classical.propDecidable _

/-! ### Eliminating the order symbol -/

/-- The language morphism eliminating the order symbol of the ordered
expansion in favor of the order variable of the extended block. -/
def orderElimLHom (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) :
    (L.sum Language.order).sum B.lang →ᴸ L.sum B.withOrder.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl g
    | Sum.inl (Sum.inr g) => nomatch g
    | Sum.inr g => nomatch g
  onRelation {n} r :=
    match n, r with
    | _, Sum.inl (Sum.inl s) => Sum.inl s
    | _, Sum.inl (Sum.inr .le) => ordVarSym L B
    | _, Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

/-- When the order variable is assigned (a relation equivalent to) the linear
order of the structure, the extended structure is an expansion along
`orderElimLHom` of the ordered structure extended by the underlying
assignment. -/
theorem orderElimLHom_isExpansionOn (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (A : Type)
    (instA : L.Structure A) (lo : LinearOrder A) (ρ : B.withOrder.Assignment A)
    (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1) :
    @LHom.IsExpansionOn _ _ (orderElimLHom L B) A
      (@sumStructure (L.sum Language.order) B.lang A
        (letI := instA; letI := lo; Lax904597.Interpretations.sumOrderStructure L A)
        (B.structure (B.restPart ρ)))
      (@sumStructure L B.withOrder.lang A instA (B.withOrder.structure ρ)) := by
  let := instA
  let := lo
  let := B.structure (B.restPart ρ)
  let := B.withOrder.structure ρ
  exact
    { map_onFunction := fun {n} f x => by
        match f with
        | Sum.inl (Sum.inl g) => rfl
        | Sum.inl (Sum.inr g) => exact nomatch g
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {n} r x => by
        match n, r with
        | _, Sum.inl (Sum.inl s) => rfl
        | _, Sum.inl (Sum.inr .le) => exact propext (hord x)
        | _, Sum.inr s => rfl }

/-! ### Order elimination, as a statement about sentences

The two theorems below are the order-elimination construction on its own,
separated from the reduction that usually produces the sentence: a problem
defined – over the *ordered* expansion, so with the order visible to the
sentence – by a `Σₖ₊₁` sentence *for some* linear order, or by a `Πₖ₊₁`
sentence *for every* linear order, is definable at that level over the bare
vocabulary. The closure theorems of the next section are the case where the
sentence comes from pulling a definition back through an ordered reduction,
where order-invariance makes “for some” and “for every” agree.

Stated this way the construction also applies where no single order-invariant
problem is in sight – to each half of a `DescriptiveComplexity.DPDefinable`
definition separately, say, whose two halves are *not* individually
order-invariant. -/

section OrderPull

variable {L₁ : Language.{0, 0}} [L₁.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {k : ℕ}

/-- **Order elimination, existentially**: a problem defined by a `Σₖ₊₁`
sentence over the ordered expansion, correct for *some* linear order on each
instance, is `Σₖ₊₁`-definable. The order is re-quantified inside the first
block, guarded by a conjunct stating that it is a linear order. -/
theorem sigmaSODefinable_of_orderPull (Cs : List Lax904597.SecondOrder.SOBlock) (hk : Cs.length = k + 1)
    (χ : (Lax904597.SecondOrder.soLang (L₁.sum Language.order) Cs).Sentence)
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ lo : LinearOrder A,
        letI := lo
        Lax904597.SecondOrder.SORealize (L₁.sum Language.order) A Cs χ true) :
    Lax904597.SecondOrder.SigmaSODefinable (k + 1) P := by
  cases Cs with
  | nil => exact absurd hk (by simp)
  | cons C₀ Cs' =>
    refine ⟨C₀.withOrder :: Cs', by simpa using hk,
      (soLangEmbed Cs' (L₁.sum C₀.withOrder.lang)).onSentence (linearGuard L₁ C₀) ⊓
        (soLangLift Cs' ((L₁.sum Language.order).sum C₀.lang)
            (L₁.sum C₀.withOrder.lang) (orderElimLHom L₁ C₀)).onSentence χ, ?_⟩
    intro A instA _ _
    constructor
    · intro hP
      obtain ⟨lo, ρ₀, hρ₀⟩ := (h A).mp hP
      let := lo
      refine ⟨C₀.joinOrder (fun w => w 0 ≤ w 1) ρ₀, ?_⟩
      refine (sorealize_inf_embed Cs' (L₁.sum C₀.withOrder.lang) A _
        (linearGuard L₁ C₀) _ false).mpr ⟨?_, ?_⟩
      · exact (realize_linearGuard L₁ C₀ instA _).mpr
          ⟨fun a => le_refl a, fun a b c hab hbc => le_trans hab hbc,
            fun a b hab hba => le_antisymm hab hba, fun a b => le_total a b⟩
      · exact (sorealize_soLangLift Cs' _ _ (orderElimLHom L₁ C₀) A _ _
          (orderElimLHom_isExpansionOn L₁ C₀ A instA lo
            (C₀.joinOrder (fun w => w 0 ≤ w 1) ρ₀)
            (fun _ => Iff.rfl)) _ false).mpr hρ₀
    · rintro ⟨ρ'', hρ''⟩
      obtain ⟨hguard, hrest⟩ := (sorealize_inf_embed Cs' (L₁.sum C₀.withOrder.lang) A _
        (linearGuard L₁ C₀) _ false).mp hρ''
      obtain ⟨h1, h2, h3, h4⟩ := (realize_linearGuard L₁ C₀ instA ρ'').mp hguard
      let lo := linearOrderOfGuard (ρ'' (Sum.inl ())) h1 h2 h3 h4
      refine (h A).mpr ⟨lo, C₀.restPart ρ'', ?_⟩
      exact (sorealize_soLangLift Cs' _ _ (orderElimLHom L₁ C₀) A _ _
        (orderElimLHom_isExpansionOn L₁ C₀ A instA lo ρ''
          (fun w => (iff_of_eq (congrArg (ρ'' (Sum.inl ())) (vec_eta₂ w))).symm))
        _ false).mp hrest

/-- **Order elimination, universally**: a problem defined by a `Πₖ₊₁` sentence
over the ordered expansion, correct for *every* linear order on each instance,
is `Πₖ₊₁`-definable. The order is re-quantified inside the first block, guarded
as the premise of an implication. -/
theorem piSODefinable_of_orderPull (Cs : List Lax904597.SecondOrder.SOBlock) (hk : Cs.length = k + 1)
    (χ : (Lax904597.SecondOrder.soLang (L₁.sum Language.order) Cs).Sentence)
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∀ lo : LinearOrder A,
        letI := lo
        Lax904597.SecondOrder.SORealize (L₁.sum Language.order) A Cs χ false) :
    Lax904597.SecondOrder.PiSODefinable (k + 1) P := by
  cases Cs with
  | nil => exact absurd hk (by simp)
  | cons C₀ Cs' =>
    refine ⟨C₀.withOrder :: Cs', by simpa using hk,
      (soLangEmbed Cs' (L₁.sum C₀.withOrder.lang)).onSentence (linearGuard L₁ C₀) ⟹
        (soLangLift Cs' ((L₁.sum Language.order).sum C₀.lang)
            (L₁.sum C₀.withOrder.lang) (orderElimLHom L₁ C₀)).onSentence χ, ?_⟩
    intro A instA _ _
    constructor
    · intro hP ρ''
      refine (sorealize_imp_embed Cs' (L₁.sum C₀.withOrder.lang) A _
        (linearGuard L₁ C₀) _ true).mpr fun hguard => ?_
      obtain ⟨h1, h2, h3, h4⟩ := (realize_linearGuard L₁ C₀ instA ρ'').mp hguard
      let lo := linearOrderOfGuard (ρ'' (Sum.inl ())) h1 h2 h3 h4
      have hinner := (h A).mp hP lo (C₀.restPart ρ'')
      exact (sorealize_soLangLift Cs' _ _ (orderElimLHom L₁ C₀) A _ _
        (orderElimLHom_isExpansionOn L₁ C₀ A instA lo ρ''
          (fun w => (iff_of_eq (congrArg (ρ'' (Sum.inl ())) (vec_eta₂ w))).symm))
        _ true).mpr hinner
    · intro hall
      refine (h A).mpr fun lo ρ₀ => ?_
      let := lo
      have hguard := (realize_linearGuard L₁ C₀ instA
          (C₀.joinOrder (fun w => w 0 ≤ w 1) ρ₀)).mpr
        ⟨fun a => le_refl a, fun a b c hab hbc => le_trans hab hbc,
          fun a b hab hba => le_antisymm hab hba, fun a b => le_total a b⟩
      have hinner := (sorealize_imp_embed Cs' (L₁.sum C₀.withOrder.lang) A _
        (linearGuard L₁ C₀) _ true).mp
        (hall (C₀.joinOrder (fun w => w 0 ≤ w 1) ρ₀)) hguard
      exact (sorealize_soLangLift Cs' _ _ (orderElimLHom L₁ C₀) A _ _
        (orderElimLHom_isExpansionOn L₁ C₀ A instA lo
          (C₀.joinOrder (fun w => w 0 ≤ w 1) ρ₀)
          (fun _ => Iff.rfl)) _ true).mp hinner

end OrderPull

/-! ### Closure of the definability levels under ordered FO reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {k : ℕ}

/-- `Σₖ₊₁`-definability is closed under ordered FO reductions: the order is
re-quantified existentially inside the first block, guarded by a conjunct
stating that it is a linear order. Order-invariance of the reduction is what
lets `DescriptiveComplexity.sigmaSODefinable_of_orderPull` be applied: the pulled-back
sentence is correct not merely for *some* order but for every one.
Registered in the Lax archive (for `NP`) as
[`Lax904597.NPClass.NP_mem_of_orderedReduction`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.NP_mem_of_orderedReduction). -/
theorem SigmaSODefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : Lax904597.SecondOrder.SigmaSODefinable (k + 1) Q) : Lax904597.SecondOrder.SigmaSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine sigmaSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
    (by simpa [pullBlocks] using hk)
    (pullSO Bs (L₁.sum Language.order) L₂ f.toInterpretation φ) ?_
  intro A _ _ _
  have hpull : ∀ lo : LinearOrder A,
      letI := lo
      (P A ↔ Lax904597.SecondOrder.SORealize (L₁.sum Language.order) A (pullBlocks f.Tag f.dim Bs)
        (pullSO Bs (L₁.sum Language.order) L₂ f.toInterpretation φ) true) := by
    intro lo
    let := lo
    have := f.toInterpretation.map_finite A
    have := f.toInterpretation.map_nonempty A
    exact (f.correct A).trans ((hφ (f.toInterpretation.Map A)).trans
      (sorealize_pullSO f.toInterpretation A Bs φ true))
  exact ⟨fun hP => ⟨finiteLinearOrder A, (hpull _).mp hP⟩,
    fun hex => (hpull hex.choose).mpr hex.choose_spec⟩

end Closure

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SigmaSODefinable

export Lax175070Proofs.DescriptiveComplexity.SigmaSODefinable (of_orderedReduction)

end Lax904597.SecondOrder.SigmaSODefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {k : ℕ}

/-- `Πₖ₊₁`-definability is closed under ordered FO reductions: the order is
re-quantified universally inside the first block, guarded as the premise of
an implication. -/
theorem PiSODefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : Lax904597.SecondOrder.PiSODefinable (k + 1) Q) : Lax904597.SecondOrder.PiSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine piSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
    (by simpa [pullBlocks] using hk)
    (pullSO Bs (L₁.sum Language.order) L₂ f.toInterpretation φ) ?_
  intro A _ _ _
  have hpull : ∀ lo : LinearOrder A,
      letI := lo
      (P A ↔ Lax904597.SecondOrder.SORealize (L₁.sum Language.order) A (pullBlocks f.Tag f.dim Bs)
        (pullSO Bs (L₁.sum Language.order) L₂ f.toInterpretation φ) false) := by
    intro lo
    let := lo
    have := f.toInterpretation.map_finite A
    have := f.toInterpretation.map_nonempty A
    exact (f.correct A).trans ((hφ (f.toInterpretation.Map A)).trans
      (sorealize_pullSO f.toInterpretation A Bs φ false))
  exact ⟨fun hP lo => (hpull lo).mp hP,
    fun hall => (hpull (finiteLinearOrder A)).mpr (hall _)⟩

end Closure

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.PiSODefinable

export Lax175070Proofs.DescriptiveComplexity.PiSODefinable (of_orderedReduction)

end Lax904597.SecondOrder.PiSODefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type}

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂} {k : ℕ}

end Closure

end Lax175070Proofs.DescriptiveComplexity


