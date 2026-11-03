/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.SecondOrder
import Lax832283Proofs.DescriptiveComplexity.Strings.FirstOrder
import Lax832283Proofs.DescriptiveComplexity.Strings.Transport
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
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax988886.ExistentialSecondOrder
end Lax988886.ExistentialSecondOrder

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (Interpretation Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
export Lax988886.ExistentialSecondOrder (Definable FirstOrder Satisfies)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab ofOrdered toProperty)
end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax832283Proofs.DescriptiveComplexity

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize SigmaSODefinable)
end Lax832283Proofs.DescriptiveComplexity

/-!
# Existential second-order definability, in both formalisms

`DescriptiveComplexity.Strings.sigmaSODefinable_one_iff`: a decision problem of the
library is `Σ₁`-definable exactly when the property it reads as on the archive's
structures is definable by an existential second-order sentence of the archive.

The two formalisms differ in their treatment of the empty structure only, which the
library's classes do not see and which `DescriptiveComplexity.Strings.toProperty`
makes a no-instance: the forward translation conjoins “the universe is nonempty” to
its matrix.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder Language Structure

open Lax.OrderedStructures Lax.FiniteStructures Lax.ExistentialSecondOrder

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### From a block to a witness vocabulary -/

section Forward

variable (V : Lax832283.StringProblems.FinVocab L) (B : Lax904597.SecondOrder.SOBlock) {m₀ : ℕ} (e : B.ι ≃ Fin m₀)

/-- The witness vocabulary of a block, along a numbering of its variables. -/
def witVoc : Lax988886.FiniteStructures.Vocabulary :=
  List.ofFn (B.arity ∘ e.symm)

/-- The witness symbol of a relation variable. -/
def wit (i : B.ι) : Fin (witVoc B e).length :=
  Fin.cast (List.length_ofFn ..).symm (e i)

theorem witVoc_get_wit (i : B.ι) : (witVoc B e).get (wit B e i) = B.arity i := by
  simp [witVoc, wit]

/-- The relation variable of a witness symbol. -/
def witVar (r : Fin (witVoc B e).length) : B.ι :=
  e.symm (Fin.cast (List.length_ofFn ..) r)

theorem witVoc_get (r : Fin (witVoc B e).length) : B.arity (witVar B e r) = (witVoc B e).get r := by
  exact (List.get_ofFn (B.arity ∘ e.symm) r).symm

theorem witVar_wit (i : B.ι) : witVar B e (wit B e i) = i := by
  have h : Fin.cast (List.length_ofFn ..) (wit B e i) = e i := Fin.ext rfl
  rw [witVar, h, e.symm_apply_apply]

/-- The atoms of the forward translation. -/
def esoAtom {m n : ℕ} : (L.sum B.lang).Relations n → (Fin n → Fin m) →
    Lax988886.ExistentialSecondOrder.FirstOrder V.σ (witVoc B e) m
  | .inl R, a => .relation (V.toSym R) (a ∘ Fin.cast (V.arity_toSym R))
  | .inr R, a => .variable (wit B e R.1)
      (a ∘ Fin.cast ((witVoc_get_wit B e R.1).trans R.2))

/-- The forward translation of a matrix. -/
def esoMatrix (φ : (L.sum B.lang).Sentence) : Lax988886.ExistentialSecondOrder.FirstOrder V.σ (witVoc B e) 0 :=
  .conj (.exists' .truth)
    ((esoAlg V.σ (witVoc B e) (esoAtom V B e)).tr φ (Sum.elim Empty.elim Fin.elim0))

open Classical in
/-- An interpretation of the witness vocabulary from an assignment of the block. -/
noncomputable def interpOf {n : ℕ} (ρ : B.Assignment (Fin n)) : Lax988886.FiniteStructures.Interpretation (witVoc B e) n :=
  fun r a => decide (ρ (witVar B e r) (a ∘ Fin.cast (witVoc_get B e r)))

/-- An assignment of the block from an interpretation of the witness vocabulary. -/
def assignOf {n : ℕ} (R : Lax988886.FiniteStructures.Interpretation (witVoc B e) n) : B.Assignment (Fin n) :=
  fun i x => R (wit B e i) (x ∘ Fin.cast (witVoc_get_wit B e i)) = true

open Classical in
private theorem interpOf_wit {n : ℕ} (ρ : B.Assignment (Fin n)) (i : B.ι) {k : ℕ}
    (h : (witVoc B e).get (wit B e i) = k) (hi : B.arity i = k) (x : Fin k → Fin n) :
    interpOf B e ρ (wit B e i) (x ∘ Fin.cast h) = true ↔ ρ i (x ∘ Fin.cast hi) := by
  have key : ∀ (i' : B.ι) (hi' : i' = i) (hk : B.arity i' = k),
      ρ i' (x ∘ Fin.cast hk) ↔ ρ i (x ∘ Fin.cast hi) := by
    rintro _ rfl _; exact Iff.rfl
  refine decide_eq_true_iff.trans ?_
  exact key _ (witVar_wit B e i) (by rw [witVar_wit]; exact hi)

variable (S : Lax751879.OrderedStructures.OrderedStructure V.σ) {n : ℕ}

private theorem esoSem (ρ : B.Assignment (Fin S.size)) (R : Lax988886.FiniteStructures.Interpretation (witVoc B e) S.size)
    (hR : ∀ i {k} (h : (witVoc B e).get (wit B e i) = k) (hi : B.arity i = k)
      (x : Fin k → Fin S.size),
      R (wit B e i) (x ∘ Fin.cast h) = true ↔ ρ i (x ∘ Fin.cast hi)) :
    letI := Lax832283.StringProblems.ofOrdered V S
    letI := B.structure ρ
    (esoAlg V.σ (witVoc B e) (esoAtom V B e)).Sem (Fin S.size)
      (fun φ w => Lax988886.ExistentialSecondOrder.FirstOrder.eval φ S R w) := by
  let := Lax832283.StringProblems.ofOrdered V S
  let := B.structure ρ
  refine { truth := fun _ => trivial, equal := fun _ _ _ => Iff.rfl, atom := ?_,
           neg := fun _ _ => Iff.rfl, conj := fun _ _ _ => Iff.rfl, ex := ?_, ext := ?_ }
  · rintro m k (Q | Q) a w
    · exact Iff.rfl
    · refine (hR Q.1 _ Q.2 (w ∘ a)).trans ?_
      change _ ↔ ρ Q.1 fun j => (w ∘ a) (Fin.cast Q.2 j)
      exact Iff.rfl
  · intro m φ w
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.cons a w, rfl, ha⟩
    · rintro ⟨w', rfl, ha⟩
      refine ⟨w' 0, ?_⟩
      have : (Fin.cons (w' 0) (w' ∘ Fin.succ) : Fin (m + 1) → _) = w' := Fin.cons_self_tail w'
      change Lax988886.ExistentialSecondOrder.FirstOrder.eval φ S R (Fin.cons (w' 0) (w' ∘ Fin.succ))
      rw [this]
      exact ha
  · intro m a w
    exact ⟨Fin.cons a w, rfl, rfl⟩

/-- The forward translation of a matrix is correct, at a nonempty size. -/
theorem eval_esoMatrix (hS : 0 < S.size) (φ : (L.sum B.lang).Sentence)
    (ρ : B.Assignment (Fin S.size)) (R : Lax988886.FiniteStructures.Interpretation (witVoc B e) S.size)
    (hR : ∀ i {k} (h : (witVoc B e).get (wit B e i) = k) (hi : B.arity i = k)
      (x : Fin k → Fin S.size),
      R (wit B e i) (x ∘ Fin.cast h) = true ↔ ρ i (x ∘ Fin.cast hi)) :
    (esoMatrix V B e φ).eval S R Fin.elim0 ↔
      @Sentence.Realize _ (Fin S.size)
        (@sumStructure L B.lang _ (Lax832283.StringProblems.ofOrdered V S) (B.structure ρ)) φ := by
  let := Lax832283.StringProblems.ofOrdered V S
  let := B.structure ρ
  have h := (esoSem V B e S ρ R hR).eval_tr φ (Sum.elim Empty.elim Fin.elim0) Fin.elim0
  have hne : (Lax988886.ExistentialSecondOrder.FirstOrder.exists' Lax988886.ExistentialSecondOrder.FirstOrder.truth : Lax988886.ExistentialSecondOrder.FirstOrder V.σ (witVoc B e) 0).eval S R
      Fin.elim0 := ⟨⟨0, hS⟩, trivial⟩
  refine (and_iff_right hne).trans (h.trans ?_)
  refine iff_of_eq (congrArg₂ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end Forward

/-! ### From a witness vocabulary to a block -/

section Backward

variable (V : Lax832283.StringProblems.FinVocab L) (τ : Lax988886.FiniteStructures.Vocabulary)

/-- The block of a witness vocabulary. -/
@[reducible] def blockOf : Lax904597.SecondOrder.SOBlock where
  ι := Fin τ.length
  arity := τ.get

/-- The assignment of a witness interpretation. -/
def blockAssign {n : ℕ} (R : Lax988886.FiniteStructures.Interpretation τ n) : (blockOf τ).Assignment (Fin n) :=
  fun r a => R r a = true

open Classical in
/-- The witness interpretation of an assignment. -/
noncomputable def blockInterp {n : ℕ} (ρ : (blockOf τ).Assignment (Fin n)) : Lax988886.FiniteStructures.Interpretation τ n :=
  fun r a => decide (ρ r a)

theorem blockAssign_blockInterp {n : ℕ} (ρ : (blockOf τ).Assignment (Fin n)) :
    blockAssign τ (blockInterp τ ρ) = ρ := by
  classical
  funext r a
  exact propext decide_eq_true_iff

/-- The backward translation of a first-order formula, the variables of the source
living at the positions `f` among the bound variables of the target. -/
def esoBack : ∀ {m : ℕ} (_ : Lax988886.ExistentialSecondOrder.FirstOrder V.σ τ m) {n : ℕ} (_ : Fin m → Fin n),
    (L.sum (blockOf τ).lang).BoundedFormula Empty n
  | _, .truth, _, _ => ⊤
  | _, .equal x y, _, f => (Term.var (Sum.inr (f x))).bdEqual (Term.var (Sum.inr (f y)))
  | _, .relation r args, _, f =>
      BoundedFormula.rel (Sum.inl (V.ofSym r)) fun i => Term.var (Sum.inr (f (args i)))
  | _, .variable r args, _, f =>
      BoundedFormula.rel (Sum.inr ⟨r, rfl⟩) fun i => Term.var (Sum.inr (f (args i)))
  | _, .neg φ, _, f => ∼(esoBack φ f)
  | _, .conj φ ψ, _, f => esoBack φ f ⊓ esoBack ψ f
  | _, .exists' φ, _, f => (esoBack φ (Fin.cons (Fin.last _) (Fin.castSucc ∘ f))).ex

/-- The backward translation is correct. -/
theorem realize_esoBack (S : Lax751879.OrderedStructures.OrderedStructure V.σ) (R : Lax988886.FiniteStructures.Interpretation τ S.size) {m : ℕ}
    (φ : Lax988886.ExistentialSecondOrder.FirstOrder V.σ τ m) {n : ℕ} (f : Fin m → Fin n) (x : Empty → Fin S.size)
    (w : Fin n → Fin S.size) :
    @BoundedFormula.Realize _ (Fin S.size)
      (@sumStructure L (blockOf τ).lang _ (Lax832283.StringProblems.ofOrdered V S)
        ((blockOf τ).structure (blockAssign τ R))) _ _ (esoBack V τ φ f) x w ↔
      φ.eval S R (w ∘ f) := by
  let := Lax832283.StringProblems.ofOrdered V S
  let := (blockOf τ).structure (blockAssign τ R)
  induction φ generalizing n with
  | truth => simp [esoBack, Lax988886.ExistentialSecondOrder.FirstOrder.eval]
  | equal x' y' =>
    simp [esoBack, Lax988886.ExistentialSecondOrder.FirstOrder.eval, BoundedFormula.realize_bdEqual]
  | relation r args =>
    exact relMap_ofOrdered_ofSym V S r _
  | «variable» r args =>
    exact Iff.rfl
  | neg φ ih =>
    rw [esoBack, BoundedFormula.realize_not]
    exact not_congr (ih f w)
  | conj φ ψ ih₁ ih₂ =>
    rw [esoBack, BoundedFormula.realize_inf]
    exact and_congr (ih₁ f w) (ih₂ f w)
  | exists' φ ih =>
    rw [esoBack, BoundedFormula.realize_ex]
    refine exists_congr fun a => (ih _ _).trans ?_
    have : (Fin.snoc w a : Fin (n + 1) → Fin S.size) ∘
        (Fin.cons (Fin.last _) (Fin.castSucc ∘ f)) = Fin.cons a (w ∘ f) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [this]

end Backward

/-! ### The equivalence -/

/-- **`Σ₁`-definability, in both formalisms.** A decision problem is defined by an
`∃SO` sentence of the library exactly when it reads as a property defined by an
`∃SO` sentence of the archive. -/
theorem sigmaSODefinable_one_iff (V : Lax832283.StringProblems.FinVocab L) (P : Lax904597.Problems.DecisionProblem L) :
    Lax904597.SecondOrder.SigmaSODefinable 1 P ↔ Lax988886.ExistentialSecondOrder.Definable (Lax832283.StringProblems.toProperty V P) := by
  constructor
  · rintro ⟨Bs, hlen, φ, hφ⟩
    obtain ⟨B, rfl⟩ := List.length_eq_one_iff.mp hlen
    let e : B.ι ≃ Fin (Nat.card B.ι) := Finite.equivFin _
    refine ⟨⟨witVoc B e, esoMatrix V B e φ⟩, fun S => ?_⟩
    constructor
    · rintro ⟨hS, hP⟩
      let := Lax832283.StringProblems.ofOrdered V S
      have : Nonempty (Fin S.size) := Fin.pos_iff_nonempty.mp hS
      obtain ⟨ρ, hρ⟩ := (hφ (Fin S.size)).mp hP
      refine ⟨interpOf B e ρ, (eval_esoMatrix V B e S hS φ ρ _ ?_).mpr hρ⟩
      intro i k h hi x
      exact interpOf_wit B e ρ i h hi x
    · rintro ⟨R, hR⟩
      have hS : 0 < S.size := by
        obtain ⟨⟨a, -⟩, -⟩ := hR
        exact Fin.pos a
      refine ⟨hS, ?_⟩
      let := Lax832283.StringProblems.ofOrdered V S
      have : Nonempty (Fin S.size) := Fin.pos_iff_nonempty.mp hS
      refine (hφ (Fin S.size)).mpr ⟨assignOf B e R, ?_⟩
      refine (eval_esoMatrix V B e S hS φ _ R ?_).mp hR
      intro i k h hi x
      subst hi
      exact Iff.rfl
  · rintro ⟨⟨τ, ψ⟩, hψ⟩
    refine ⟨[blockOf τ], rfl, esoBack V τ ψ Fin.elim0, ?_⟩
    intro A _ _ _
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
    let S := toOrdered V A e
    refine (toProperty_toOrdered V P A e).symm.trans ((hψ S).trans ?_)
    have hsat : Lax988886.ExistentialSecondOrder.Satisfies S ⟨τ, ψ⟩ ↔
        @Lax904597.SecondOrder.SORealize L (Fin S.size) (Lax832283.StringProblems.ofOrdered V S) [blockOf τ] (esoBack V τ ψ Fin.elim0) true := by
      constructor
      · rintro ⟨R, hR⟩
        refine ⟨blockAssign τ R, ?_⟩
        refine (realize_esoBack V τ S R ψ Fin.elim0 default default).mpr ?_
        rwa [Subsingleton.elim (default ∘ Fin.elim0) Fin.elim0]
      · rintro ⟨ρ, hρ⟩
        refine ⟨blockInterp τ ρ, ?_⟩
        rw [← blockAssign_blockInterp τ ρ] at hρ
        have := (realize_esoBack V τ S (blockInterp τ ρ) ψ Fin.elim0 default default).mp hρ
        rwa [Subsingleton.elim (default ∘ Fin.elim0) Fin.elim0] at this
    refine hsat.trans ?_
    exact (@sorealize_iso L A (Fin S.size) _ (Lax832283.StringProblems.ofOrdered V S) (ofOrderedEquiv V A e) _ _ _).symm

end Lax832283Proofs.DescriptiveComplexity.Strings


