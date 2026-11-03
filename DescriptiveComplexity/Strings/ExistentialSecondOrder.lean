/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Strings.FirstOrder
import DescriptiveComplexity.Strings.Transport

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

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure
open Lax.OrderedStructures Lax.FiniteStructures Lax.ExistentialSecondOrder

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### From a block to a witness vocabulary -/

section Forward

variable (V : FinVocab L) (B : SOBlock) {m₀ : ℕ} (e : B.ι ≃ Fin m₀)

/-- The witness vocabulary of a block, along a numbering of its variables. -/
def witVoc : Lax.FiniteStructures.Vocabulary :=
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

theorem wit_witVar (r : Fin (witVoc B e).length) : wit B e (witVar B e r) = r := by
  apply Fin.ext
  simp [witVar, wit]
  rfl

/-- The atoms of the forward translation. -/
def esoAtom {m n : ℕ} : (L.sum B.lang).Relations n → (Fin n → Fin m) →
    FirstOrder V.σ (witVoc B e) m
  | .inl R, a => .relation (V.toSym R) (a ∘ Fin.cast (V.arity_toSym R))
  | .inr R, a => .variable (wit B e R.1)
      (a ∘ Fin.cast ((witVoc_get_wit B e R.1).trans R.2))

/-- The forward translation of a matrix. -/
def esoMatrix (φ : (L.sum B.lang).Sentence) : FirstOrder V.σ (witVoc B e) 0 :=
  .conj (.exists' .truth)
    ((esoAlg V.σ (witVoc B e) (esoAtom V B e)).tr φ (Sum.elim Empty.elim Fin.elim0))

open Classical in
/-- An interpretation of the witness vocabulary from an assignment of the block. -/
noncomputable def interpOf {n : ℕ} (ρ : B.Assignment (Fin n)) : Interpretation (witVoc B e) n :=
  fun r a => decide (ρ (witVar B e r) (a ∘ Fin.cast (witVoc_get B e r)))

/-- An assignment of the block from an interpretation of the witness vocabulary. -/
def assignOf {n : ℕ} (R : Interpretation (witVoc B e) n) : B.Assignment (Fin n) :=
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

variable (S : OrderedStructure V.σ) {n : ℕ}

private theorem esoSem (ρ : B.Assignment (Fin S.size)) (R : Interpretation (witVoc B e) S.size)
    (hR : ∀ i {k} (h : (witVoc B e).get (wit B e i) = k) (hi : B.arity i = k)
      (x : Fin k → Fin S.size),
      R (wit B e i) (x ∘ Fin.cast h) = true ↔ ρ i (x ∘ Fin.cast hi)) :
    letI := ofOrdered V S
    letI := B.structure ρ
    (esoAlg V.σ (witVoc B e) (esoAtom V B e)).Sem (Fin S.size)
      (fun φ w => FirstOrder.eval φ S R w) := by
  let := ofOrdered V S
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
      change FirstOrder.eval φ S R (Fin.cons (w' 0) (w' ∘ Fin.succ))
      rw [this]
      exact ha
  · intro m a w
    exact ⟨Fin.cons a w, rfl, rfl⟩

/-- The forward translation of a matrix is correct, at a nonempty size. -/
theorem eval_esoMatrix (hS : 0 < S.size) (φ : (L.sum B.lang).Sentence)
    (ρ : B.Assignment (Fin S.size)) (R : Interpretation (witVoc B e) S.size)
    (hR : ∀ i {k} (h : (witVoc B e).get (wit B e i) = k) (hi : B.arity i = k)
      (x : Fin k → Fin S.size),
      R (wit B e i) (x ∘ Fin.cast h) = true ↔ ρ i (x ∘ Fin.cast hi)) :
    (esoMatrix V B e φ).eval S R Fin.elim0 ↔
      @Sentence.Realize _ (Fin S.size)
        (@sumStructure L B.lang _ (ofOrdered V S) (B.structure ρ)) φ := by
  let := ofOrdered V S
  let := B.structure ρ
  have h := (esoSem V B e S ρ R hR).eval_tr φ (Sum.elim Empty.elim Fin.elim0) Fin.elim0
  have hne : (FirstOrder.exists' FirstOrder.truth : FirstOrder V.σ (witVoc B e) 0).eval S R
      Fin.elim0 := ⟨⟨0, hS⟩, trivial⟩
  refine (and_iff_right hne).trans (h.trans ?_)
  refine iff_of_eq (congrArg₂ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end Forward

/-! ### From a witness vocabulary to a block -/

section Backward

variable (V : FinVocab L) (τ : Lax.FiniteStructures.Vocabulary)

/-- The block of a witness vocabulary. -/
@[reducible] def blockOf : SOBlock where
  ι := Fin τ.length
  arity := τ.get

/-- The assignment of a witness interpretation. -/
def blockAssign {n : ℕ} (R : Interpretation τ n) : (blockOf τ).Assignment (Fin n) :=
  fun r a => R r a = true

open Classical in
/-- The witness interpretation of an assignment. -/
noncomputable def blockInterp {n : ℕ} (ρ : (blockOf τ).Assignment (Fin n)) : Interpretation τ n :=
  fun r a => decide (ρ r a)

theorem blockAssign_blockInterp {n : ℕ} (ρ : (blockOf τ).Assignment (Fin n)) :
    blockAssign τ (blockInterp τ ρ) = ρ := by
  classical
  funext r a
  exact propext decide_eq_true_iff

/-- The backward translation of a first-order formula, the variables of the source
living at the positions `f` among the bound variables of the target. -/
def esoBack : ∀ {m : ℕ} (_ : FirstOrder V.σ τ m) {n : ℕ} (_ : Fin m → Fin n),
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
theorem realize_esoBack (S : OrderedStructure V.σ) (R : Interpretation τ S.size) {m : ℕ}
    (φ : FirstOrder V.σ τ m) {n : ℕ} (f : Fin m → Fin n) (x : Empty → Fin S.size)
    (w : Fin n → Fin S.size) :
    @BoundedFormula.Realize _ (Fin S.size)
      (@sumStructure L (blockOf τ).lang _ (ofOrdered V S)
        ((blockOf τ).structure (blockAssign τ R))) _ _ (esoBack V τ φ f) x w ↔
      φ.eval S R (w ∘ f) := by
  let := ofOrdered V S
  let := (blockOf τ).structure (blockAssign τ R)
  induction φ generalizing n with
  | truth => simp [esoBack, FirstOrder.eval]
  | equal x' y' =>
    simp [esoBack, FirstOrder.eval, BoundedFormula.realize_bdEqual]
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
theorem sigmaSODefinable_one_iff (V : FinVocab L) (P : DecisionProblem L) :
    SigmaSODefinable 1 P ↔ Definable (toProperty V P) := by
  constructor
  · rintro ⟨Bs, hlen, φ, hφ⟩
    obtain ⟨B, rfl⟩ := List.length_eq_one_iff.mp hlen
    let e : B.ι ≃ Fin (Nat.card B.ι) := Finite.equivFin _
    refine ⟨⟨witVoc B e, esoMatrix V B e φ⟩, fun S => ?_⟩
    constructor
    · rintro ⟨hS, hP⟩
      let := ofOrdered V S
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
      let := ofOrdered V S
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
    have hsat : Satisfies S ⟨τ, ψ⟩ ↔
        @SORealize L (Fin S.size) (ofOrdered V S) [blockOf τ] (esoBack V τ ψ Fin.elim0) true := by
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
    exact (@sorealize_iso L A (Fin S.size) _ (ofOrdered V S) (ofOrderedEquiv V A e) _ _ _).symm

end DescriptiveComplexity.Strings
