/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.QSOWitness
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

namespace Lax366625Proofs.DescriptiveComplexity.SOBlock
end Lax366625Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

/-!
# First-order sums and products of witness counts

The two first-order quantifiers of ΣQSO(FO) keep witness counts witness
counts.

* **The sum** over the `n`-tuples (`DescriptiveComplexity.WCount.sum`): the
  tuple is guessed too, as `n` unary relation variables holding one element
  each.
* **The product** over the `n`-tuples (`DescriptiveComplexity.WCount.prod`):
  one witness per tuple, i.e., every relation variable of the block takes the
  tuple as `n` more arguments (`DescriptiveComplexity.SOBlock.extend`); the
  formula reads them by substituting `X'(w̄, ȳ)` for every atom `X(ȳ)`
  (`DescriptiveComplexity.extendRel`), and holds for every tuple.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M : Language.{0, 0}} {α : Type}

/-! ### The sum over tuples -/

/-- `n` unary relation variables. -/
@[reducible]
def tupleBlock (n : ℕ) : Lax904597.SecondOrder.SOBlock where
  ι := Fin n
  arity := fun _ => 1

namespace WCount

section Sum

variable (B : Lax904597.SecondOrder.SOBlock) (n : ℕ)

/-- The `i`-th unary relation variable, beside the block `B`. -/
abbrev wSym (i : Fin n) : (M.sum (SOBlock.cons B (tupleBlock n)).lang).Relations 1 :=
  Sum.inr ⟨Sum.inr i, rfl⟩

/-- “The `i`-th unary relation variable holds of exactly one element.” -/
noncomputable def exactlyOneF (i : Fin n) :
    (M.sum (SOBlock.cons B (tupleBlock n)).lang).Formula α :=
  FirstOrder.Language.Formula.iExs (Fin 1)
      (FirstOrder.Language.Relations.formula₁ (wSym B n i) (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 1)
          ((FirstOrder.Language.Relations.formula₁ (wSym B n i) (FirstOrder.Language.Term.var (Sum.inr 0))).imp
            (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))))))

/-- **The kernel of a sum over tuples**: each unary relation variable holds of
exactly one element, and the tuple of these elements satisfies the formula. -/
noncomputable def sumKernel (φ : (M.sum B.lang).Formula (α ⊕ Fin n)) :
    (M.sum (SOBlock.cons B (tupleBlock n)).lang).Formula α :=
  (Formula.iInf fun i => exactlyOneF B n i) ⊓
    Formula.iExs (Fin n) ((Formula.iInf fun i =>
      Relations.formula₁ (wSym B n i) (Term.var (Sum.inr i))) ⊓ liftFstF B (tupleBlock n) φ)

variable {A : Type} [M.Structure A] {B n}

theorem realize_sumKernel (φ : (M.sum B.lang).Formula (α ⊕ Fin n)) (ρ : B.Assignment A)
    (μ : (tupleBlock n).Assignment A) (v : α → A) :
    (@Formula.Realize _ A (@sumStructure M _ A _
      ((SOBlock.cons B (tupleBlock n)).structure (consAssign ρ μ))) _ (sumKernel B n φ) v) ↔
      (∀ i, ∃ y, μ i ![y] ∧ ∀ z, μ i ![z] → z = y) ∧
        ∃ w : Fin n → A, (∀ i, μ i ![w i]) ∧
          @Formula.Realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ φ (Sum.elim v w) := by
  have hl := fun w : Fin n → A => realize_liftFstF B (tupleBlock n) ρ μ (Sum.elim v w) φ
  let := (SOBlock.cons B (tupleBlock n)).structure (consAssign ρ μ)
  have hw : ∀ (i : Fin n) (x : Fin 1 → A),
      RelMap (wSym (M := M) B n i) x ↔ μ i ![x 0] := fun i x => by
    change μ i (fun j => x (Fin.cast rfl j)) ↔ _
    exact iff_of_eq (congrArg (μ i) (funext fun j => by fin_cases j; rfl))
  rw [sumKernel, Formula.realize_inf, Formula.realize_iInf, Formula.realize_iExs]
  simp only [exactlyOneF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_rel₁, Formula.realize_equal, Formula.realize_iInf,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, hw, hl]
  refine and_congr (forall_congr' fun i => ⟨fun ⟨y, hy, hz⟩ => ⟨y 0, hy, fun z hz' => ?_⟩,
    fun ⟨y, hy, hz⟩ => ⟨fun _ => y, hy, fun z hz' => hz _ hz'⟩⟩) Iff.rfl
  exact hz (fun _ => z) hz'

/-- The element a unary relation variable holding of exactly one element holds
of. -/
noncomputable def pickOf (μ : (tupleBlock n).Assignment A)
    (h : ∀ i, ∃ y, μ i ![y] ∧ ∀ z, μ i ![z] → z = y) (i : Fin n) : A :=
  Classical.choose (h i)

/-- The unary relation variables holding of the elements of a tuple. -/
def tupleAssign (w : Fin n → A) : (tupleBlock n).Assignment A :=
  fun i x => x 0 = w i

omit [M.Structure A] in
theorem tupleAssign_spec (w : Fin n → A) (i : Fin n) :
    ∃ y, tupleAssign w i ![y] ∧ ∀ z, tupleAssign w i ![z] → z = y :=
  ⟨w i, rfl, fun _ hz => hz⟩

/-- **The witnesses of a sum over tuples** are a tuple and a witness for
it. -/
noncomputable def sumEquiv' (φ : (M.sum B.lang).Formula (α ⊕ Fin n)) (v : α → A) :
    FWit M (SOBlock.cons B (tupleBlock n)) (sumKernel B n φ) A v ≃
      Σ w : Fin n → A, FWit M B φ A (Sum.elim v w) where
  toFun ρ' :=
    have h := (realize_sumKernel φ (fun i => ρ'.1 (Sum.inl i)) (fun j => ρ'.1 (Sum.inr j)) v).mp
      (by rw [consAssign_split]; exact ρ'.2)
    ⟨pickOf _ h.1, fun i => ρ'.1 (Sum.inl i), by
      obtain ⟨w, hw, hφ⟩ := h.2
      have : w = pickOf _ h.1 := funext fun i =>
        (Classical.choose_spec (h.1 i)).2 _ (hw i)
      rw [← this]
      exact hφ⟩
  invFun p := ⟨consAssign p.2.1 (tupleAssign p.1), (realize_sumKernel φ _ _ v).mpr
    ⟨tupleAssign_spec p.1, p.1, fun _ => rfl, p.2.2⟩⟩
  left_inv ρ' := by
    have h := (realize_sumKernel φ (fun i => ρ'.1 (Sum.inl i)) (fun j => ρ'.1 (Sum.inr j)) v).mp
      (by rw [consAssign_split]; exact ρ'.2)
    refine Subtype.ext ?_
    change consAssign (fun i => ρ'.1 (Sum.inl i)) (tupleAssign (pickOf _ h.1)) = ρ'.1
    conv_rhs => rw [← consAssign_split ρ'.1]
    congr 1
    funext i x
    refine propext ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxx : x = ![x 0] := funext fun j => by fin_cases j; rfl
      rw [hxx, hx]
      exact (Classical.choose_spec (h.1 i)).1
    · have hxx : x = ![x 0] := funext fun j => by fin_cases j; rfl
      rw [hxx] at hx
      exact (Classical.choose_spec (h.1 i)).2 _ hx
  right_inv p := by
    obtain ⟨w, ρ, hρ⟩ := p
    have hw : pickOf (tupleAssign w) (tupleAssign_spec w) = w := funext fun i =>
      (Classical.choose_spec (tupleAssign_spec w i)).1
    exact Sigma.subtype_ext hw rfl

end Sum

/-- **The sum of a witness count over the tuples** is a witness count. -/
theorem sum (n : ℕ) {f : ∀ (A : Type) [M.Structure A], (α ⊕ Fin n → A) → ℕ}
    (hf : WCount M (α ⊕ Fin n) f) :
    WCount M α fun A _ v => ∑ᶠ w : Fin n → A, f A (Sum.elim v w) := by
  obtain ⟨B, φ, hφ⟩ := hf
  refine ⟨SOBlock.cons B (tupleBlock n), sumKernel B n φ, fun A _ _ v => ?_⟩
  have := Fintype.ofFinite (Fin n → A)
  change ∑ᶠ w : Fin n → A, f A (Sum.elim v w) = _
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun w _ => hφ A (Sum.elim v w),
    ← Nat.card_sigma]
  exact (Nat.card_congr (sumEquiv' φ v)).symm

end WCount

/-! ### The product over tuples -/

/-- Every relation variable of the block takes `n` more arguments. -/
@[reducible]
def SOBlock.extend (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) : Lax904597.SecondOrder.SOBlock where
  ι := B.ι
  arity := fun i => n + B.arity i

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax366625Proofs.DescriptiveComplexity.SOBlock (extend)

end Lax904597.SecondOrder.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M : Language.{0, 0}} {α : Type}

/-- The assignments of the extended block are the families of assignments
indexed by the `n`-tuples. -/
def SOBlock.extendAssignEquiv (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (A : Type) :
    (B.extend n).Assignment A ≃ ((Fin n → A) → B.Assignment A) where
  toFun ρ w i y := ρ i (Fin.append w y)
  invFun σ i u := σ (fun j => u (Fin.castAdd _ j)) i fun j => u (Fin.natAdd n j)
  left_inv ρ := funext fun i => funext fun u => by
    change ρ i (Fin.append (fun j => u (Fin.castAdd _ j)) fun j => u (Fin.natAdd n j)) = ρ i u
    rw [Fin.append_castAdd_natAdd]
  right_inv σ := funext fun w => funext fun i => funext fun y => by
    change σ (fun j => Fin.append w y (Fin.castAdd _ j)) i (fun j => Fin.append w y
      (Fin.natAdd n j)) = σ w i y
    simp only [Fin.append_left, Fin.append_right]

end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax366625Proofs.DescriptiveComplexity.SOBlock (extendAssignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M : Language.{0, 0}} {α : Type}

section Extend

variable {B : Lax904597.SecondOrder.SOBlock} {n : ℕ}

/-- A term of a relational expansion, read in another expansion of the same
base vocabulary. -/
def castTerm {B' : Lax904597.SecondOrder.SOBlock} {γ : Type} : (M.sum B.lang).Term γ → (M.sum B'.lang).Term γ
  | .var x => .var x
  | .func (Sum.inl f) ts => .func (Sum.inl f) fun i => castTerm (ts i)
  | .func (Sum.inr f) _ => isEmptyElim f

/-- **Substituting `X'(w̄, ȳ)` for every atom `X(ȳ)`** of a relation variable
of the block, `w̄` free variables. -/
def extendRel (w : Fin n → α) :
    ∀ {k : ℕ}, (M.sum B.lang).BoundedFormula α k → (M.sum (B.extend n).lang).BoundedFormula α k
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (castTerm t₁) (castTerm t₂)
  | _, .rel (Sum.inl r) ts => .rel (Sum.inl r) fun i => castTerm (ts i)
  | _, .rel (Sum.inr r) ts =>
      .rel (Sum.inr ⟨r.1, congrArg (n + ·) r.2⟩)
        (Fin.append (fun j => Term.var (Sum.inl (w j))) fun i => castTerm (ts i))
  | _, .imp φ ψ => .imp (extendRel w φ) (extendRel w ψ)
  | _, .all φ => .all (extendRel w φ)

variable {A : Type} [M.Structure A]

theorem realize_castTerm {B' : Lax904597.SecondOrder.SOBlock} {γ : Type} (ρ : B.Assignment A) (ρ' : B'.Assignment A)
    (t : (M.sum B.lang).Term γ) (u : γ → A) :
    @Term.realize _ A (@sumStructure M _ A _ (B'.structure ρ')) _ u (castTerm t) =
      @Term.realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ u t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    rcases f with f | f
    · simp only [castTerm, Term.realize]
      exact congrArg _ (funext ih)
    · exact isEmptyElim f

/-- The assignment of the block at a tuple. -/
def atTuple (ρ : (B.extend n).Assignment A) (a : Fin n → A) : B.Assignment A :=
  fun i y => ρ i (Fin.append a y)

theorem realize_extendRel (w : Fin n → α) (ρ : (B.extend n).Assignment A) {k : ℕ}
    (φ : (M.sum B.lang).BoundedFormula α k) (u : α → A) (xs : Fin k → A) :
    @BoundedFormula.Realize _ A (@sumStructure M _ A _ ((B.extend n).structure ρ)) _ _
        (extendRel w φ) u xs ↔
      @BoundedFormula.Realize _ A (@sumStructure M _ A _ (B.structure (atTuple ρ (u ∘ w)))) _ _
        φ u xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [extendRel, BoundedFormula.Realize, realize_castTerm (atTuple ρ (u ∘ w)) ρ]
  | rel R ts =>
    rcases R with r | ⟨i, rfl⟩
    · simp only [extendRel, BoundedFormula.Realize, realize_castTerm (atTuple ρ (u ∘ w)) ρ]
      exact Iff.rfl
    · simp only [extendRel, BoundedFormula.Realize]
      refine iff_of_eq ?_
      change ρ i _ = ρ i _
      refine congrArg (ρ i) (funext fun j => ?_)
      rw [Fin.cast_eq_self]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left, Term.realize, Sum.elim_inl, Function.comp_apply]
      · simp only [Fin.append_right, Fin.cast_eq_self, realize_castTerm (atTuple ρ (u ∘ w)) ρ]
  | imp φ ψ ih₁ ih₂ =>
    simp only [extendRel, BoundedFormula.realize_imp, ih₁, ih₂]
  | all φ ih =>
    simp only [extendRel, BoundedFormula.realize_all, ih]

end Extend

namespace WCount

/-- **The product of a witness count over the tuples** is a witness count:
one witness per tuple, read off the extended block. -/
theorem prod (n : ℕ) {f : ∀ (A : Type) [M.Structure A], (α ⊕ Fin n → A) → ℕ}
    (hf : WCount M (α ⊕ Fin n) f) :
    WCount M α fun A _ v => ∏ᶠ w : Fin n → A, f A (Sum.elim v w) := by
  obtain ⟨B, φ, hφ⟩ := hf
  refine ⟨B.extend n, Formula.iAlls (Fin n) (extendRel (Sum.inr : Fin n → α ⊕ Fin n) φ),
    fun A _ _ v => ?_⟩
  have := Fintype.ofFinite (Fin n → A)
  change ∏ᶠ w : Fin n → A, f A (Sum.elim v w) = _
  rw [finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun w _ => hφ A (Sum.elim v w),
    ← Nat.card_pi]
  refine (Nat.card_congr ((Equiv.subtypeEquiv (B.extendAssignEquiv n A) fun ρ => ?_).trans
    (Equiv.subtypePiEquivPi (p := fun w b => @Formula.Realize _ A
      (@sumStructure M _ A _ (B.structure b)) _ φ (Sum.elim v w))))).symm
  let := (B.extend n).structure ρ
  rw [Formula.realize_iAlls]
  refine forall_congr' fun w => ?_
  have h := realize_extendRel (Sum.inr : Fin n → α ⊕ Fin n) ρ φ (Sum.elim v w) default
  exact h

end WCount

end Lax366625Proofs.DescriptiveComplexity


