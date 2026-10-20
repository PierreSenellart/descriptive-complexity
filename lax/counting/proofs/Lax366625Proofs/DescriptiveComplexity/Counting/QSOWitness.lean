/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.QSO
import Lax366625Proofs.DescriptiveComplexity.Counting.SharpP
import Mathlib.SetTheory.Cardinal.Finite
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

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

/-!
# Witness counts with free variables, and their closure properties

A function of a structure and a valuation is a **witness count**
(`DescriptiveComplexity.WCount`) when it counts the assignments of a block of
relation variables satisfying a first-order formula with those free
variables. Witness counts are closed under every construction of ΣQSO(FO):

* a formula, counting `1` or `0` (`DescriptiveComplexity.WCount.ind`), and a
  constant (`DescriptiveComplexity.WCount.const`);
* the product of two (`DescriptiveComplexity.WCount.mul`): the two blocks side
  by side, the two formulas conjoined;
* the sum of two (`DescriptiveComplexity.WCount.add`): the two blocks and a
  selector of arity zero, as in `DescriptiveComplexity.pairKernel`;
* the second-order sum (`DescriptiveComplexity.WCount.sosum`): the summed
  block joins the block of the count.

The first-order sum and product are in
`DescriptiveComplexity.Counting.QSOQuantifiers`.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M : Language.{0, 0}} {α : Type}

/-- The witnesses of a formula with free variables, under a valuation. -/
abbrev FWit (M : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) {α : Type} (φ : (M.sum B.lang).Formula α)
    (A : Type) [M.Structure A] (v : α → A) : Type :=
  {ρ : B.Assignment A // @Formula.Realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ φ v}

/-- **A witness count**: on finite structures, the number of witnesses of a
formula with free variables, for some block. -/
def WCount (M : Language.{0, 0}) (α : Type) (f : ∀ (A : Type) [M.Structure A], (α → A) → ℕ) :
    Prop :=
  ∃ (B : Lax904597.SecondOrder.SOBlock) (φ : (M.sum B.lang).Formula α),
    ∀ (A : Type) [M.Structure A] [Finite A] (v : α → A), f A v = Nat.card (FWit M B φ A v)

namespace WCount

/-- Witness counts only depend on their values on finite structures. -/
theorem congr {f g : ∀ (A : Type) [M.Structure A], (α → A) → ℕ} (hf : WCount M α f)
    (h : ∀ (A : Type) [M.Structure A] [Finite A] (v : α → A), f A v = g A v) : WCount M α g := by
  obtain ⟨B, φ, hφ⟩ := hf
  exact ⟨B, φ, fun A _ _ v => (h A v).symm.trans (hφ A v)⟩

open Classical in
/-- **A formula** counts `1` or `0`: the trivial block. -/
theorem ind (φ : M.Formula α) :
    WCount M α fun _ _ v => if φ.Realize v then 1 else 0 := by
  refine ⟨SOBlock.trivial, LHom.sumInl.onFormula φ, fun A _ _ v => ?_⟩
  have hr : ∀ ρ : SOBlock.trivial.Assignment A,
      (@Formula.Realize _ A (@sumStructure M _ A _ (SOBlock.trivial.structure ρ)) _
        (LHom.sumInl.onFormula φ) v) ↔ φ.Realize v := fun ρ => by
    let := SOBlock.trivial.structure ρ
    exact LHom.realize_onFormula _ φ
  have hu : Unique (SOBlock.trivial.Assignment A) :=
    ⟨⟨fun i => (i : Empty).elim⟩, fun ρ => funext fun i => (i : Empty).elim⟩
  change (if φ.Realize v then 1 else 0) = _
  by_cases h : φ.Realize v
  · rw [if_pos h]
    have hc : Nat.card (FWit M SOBlock.trivial (LHom.sumInl.onFormula φ) A v) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨default, (hr default).mpr h⟩⟩⟩
    exact hc.symm
  · rw [if_neg h]
    exact (Nat.card_eq_zero.mpr (Or.inl ⟨fun ρ => h ((hr ρ.1).mp ρ.2)⟩)).symm

/-! ### Products -/

/-- A formula over the expansion by `B`, read over the expansion by
`SOBlock.cons B C`. -/
noncomputable def liftFstF (B C : Lax904597.SecondOrder.SOBlock) (φ : (M.sum B.lang).Formula α) :
    (M.sum (SOBlock.cons B C).lang).Formula α :=
  (mergeStep M B C).onFormula (LHom.sumInl.onFormula φ)

/-- A formula over the expansion by `C`, read over the expansion by
`SOBlock.cons B C`. -/
noncomputable def liftSndF (B C : Lax904597.SecondOrder.SOBlock) (φ : (M.sum C.lang).Formula α) :
    (M.sum (SOBlock.cons B C).lang).Formula α :=
  (mergeStep M B C).onFormula ((LHom.sumMap LHom.sumInl (LHom.id C.lang)).onFormula φ)

section Lift

variable {A : Type} [M.Structure A] (B C : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A) (μ : C.Assignment A)
  (v : α → A)

theorem realize_liftFstF (φ : (M.sum B.lang).Formula α) :
    (@Formula.Realize _ A (@sumStructure M _ A _ ((SOBlock.cons B C).structure (consAssign ρ μ)))
      _ (liftFstF B C φ) v) ↔
      @Formula.Realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ φ v := by
  let := B.structure ρ
  let := C.structure μ
  let := (SOBlock.cons B C).structure (consAssign ρ μ)
  have := mergeStep_isExpansionOn M (A := A) inferInstance B C ρ μ
  rw [liftFstF, LHom.realize_onFormula, LHom.realize_onFormula]

theorem realize_liftSndF (φ : (M.sum C.lang).Formula α) :
    (@Formula.Realize _ A (@sumStructure M _ A _ ((SOBlock.cons B C).structure (consAssign ρ μ)))
      _ (liftSndF B C φ) v) ↔
      @Formula.Realize _ A (@sumStructure M _ A _ (C.structure μ)) _ φ v := by
  let := B.structure ρ
  let := C.structure μ
  let := (SOBlock.cons B C).structure (consAssign ρ μ)
  have := mergeStep_isExpansionOn M (A := A) inferInstance B C ρ μ
  have : (LHom.sumMap (LHom.sumInl : M →ᴸ M.sum B.lang) (LHom.id C.lang)).IsExpansionOn A :=
    ⟨fun f _ => by rcases f with f | f <;> rfl, fun r _ => by rcases r with r | r <;> rfl⟩
  rw [liftSndF, LHom.realize_onFormula, LHom.realize_onFormula]

theorem realize_mergeStep (φ : ((M.sum B.lang).sum C.lang).Formula α) :
    (@Formula.Realize _ A (@sumStructure M _ A _ ((SOBlock.cons B C).structure (consAssign ρ μ)))
      _ ((mergeStep M B C).onFormula φ) v) ↔
      @Formula.Realize _ A (@sumStructure (M.sum B.lang) _ A
        (@sumStructure M _ A _ (B.structure ρ)) (C.structure μ)) _ φ v := by
  let := B.structure ρ
  let := C.structure μ
  let := (SOBlock.cons B C).structure (consAssign ρ μ)
  have := mergeStep_isExpansionOn M (A := A) inferInstance B C ρ μ
  rw [LHom.realize_onFormula]

end Lift

/-- **The product of two witness counts** is a witness count: the two blocks
side by side, the two formulas conjoined. -/
theorem mul {f g : ∀ (A : Type) [M.Structure A], (α → A) → ℕ} (hf : WCount M α f)
    (hg : WCount M α g) : WCount M α fun A _ v => f A v * g A v := by
  obtain ⟨B, φ, hφ⟩ := hf
  obtain ⟨C, ψ, hψ⟩ := hg
  refine ⟨SOBlock.cons B C, liftFstF B C φ ⊓ liftSndF B C ψ, fun A _ _ v => ?_⟩
  change f A v * g A v = _
  rw [hφ A v, hψ A v, ← Nat.card_prod]
  refine (Nat.card_congr ((Equiv.subtypeEquiv (SOBlock.consAssignEquiv B C A) fun ρ => ?_).trans
    (Equiv.subtypeProdEquivProd))).symm
  have h1 := realize_liftFstF B C (fun i => ρ (Sum.inl i)) (fun j => ρ (Sum.inr j)) v φ
  have h2 := realize_liftSndF B C (fun i => ρ (Sum.inl i)) (fun j => ρ (Sum.inr j)) v ψ
  rw [consAssign_split] at h1 h2
  let := (SOBlock.cons B C).structure ρ
  exact Formula.realize_inf.trans (and_congr h1 h2)

/-! ### Second-order sums -/

/-- **The second-order sum of a witness count** is a witness count: the
summed block joins the block of the count. -/
theorem sosum (C : Lax904597.SecondOrder.SOBlock) {g : ∀ (A : Type) [(M.sum C.lang).Structure A], (α → A) → ℕ}
    (hg : WCount (M.sum C.lang) α g) :
    WCount M α fun A inst v =>
      ∑ᶠ X : C.Assignment A, @g A (@sumStructure M _ A inst (C.structure X)) v := by
  obtain ⟨B, φ, hφ⟩ := hg
  refine ⟨SOBlock.cons C B, (mergeStep M C B).onFormula φ, fun A _ _ v => ?_⟩
  have := Fintype.ofFinite (C.Assignment A)
  change ∑ᶠ X : C.Assignment A, @g A (@sumStructure M _ A _ (C.structure X)) v = _
  rw [finsum_eq_sum_of_fintype]
  have hX : ∀ X : C.Assignment A, @g A (@sumStructure M _ A _ (C.structure X)) v =
      Nat.card {ρ : B.Assignment A // @Formula.Realize _ A
        (@sumStructure (M.sum C.lang) _ A (@sumStructure M _ A _ (C.structure X))
          (B.structure ρ)) _ φ v} := fun X =>
    @hφ A (@sumStructure M _ A _ (C.structure X)) _ v
  rw [Finset.sum_congr rfl fun X _ => hX X, ← Nat.card_sigma]
  refine (Nat.card_congr ((Equiv.subtypeEquiv (SOBlock.consAssignEquiv C B A) fun ρ => ?_).trans
    (Equiv.subtypeProdEquivSigmaSubtype fun X ρ => @Formula.Realize _ A
      (@sumStructure (M.sum C.lang) _ A (@sumStructure M _ A _ (C.structure X))
        (B.structure ρ)) _ φ v))).symm
  have h := realize_mergeStep C B (fun i => ρ (Sum.inl i)) (fun j => ρ (Sum.inr j)) v φ
  rw [consAssign_split] at h
  exact h

/-! ### Sums -/

/-- “The relation variables of the block are empty”, as a formula. -/
noncomputable def emptyF (B : Lax904597.SecondOrder.SOBlock) : (M.sum B.lang).Formula α :=
  (emptyBlockS B : (M.sum B.lang).Sentence).relabel Empty.elim

theorem realize_emptyF {A : Type} [M.Structure A] (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A)
    (v : α → A) :
    (@Formula.Realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ (emptyF B) v) ↔
      ∀ (i : B.ι) (x : Fin (B.arity i) → A), ¬ρ i x := by
  let := B.structure ρ
  rw [emptyF, Formula.realize_relabel, ← realize_emptyBlockS (L := M) B ρ]
  exact iff_of_eq (congrArg (Formula.Realize _) (Subsingleton.elim _ _))

/-- The block of a sum: the two blocks and a selector. -/
abbrev sumBlock (B C : Lax904597.SecondOrder.SOBlock) : Lax904597.SecondOrder.SOBlock :=
  SOBlock.cons B (SOBlock.cons C boolBlock)

/-- “The selector holds.” -/
noncomputable def selF (B C : Lax904597.SecondOrder.SOBlock) : (M.sum (sumBlock B C).lang).Formula α :=
  Relations.formula
    (Sum.inr ⟨Sum.inr (Sum.inr ()), rfl⟩ : (M.sum (sumBlock B C).lang).Relations 0)
    finZeroElim

/-- **The kernel of a sum**: the first formula of the first block when the
selector holds, the second block being empty; the second formula of the
second block otherwise, the first block being empty. -/
noncomputable def sumF (B C : Lax904597.SecondOrder.SOBlock) (φ : (M.sum B.lang).Formula α)
    (ψ : (M.sum C.lang).Formula α) : (M.sum (sumBlock B C).lang).Formula α :=
  (selF B C ⊓ (liftFstF B _ φ ⊓ liftSndF B _ (liftFstF C boolBlock (emptyF C)))) ⊔
    (∼(selF B C) ⊓ (liftSndF B _ (liftFstF C boolBlock ψ) ⊓ liftFstF B _ (emptyF B)))

section Sum

variable {A : Type} [M.Structure A] (B C : Lax904597.SecondOrder.SOBlock) (φ : (M.sum B.lang).Formula α)
  (ψ : (M.sum C.lang).Formula α) (v : α → A)

theorem realize_sumF (ρ : B.Assignment A) (μ : C.Assignment A) (ζ : boolBlock.Assignment A) :
    (@Formula.Realize _ A (@sumStructure M _ A _
      ((sumBlock B C).structure (consAssign ρ (consAssign μ ζ)))) _ (sumF B C φ ψ) v) ↔
      (boolSel ζ ∧ @Formula.Realize _ A (@sumStructure M _ A _ (B.structure ρ)) _ φ v ∧
          ∀ (i : C.ι) (x : Fin (C.arity i) → A), ¬μ i x) ∨
        (¬boolSel ζ ∧ @Formula.Realize _ A (@sumStructure M _ A _ (C.structure μ)) _ ψ v ∧
          ∀ (i : B.ι) (x : Fin (B.arity i) → A), ¬ρ i x) := by
  have h1 := realize_liftFstF B (SOBlock.cons C boolBlock) ρ (consAssign μ ζ) v φ
  have h2 := realize_liftSndF B (SOBlock.cons C boolBlock) ρ (consAssign μ ζ) v
    (liftFstF C boolBlock (emptyF (M := M) (α := α) C))
  have h3 := realize_liftSndF B (SOBlock.cons C boolBlock) ρ (consAssign μ ζ) v
    (liftFstF C boolBlock ψ)
  have h4 := realize_liftFstF B (SOBlock.cons C boolBlock) ρ (consAssign μ ζ) v
    (emptyF (M := M) (α := α) B)
  have h5 := realize_liftFstF C boolBlock μ ζ v (emptyF (M := M) (α := α) C)
  have h6 := realize_liftFstF C boolBlock μ ζ v ψ
  have hs : (@Formula.Realize _ A (@sumStructure M _ A _
      ((sumBlock B C).structure (consAssign ρ (consAssign μ ζ)))) _ (selF B C) v) ↔
      boolSel ζ := (boolSel_iff ζ _).symm
  let := (sumBlock B C).structure (consAssign ρ (consAssign μ ζ))
  rw [sumF, Formula.realize_sup, Formula.realize_inf, Formula.realize_inf, Formula.realize_inf,
    Formula.realize_inf, Formula.realize_not, hs, h1, h2, h3, h4, h5, h6, realize_emptyF,
    realize_emptyF]

/-- The empty assignment. -/
def emptyAssign (C : Lax904597.SecondOrder.SOBlock) (A : Type) : C.Assignment A := fun _ _ => False

/-- The selector, true or false. -/
def selAssign (b : Prop) (A : Type) : boolBlock.Assignment A := fun _ _ => b

theorem eq_emptyAssign {C : Lax904597.SecondOrder.SOBlock} {μ : C.Assignment A} (h : ∀ i x, ¬μ i x) :
    μ = emptyAssign C A :=
  funext fun i => funext fun x => propext ⟨fun hx => h i x hx, False.elim⟩

theorem eq_selAssign (ζ : boolBlock.Assignment A) : ζ = selAssign (boolSel ζ) A :=
  funext fun i => funext fun x => by
    cases i
    exact propext (boolSel_iff ζ x).symm

/-- The witnesses of a sum, on the three parts of the block. -/
def sumPred (t : B.Assignment A × C.Assignment A × boolBlock.Assignment A) : Prop :=
  (boolSel t.2.2 ∧ @Formula.Realize _ A (@sumStructure M _ A _ (B.structure t.1)) _ φ v ∧
      ∀ i x, ¬t.2.1 i x) ∨
    (¬boolSel t.2.2 ∧ @Formula.Realize _ A (@sumStructure M _ A _ (C.structure t.2.1)) _ ψ v ∧
      ∀ i x, ¬t.1 i x)

/-- **The witnesses of a sum** are those of one formula or the other. -/
noncomputable def sumEquiv :
    {ρ : (sumBlock B C).Assignment A // @Formula.Realize _ A
        (@sumStructure M _ A _ ((sumBlock B C).structure ρ)) _ (sumF B C φ ψ) v} ≃
      FWit M B φ A v ⊕ FWit M C ψ A v := by
  classical
  refine (Equiv.subtypeEquiv (q := sumPred B C φ ψ v) ((SOBlock.consAssignEquiv B _ A).trans
    (Equiv.prodCongr (Equiv.refl _) (SOBlock.consAssignEquiv C boolBlock A))) fun ρ' => ?_).trans ?_
  · have h := realize_sumF B C φ ψ v (fun i => ρ' (Sum.inl i)) (fun j => ρ' (Sum.inr (Sum.inl j)))
      (fun k => ρ' (Sum.inr (Sum.inr k)))
    rw [consAssign_split (ρ := fun j => ρ' (Sum.inr j)), consAssign_split] at h
    exact h
  · exact
      { toFun := fun t => if hs : boolSel t.1.2.2 then
            Sum.inl ⟨t.1.1, (t.2.resolve_right fun h => h.1 hs).2.1⟩
          else Sum.inr ⟨t.1.2.1, (t.2.resolve_left fun h => hs h.1).2.1⟩
        invFun := Sum.elim (fun w => ⟨(w.1, emptyAssign C A, selAssign True A),
            Or.inl ⟨(boolSel_iff _ finZeroElim).mpr trivial, w.2, fun _ _ h => h⟩⟩)
          fun w => ⟨(emptyAssign B A, w.1, selAssign False A),
            Or.inr ⟨fun h => (boolSel_iff _ finZeroElim).mp h, w.2, fun _ _ h => h⟩⟩
        left_inv := fun t => by
          obtain ⟨⟨ρ, μ, ζ⟩, ht⟩ := t
          by_cases hs : boolSel ζ
          · have hμ := (ht.resolve_right fun h => h.1 hs).2.2
            simp only [hs, ↓reduceDIte, Sum.elim_inl]
            refine Subtype.ext (Prod.ext rfl (Prod.ext (eq_emptyAssign hμ).symm ?_))
            change selAssign True A = ζ
            rw [eq_selAssign ζ, eq_true hs]
          · have hρ := (ht.resolve_left fun h => hs h.1).2.2
            simp only [hs, ↓reduceDIte, Sum.elim_inr]
            refine Subtype.ext (Prod.ext (eq_emptyAssign hρ).symm (Prod.ext rfl ?_))
            change selAssign False A = ζ
            rw [eq_selAssign ζ, eq_false hs]
        right_inv := by
          have hT : boolSel (selAssign True A) := (boolSel_iff _ finZeroElim).mpr trivial
          have hF : ¬boolSel (selAssign False A) := fun h => (boolSel_iff _ finZeroElim).mp h
          rintro (w | w)
          · simp only [Sum.elim_inl, hT, ↓reduceDIte]
          · simp only [Sum.elim_inr, hF, ↓reduceDIte] }

end Sum

/-- **The sum of two witness counts** is a witness count. -/
theorem add {f g : ∀ (A : Type) [M.Structure A], (α → A) → ℕ} (hf : WCount M α f)
    (hg : WCount M α g) : WCount M α fun A _ v => f A v + g A v := by
  obtain ⟨B, φ, hφ⟩ := hf
  obtain ⟨C, ψ, hψ⟩ := hg
  refine ⟨sumBlock B C, sumF B C φ ψ, fun A _ _ v => ?_⟩
  change f A v + g A v = _
  rw [hφ A v, hψ A v, ← Nat.card_sum]
  exact (Nat.card_congr (sumEquiv B C φ ψ v)).symm

/-- **A constant** is a witness count. -/
theorem const (s : ℕ) : WCount M α fun _ _ _ => s := by
  induction s with
  | zero => exact (ind (⊥ : M.Formula α)).congr fun A _ _ v => by simp
  | succ s ih => exact (ih.add (ind (⊤ : M.Formula α))).congr fun A _ _ v => by simp

end WCount

end Lax366625Proofs.DescriptiveComplexity


