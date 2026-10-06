/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.SetArith
import Lax366625Proofs.DescriptiveComplexity.FixedPointStratify
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

namespace Lax366625Proofs.DescriptiveComplexity.StepDef
end Lax366625Proofs.DescriptiveComplexity.StepDef

namespace Lax366625Proofs.DescriptiveComplexity.StepDef.Computes
end Lax366625Proofs.DescriptiveComplexity.StepDef.Computes

namespace Lax366625Proofs.DescriptiveComplexity.StepDef.Ext
end Lax366625Proofs.DescriptiveComplexity.StepDef.Ext

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Towers of inductions: first-order strata and sweep strata

The definability layer of the normal form of FP
(`DescriptiveComplexity.Counting.Digits`). The digits of a quantitative term
are computed by a *tower* of inflationary inductions, each reading the
converged relations of the ones below as if they were relations of the
instance; a tower is one induction, by stratification
(`DescriptiveComplexity.StepDef.stratify`). Two kinds of stratum are all the
construction uses, and both are stated over an arbitrary vocabulary `M` – in a
tower, the base vocabulary expanded by the relations already computed:

* a **first-order stratum** (`DescriptiveComplexity.Digits.foStratum`) defines
  a family of relations by formulas of `M`; its limit is what the formulas say
  (`DescriptiveComplexity.Digits.inflLimit_foStratum`);
* a **sweep stratum** (`DescriptiveComplexity.Digits.sweep`) computes rows
  indexed by the tuples of a definable linear order, each row by a formula
  that may read the rows before it. It is the iteration of
  `DescriptiveComplexity.Digits.sweep_limit`, written with a relation `done` beside
  the relation `row`, and its limit is the family of rows
  (`DescriptiveComplexity.Digits.inflLimit_sweep`).

`DescriptiveComplexity.StepDef.Ext` is the bookkeeping of a tower: an
induction extends another when it computes, among others, the same relations.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

/-! ### Tuples in blocks -/

section Tuples

variable {A : Type} {a q ℓ : ℕ}

/-- Parameters, then an index. -/
def j2 (w : Fin a → A) (i : Fin q → A) : Fin (a + q) → A :=
  Fin.append w i

/-- Parameters, then an index, then a position. -/
def j3 (w : Fin a → A) (i : Fin q → A) (p : Fin ℓ → A) : Fin (a + q + ℓ) → A :=
  Fin.append (Fin.append w i) p

theorem exists_j2 (x : Fin (a + q) → A) : ∃ w i, x = j2 (a := a) (q := q) w i :=
  ⟨fun k => x (Fin.castAdd q k), fun k => x (Fin.natAdd a k),
    (Fin.append_castAdd_natAdd (f := x)).symm⟩

/-- The variables of a formula about parameters and an index, as arguments of a
relation. -/
def g2 : Fin a ⊕ Fin q → Fin (a + q) :=
  Sum.elim (Fin.castAdd q) (Fin.natAdd a)

/-- The variables of a formula about parameters, an index and a position, as
arguments of a relation. -/
def g3 : (Fin a ⊕ Fin q) ⊕ Fin ℓ → Fin (a + q + ℓ) :=
  Sum.elim (Fin.castAdd ℓ ∘ g2) (Fin.natAdd (a + q))

theorem j2_comp_g2 (w : Fin a → A) (i : Fin q → A) : j2 w i ∘ g2 = Sum.elim w i := by
  funext x
  rcases x with k | k <;> simp [j2, g2]

theorem j3_comp_g3 (w : Fin a → A) (i : Fin q → A) (p : Fin ℓ → A) :
    j3 w i p ∘ g3 = Sum.elim (Sum.elim w i) p := by
  funext x
  rcases x with (k | k) | k <;> simp [j3, g3, g2]

theorem comp_append {γ : Type} (v : γ → A) (s : Fin a → γ) (t : Fin q → γ) :
    (fun k => v (Fin.append s t k)) = Fin.append (v ∘ s) (v ∘ t) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

end Tuples

variable {M : Language.{0, 0}}

/-! ### First-order strata -/

/-- **A first-order stratum**: a family of relations, each defined by a
formula of the vocabulary. -/
@[reducible] noncomputable def foStratum (J : Type) [Finite J] (ar : J → ℕ)
    (ψ : ∀ j, M.Formula (Fin (ar j))) : Lax535992.InflationaryFixedPoint.StepDef M where
  B := ⟨J, ar⟩
  step := fun j => LHom.sumInl.onFormula (ψ j)
  out := ⊤

/-- **The limit of a first-order stratum is what its formulas say.** -/
theorem inflLimit_foStratum {A : Type} [M.Structure A] (J : Type) [Finite J] (ar : J → ℕ)
    (ψ : ∀ j, M.Formula (Fin (ar j))) (j : J) (x : Fin (ar j) → A) :
    (foStratum J ar ψ).inflLimit A j x ↔ (ψ j).Realize x := by
  have hnext : ∀ ρ : (foStratum J ar ψ).B.Assignment A,
      (foStratum J ar ψ).next ρ j x ↔ (ψ j).Realize x := by
    intro ρ
    let := (foStratum J ar ψ).B.structure ρ
    exact LHom.realize_onFormula (φ := (LHom.sumInl : M →ᴸ M.sum (foStratum J ar ψ).B.lang))
      (ψ j)
  have hst : ∀ n, (foStratum J ar ψ).inflStage A (n + 1) j x ↔ (ψ j).Realize x := by
    intro n
    induction n with
    | zero =>
      rw [StepDef.inflStage_succ]
      exact ⟨fun h => h.elim False.elim (hnext _).mp, fun h => Or.inr ((hnext _).mpr h)⟩
    | succ n ih =>
      rw [StepDef.inflStage_succ]
      exact ⟨fun h => h.elim ih.mp (hnext _).mp, fun h => Or.inr ((hnext _).mpr h)⟩
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n => exact (hst n).mp hn
  · exact fun h => ⟨1, (hst 0).mpr h⟩

/-! ### Sweep strata -/

/-- The block of a sweep: the relation `row` (parameters, index, position) and
the relation `done` (parameters, index). -/
@[reducible] def sweepBlock (a q ℓ : ℕ) : Lax904597.SecondOrder.SOBlock where
  ι := Bool
  arity := fun b => cond b (a + q + ℓ) (a + q)

section SweepFormulas

variable (M) (a q ℓ : ℕ)

/-- The symbol of the rows. -/
abbrev rowSym : (M.sum (sweepBlock a q ℓ).lang).Relations (a + q + ℓ) :=
  Sum.inr ⟨true, rfl⟩

/-- The symbol of the marker. -/
abbrev doneSym : (M.sum (sweepBlock a q ℓ).lang).Relations (a + q) :=
  Sum.inr ⟨false, rfl⟩

variable {M a q} {γ : Type}

/-- “The row of this index is done.” -/
def doneAt (ws : Fin a → γ) (is : Fin q → γ) : (M.sum (sweepBlock a q ℓ).lang).Formula γ :=
  Relations.formula (doneSym M a q ℓ) fun k => Term.var (Fin.append ws is k)

variable {ℓ}

/-- “This position is in the row of this index.” -/
def rowAt (ws : Fin a → γ) (is : Fin q → γ) (ps : Fin ℓ → γ) :
    (M.sum (sweepBlock a q ℓ).lang).Formula γ :=
  Relations.formula (rowSym M a q ℓ) fun k => Term.var (Fin.append (Fin.append ws is) ps k)

variable {A : Type} [M.Structure A]

theorem realize_doneAt (ρ : (sweepBlock a q ℓ).Assignment A) (ws : Fin a → γ)
    (is : Fin q → γ) (v : γ → A) :
    (@Formula.Realize _ A ((sweepBlock a q ℓ).structure₁ (L := M) ρ) _ (doneAt ℓ ws is) v) ↔
      ρ false (j2 (v ∘ ws) (v ∘ is)) := by
  let := (sweepBlock a q ℓ).structure₁ (L := M) ρ
  rw [doneAt, Formula.realize_rel]
  exact iff_of_eq (congrArg (ρ false) (comp_append v ws is))

theorem realize_rowAt (ρ : (sweepBlock a q ℓ).Assignment A) (ws : Fin a → γ)
    (is : Fin q → γ) (ps : Fin ℓ → γ) (v : γ → A) :
    (@Formula.Realize _ A ((sweepBlock a q ℓ).structure₁ (L := M) ρ) _ (rowAt ws is ps) v) ↔
      ρ true (j3 (v ∘ ws) (v ∘ is) (v ∘ ps)) := by
  let := (sweepBlock a q ℓ).structure₁ (L := M) ρ
  rw [rowAt, Formula.realize_rel]
  refine iff_of_eq (congrArg (ρ true) ?_)
  exact (comp_append v (Fin.append ws is) ps).trans
    (congrArg (fun f => Fin.append f (v ∘ ps)) (comp_append v ws is))

variable (ℓ) in
/-- “The row of this index may be written”: the index is the first one, or the
row of the index it covers is done. -/
noncomputable def readyF (bot : M.Formula (Fin q)) (cov : M.Formula (Fin q ⊕ Fin q)) :
    (M.sum (sweepBlock a q ℓ).lang).Formula (Fin a ⊕ Fin q) :=
  Formula.relabel Sum.inr (LHom.sumInl.onFormula bot) ⊔
    Formula.iExs (Fin q)
      ((Formula.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) (LHom.sumInl.onFormula cov) :
          (M.sum (sweepBlock a q ℓ).lang).Formula ((Fin a ⊕ Fin q) ⊕ Fin q)) ⊓
        doneAt ℓ (Sum.inl ∘ Sum.inl) Sum.inr)

theorem realize_readyF (ρ : (sweepBlock a q ℓ).Assignment A) (bot : M.Formula (Fin q))
    (cov : M.Formula (Fin q ⊕ Fin q)) (w : Fin a → A) (i : Fin q → A) :
    (@Formula.Realize _ A ((sweepBlock a q ℓ).structure₁ (L := M) ρ) _ (readyF ℓ bot cov)
        (Sum.elim w i)) ↔
      bot.Realize i ∨ ∃ i₀ : Fin q → A, cov.Realize (Sum.elim i₀ i) ∧ ρ false (j2 w i₀) := by
  have hd := fun v : (Fin a ⊕ Fin q) ⊕ Fin q → A =>
    realize_doneAt (M := M) (ℓ := ℓ) ρ (Sum.inl ∘ Sum.inl) Sum.inr v
  let := (sweepBlock a q ℓ).structure₁ (L := M) ρ
  have hl : ∀ {α : Type} (φ : M.Formula α) (v : α → A),
      ((LHom.sumInl : M →ᴸ M.sum (sweepBlock a q ℓ).lang).onFormula φ).Realize v ↔
        φ.Realize v :=
    fun φ v => LHom.realize_onFormula _ φ
  refine Formula.realize_sup.trans (or_congr (Formula.realize_relabel.trans (hl bot _))
    (Formula.realize_iExs.trans (exists_congr fun i₀ => ?_)))
  refine Formula.realize_inf.trans (and_congr
    ((Formula.realize_relabel.trans (hl cov _)).trans (iff_of_eq (congrArg _ ?_))) (hd _))
  funext x
  rcases x with k | k <;> rfl

end SweepFormulas

/-- **A sweep stratum**: rows indexed by the tuples of a linear order given by
its least element (`bot`) and its covers (`cov`), each row defined by the
formula `Θ` – about parameters, an index and a position – which may read the
rows before it. -/
@[reducible] noncomputable def sweep {a q ℓ : ℕ} (bot : M.Formula (Fin q))
    (cov : M.Formula (Fin q ⊕ Fin q))
    (Θ : (M.sum (sweepBlock a q ℓ).lang).Formula ((Fin a ⊕ Fin q) ⊕ Fin ℓ)) : Lax535992.InflationaryFixedPoint.StepDef M where
  B := sweepBlock a q ℓ
  step := fun b =>
    match b with
    | false => Formula.relabel g2 (readyF ℓ bot cov)
    | true =>
        Formula.relabel g3 ((∼(doneAt ℓ (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)) ⊓
          Formula.relabel Sum.inl (readyF ℓ bot cov)) ⊓ Θ)
  out := ⊤

section SweepLimit

variable {a q ℓ : ℕ} {A : Type} [M.Structure A]

variable {Idx : Type} [LinearOrder Idx] [Finite Idx]

/-- **The limit of a sweep stratum is the family of its rows.** The index
tuples are read as the elements of a finite linear order through `ix`; the
formula `Θ` realizes a condition `Φ` on the rows, which determines the row of
an index from the rows before it. -/
theorem inflLimit_sweep (ix : (Fin q → A) ≃ Idx) (bot : M.Formula (Fin q))
    (cov : M.Formula (Fin q ⊕ Fin q))
    (Θ : (M.sum (sweepBlock a q ℓ).lang).Formula ((Fin a ⊕ Fin q) ⊕ Fin ℓ))
    (hbot : ∀ i : Fin q → A, bot.Realize i ↔ ∀ c, ix i ≤ c)
    (hcov : ∀ i₀ i : Fin q → A, cov.Realize (Sum.elim i₀ i) ↔ ix i₀ ⋖ ix i)
    (Φ : (Fin a → A) → Idx → (Idx → (Fin ℓ → A) → Prop) → (Fin ℓ → A) → Prop)
    (T : (Fin a → A) → Idx → (Fin ℓ → A) → Prop)
    (hΦ : ∀ w i (R : Idx → (Fin ℓ → A) → Prop), (∀ i', i' < i → R i' = T w i') →
      Φ w i R = T w i)
    (hΘ : ∀ (ρ : (sweepBlock a q ℓ).Assignment A) (w : Fin a → A) (i : Fin q → A)
      (p : Fin ℓ → A),
      (@Formula.Realize _ A ((sweepBlock a q ℓ).structure₁ (L := M) ρ) _ Θ
          (Sum.elim (Sum.elim w i) p)) ↔
        Φ w (ix i) (fun i' p' => ρ true (j3 w (ix.symm i') p')) p)
    (w : Fin a → A) (i : Fin q → A) (p : Fin ℓ → A) :
    (sweep bot cov Θ).inflLimit A true (j3 w i p) ↔ T w (ix i) p := by
  have hready : ∀ (ρ : (sweepBlock a q ℓ).Assignment A) (w : Fin a → A) (i' : Idx),
      (@Formula.Realize _ A ((sweepBlock a q ℓ).structure₁ (L := M) ρ) _ (readyF ℓ bot cov)
          (Sum.elim w (ix.symm i'))) ↔
        ((∀ c, i' ≤ c) ∨ ∃ i₀, i₀ ⋖ i' ∧ ρ false (j2 w (ix.symm i₀))) := by
    intro ρ w i'
    rw [realize_readyF, hbot, ix.apply_symm_apply]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨i₀, hc, hd⟩
      rw [hcov, ix.apply_symm_apply] at hc
      exact ⟨ix i₀, hc, by rwa [ix.symm_apply_apply]⟩
    · rintro ⟨i₀, hc, hd⟩
      refine ⟨ix.symm i₀, ?_, hd⟩
      rw [hcov, ix.apply_symm_apply, ix.apply_symm_apply]
      exact hc
  have key := sweep_limit Φ T hΦ
    (Dn := fun s w i' => (sweep bot cov Θ).inflStage A s false (j2 w (ix.symm i')))
    (Rw := fun s w i' p => (sweep bot cov Θ).inflStage A s true (j3 w (ix.symm i') p))
    (fun _ _ h => h) (fun _ _ _ h => h)
    (by
      intro s w i'
      rw [StepDef.inflStage_succ]
      refine or_congr Iff.rfl ?_
      let := (sweepBlock a q ℓ).structure₁ (L := M) ((sweep bot cov Θ).inflStage A s)
      refine Iff.trans ?_ (hready _ w i')
      change (Formula.relabel g2 (readyF ℓ bot cov)).Realize _ ↔ _
      exact Formula.realize_relabel.trans (iff_of_eq (congrArg _ (j2_comp_g2 _ _))))
    (by
      intro s w i' p
      rw [StepDef.inflStage_succ]
      refine or_congr Iff.rfl ?_
      have hd := realize_doneAt (M := M) (ℓ := ℓ) ((sweep bot cov Θ).inflStage A s)
        (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) (Sum.elim (Sum.elim w (ix.symm i')) p)
      have hr := hready ((sweep bot cov Θ).inflStage A s) w i'
      have hθ := hΘ ((sweep bot cov Θ).inflStage A s) w (ix.symm i') p
      rw [ix.apply_symm_apply] at hθ
      let := (sweepBlock a q ℓ).structure₁ (L := M) ((sweep bot cov Θ).inflStage A s)
      change (Formula.relabel g3 ((∼(doneAt ℓ (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)) ⊓
          Formula.relabel Sum.inl (readyF ℓ bot cov)) ⊓ Θ)).Realize _ ↔ _
      refine Formula.realize_relabel.trans
        ((iff_of_eq (congrArg _ (j3_comp_g3 _ _ _))).trans ?_)
      refine Formula.realize_inf.trans ((and_congr (Formula.realize_inf.trans (and_congr
        (Formula.realize_not.trans (not_congr hd)) (Formula.realize_relabel.trans hr)))
        hθ).trans and_assoc))
    w (ix i) p
  rw [ix.symm_apply_apply] at key
  exact key

end SweepLimit

end Digits

/-! ### Extensions -/

section Ext

variable {K : Language.{0, 0}}

/-- An induction **extends** another when it computes, among others, the same
relations: a map of the relation variables, preserving the arities and the
limits. -/
structure StepDef.Ext (e e' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)) where
  /-- Where a relation variable of the first induction is in the second. -/
  emb : e.B.ι → e'.B.ι
  /-- The arities are preserved. -/
  arity_emb : ∀ i, e'.B.arity (emb i) = e.B.arity i
  /-- The limits are preserved. -/
  limit : ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A],
    SOBlock.homAssign emb arity_emb (e'.inflLimit A) = e.inflLimit A

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (Ext)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Ext

export Lax366625Proofs.DescriptiveComplexity.StepDef.Ext (arity_emb emb limit)

end Lax535992.InflationaryFixedPoint.StepDef.Ext

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

namespace StepDef.Ext

variable {e e' e'' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)}

/-- Every induction extends itself. -/
def refl (e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)) : e.Ext e where
  emb := id
  arity_emb := fun _ => rfl
  limit := fun _ _ _ _ => rfl

end StepDef.Ext

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Ext

export Lax366625Proofs.DescriptiveComplexity.StepDef.Ext (refl)

end Lax535992.InflationaryFixedPoint.StepDef.Ext

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

namespace StepDef.Ext

variable {e e' e'' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)}

/-- Extensions compose. -/
def trans (x : e.Ext e') (y : e'.Ext e'') : e.Ext e'' where
  emb := y.emb ∘ x.emb
  arity_emb := fun i => (y.arity_emb (x.emb i)).trans (x.arity_emb i)
  limit := fun A _ _ _ => by
    rw [← x.limit A, ← y.limit A]
    rfl

end StepDef.Ext

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Ext

export Lax366625Proofs.DescriptiveComplexity.StepDef.Ext (trans)

end Lax535992.InflationaryFixedPoint.StepDef.Ext

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

namespace StepDef.Ext

variable {e e' e'' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)}

/-- **Adding a stratum extends an induction.** -/
noncomputable def stratify (e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order))
    (d : Lax535992.InflationaryFixedPoint.StepDef ((K.sum Language.order).sum e.B.lang)) : e.Ext (e.stratify d) where
  emb := fun i => .inl (.inl i)
  arity_emb := fun _ => rfl
  limit := fun _ _ _ _ => e.strat1Assign_inflLimit d

end StepDef.Ext

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Ext

export Lax366625Proofs.DescriptiveComplexity.StepDef.Ext (stratify)

end Lax535992.InflationaryFixedPoint.StepDef.Ext

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

namespace StepDef.Ext

variable {e e' e'' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)}

/-- The symbol of a relation variable, in an extension. -/
def sym (x : e.Ext e') {r : ℕ} (j : e.B.lang.Relations r) : e'.B.lang.Relations r :=
  ⟨x.emb j.1, (x.arity_emb j.1).trans j.2⟩

end StepDef.Ext

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Ext

export Lax366625Proofs.DescriptiveComplexity.StepDef.Ext (sym)

end Lax535992.InflationaryFixedPoint.StepDef.Ext

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

namespace StepDef.Ext

variable {e e' e'' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)}

end StepDef.Ext

/-- The relation variable `j` of the induction `e` **computes** the relation
`R` of ordered structures. -/
def StepDef.Computes (e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)) {r : ℕ} (j : e.B.lang.Relations r)
    (R : ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin r → A) → Prop) : Prop :=
  ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (x : Fin r → A),
    e.inflLimit A j.1 (fun k => x (Fin.cast j.2 k)) ↔ R A x

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (Computes)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

theorem StepDef.Computes.ext {e e' : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order)} {r : ℕ}
    {j : e.B.lang.Relations r}
    {R : ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin r → A) → Prop}
    (h : e.Computes j R) (x : e.Ext e') : e'.Computes (x.sym j) R := by
  intro A _ _ _ _ y
  rw [← h A y, ← x.limit A]
  rfl

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef.Computes

export Lax366625Proofs.DescriptiveComplexity.StepDef.Computes (ext)

end Lax535992.InflationaryFixedPoint.StepDef.Computes

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

/-- **The relations of a new stratum**, in the stratified induction: their
limits are those of the stratum, over the structure expanded by the limit of
the induction below. -/
theorem StepDef.inflLimit_stratify_inr (e : Lax535992.InflationaryFixedPoint.StepDef (K.sum Language.order))
    (d : Lax535992.InflationaryFixedPoint.StepDef ((K.sum Language.order).sum e.B.lang)) (A : Type) [K.Structure A]
    [LinearOrder A] [Finite A] (i : d.B.ι) (x : Fin (d.B.arity i) → A) :
    (e.stratify d).inflLimit A (.inr i) x ↔
      @Lax535992.InflationaryFixedPoint.StepDef.inflLimit _ d A (e.B.structure₁ (L := K.sum Language.order) (e.inflLimit A))
        i x :=
  iff_of_eq (congrFun (congrFun (e.strat2Assign_inflLimit d (A := A)) i) x)

end Ext

end Lax366625Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax366625Proofs.DescriptiveComplexity.StepDef (inflLimit_stratify_inr)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Ext

variable {K : Language.{0, 0}}

end Ext

end Lax366625Proofs.DescriptiveComplexity


