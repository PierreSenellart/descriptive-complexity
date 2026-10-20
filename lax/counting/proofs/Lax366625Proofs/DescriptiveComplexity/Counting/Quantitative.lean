/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.Class
import Lax366625Proofs.DescriptiveComplexity.FixedPointHorn
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625Proofs.DescriptiveComplexity.QTerm
end Lax366625Proofs.DescriptiveComplexity.QTerm

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (FPDefinable QLFPDef QTerm)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

/-!
# Quantitative first-order logic, and the class FP

The quantitative logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive], in its first-order
fragment QFO: above a layer of Boolean formulas, a layer of terms denoting
natural numbers,

`α ::= φ | s | α + α | α · α | Σx. α | Πx. α`,

a formula counting `1` when it holds and `0` when it does not, and the two
quantifiers being the sum and the product over the elements of the structure
(`DescriptiveComplexity.QTerm`, `DescriptiveComplexity.QTerm.eval`). The
logic, its semantics and the idea of separating a Boolean level from a
quantitative one are theirs; QSO, the full logic of the paper, has
second-order sums and products as well, which are not formalized here.

**FP**, the class of the functions computable in polynomial time – here those
with natural-number values, which is what a
`DescriptiveComplexity.CountingProblem` is – is *defined* by this logic over a
Boolean layer of least fixed points: a problem is in FP when it is the value
of a QFO term over the vocabulary expanded by the relations of a least fixed
point, on every ordered finite
structure (`DescriptiveComplexity.FPDefinable`). That QFO(LFP) captures FP over
ordered structures is Theorem 4.4 of the paper; it is cited, not proved, as the
capture theorems behind the other logically defined classes of the library
are where no machine characterization is given.

A term over the plain ordered vocabulary, with no fixed point, defines a
problem of FP (`DescriptiveComplexity.fpDefinable_of_qfo`): this is the case of
most concrete functions, the fixed point being what makes the class all of FP.

## Positivity is first-order

Whether a term is positive is a *formula* (`DescriptiveComplexity.QTerm.pos`):
a sum is positive when some summand is, a product when every factor is. So
the support of a problem of FP is in PTIME
(`DescriptiveComplexity.support_mem_PTIME_of_fpDefinable`), as the support of
a problem of `#P` is in NP; and a parsimoniously `#P`-hard problem cannot be
in FP unless `NP ⊆ PTIME`
(`DescriptiveComplexity.NP_subset_PTIME_of_parsimoniousHard_of_fpDefinable`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Terms -/

namespace QTerm

variable {L L' : Language.{0, 0}}

/-- Reading a term in a larger vocabulary. -/
def onTerm (Φ : L →ᴸ L') : ∀ {α : Type}, Lax366625.QuantitativeLogic.QTerm L α → Lax366625.QuantitativeLogic.QTerm L' α
  | _, Lax366625.QuantitativeLogic.QTerm.ind φ => Lax366625.QuantitativeLogic.QTerm.ind (Φ.onFormula φ)
  | _, Lax366625.QuantitativeLogic.QTerm.const s => Lax366625.QuantitativeLogic.QTerm.const s
  | _, Lax366625.QuantitativeLogic.QTerm.add s t => Lax366625.QuantitativeLogic.QTerm.add ((onTerm Φ s)) ((onTerm Φ t))
  | _, Lax366625.QuantitativeLogic.QTerm.mul s t => Lax366625.QuantitativeLogic.QTerm.mul ((onTerm Φ s)) ((onTerm Φ t))
  | _, Lax366625.QuantitativeLogic.QTerm.sum n t => Lax366625.QuantitativeLogic.QTerm.sum n ((onTerm Φ t))
  | _, Lax366625.QuantitativeLogic.QTerm.prod n t => Lax366625.QuantitativeLogic.QTerm.prod n ((onTerm Φ t))

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (onTerm)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

theorem eval_onTerm (Φ : L →ᴸ L') {A : Type} [L.Structure A] [L'.Structure A]
    [Φ.IsExpansionOn A] {α : Type} (t : Lax366625.QuantitativeLogic.QTerm L α) (v : α → A) :
    (t.onTerm Φ).eval v = t.eval v := by
  induction t with
  | ind φ =>
    by_cases h : φ.Realize v <;> simp [onTerm, Lax366625.QuantitativeLogic.QTerm.eval, LHom.realize_onFormula, h]
  | const s => rfl
  | add s t hs ht => simp only [onTerm, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | mul s t hs ht => simp only [onTerm, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | sum n t ht => simp only [onTerm, Lax366625.QuantitativeLogic.QTerm.eval, ht]
  | prod n t ht => simp only [onTerm, Lax366625.QuantitativeLogic.QTerm.eval, ht]

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (eval_onTerm)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

/-- Renaming the free variables of a term. -/
def relabel : ∀ {α : Type}, Lax366625.QuantitativeLogic.QTerm L α → ∀ {β : Type}, (α → β) → Lax366625.QuantitativeLogic.QTerm L β
  | _, Lax366625.QuantitativeLogic.QTerm.ind φ, _, f => Lax366625.QuantitativeLogic.QTerm.ind (φ.relabel f)
  | _, Lax366625.QuantitativeLogic.QTerm.const s, _, _ => Lax366625.QuantitativeLogic.QTerm.const s
  | _, Lax366625.QuantitativeLogic.QTerm.add s t, _, f => Lax366625.QuantitativeLogic.QTerm.add ((relabel s) f) ((relabel t) f)
  | _, Lax366625.QuantitativeLogic.QTerm.mul s t, _, f => Lax366625.QuantitativeLogic.QTerm.mul ((relabel s) f) ((relabel t) f)
  | _, Lax366625.QuantitativeLogic.QTerm.sum n t, _, f => Lax366625.QuantitativeLogic.QTerm.sum n ((relabel t) (Sum.map f id))
  | _, Lax366625.QuantitativeLogic.QTerm.prod n t, _, f => Lax366625.QuantitativeLogic.QTerm.prod n ((relabel t) (Sum.map f id))

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (relabel)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

theorem eval_relabel {A : Type} [L.Structure A] {α : Type} (t : Lax366625.QuantitativeLogic.QTerm L α) :
    ∀ {β : Type} (f : α → β) (v : β → A), (t.relabel f).eval v = t.eval (v ∘ f) := by
  induction t with
  | ind φ =>
    intro β f v
    by_cases h : φ.Realize (v ∘ f) <;> simp [relabel, Lax366625.QuantitativeLogic.QTerm.eval, Formula.realize_relabel, h]
  | const s => intro β f v; rfl
  | add s t hs ht => intro β f v; simp only [relabel, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | mul s t hs ht => intro β f v; simp only [relabel, Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | sum n t ht =>
    intro β f v
    simp only [relabel, Lax366625.QuantitativeLogic.QTerm.eval, ht, Sum.elim_comp_map, Function.comp_id]
  | prod n t ht =>
    intro β f v
    simp only [relabel, Lax366625.QuantitativeLogic.QTerm.eval, ht, Sum.elim_comp_map, Function.comp_id]

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (eval_relabel)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

/-- **The value of a term is isomorphism-invariant.** -/
theorem eval_equiv {A B : Type} [L.Structure A] [L.Structure B] (e : A ≃[L] B) {α : Type}
    (t : Lax366625.QuantitativeLogic.QTerm L α) (v : α → A) : t.eval (e ∘ v) = t.eval v := by
  induction t with
  | ind φ =>
    have h := StrongHomClass.realize_formula e φ (v := v)
    by_cases hφ : φ.Realize v <;> simp [Lax366625.QuantitativeLogic.QTerm.eval, h, hφ]
  | const s => rfl
  | add s t hs ht => simp only [Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | mul s t hs ht => simp only [Lax366625.QuantitativeLogic.QTerm.eval, hs, ht]
  | sum n t ht =>
    simp only [Lax366625.QuantitativeLogic.QTerm.eval]
    refine (finsum_comp_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e.toEquiv)).symm.trans
      (finsum_congr fun w => ?_)
    rw [← ht (Sum.elim v w)]
    exact congrArg t.eval (funext fun x => by cases x <;> rfl)
  | prod n t ht =>
    simp only [Lax366625.QuantitativeLogic.QTerm.eval]
    refine (finprod_comp_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e.toEquiv)).symm.trans
      (finprod_congr fun w => ?_)
    rw [← ht (Sum.elim v w)]
    exact congrArg t.eval (funext fun x => by cases x <;> rfl)

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (eval_equiv)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

/-! ### Positivity -/

/-- **“The term is positive”, as a formula**: a formula is positive when it
holds, a sum when some summand is, a product when every factor is. -/
noncomputable def pos : ∀ {α : Type}, Lax366625.QuantitativeLogic.QTerm L α → L.Formula α
  | _, Lax366625.QuantitativeLogic.QTerm.ind φ => φ
  | _, Lax366625.QuantitativeLogic.QTerm.const s => if s = 0 then ⊥ else ⊤
  | _, Lax366625.QuantitativeLogic.QTerm.add s t => (pos s) ⊔ (pos t)
  | _, Lax366625.QuantitativeLogic.QTerm.mul s t => (pos s) ⊓ (pos t)
  | _, Lax366625.QuantitativeLogic.QTerm.sum n t => Formula.iExs (Fin n) (pos t)
  | _, Lax366625.QuantitativeLogic.QTerm.prod n t => Formula.iAlls (Fin n) (pos t)

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (pos)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

theorem realize_pos {A : Type} [L.Structure A] [Finite A] {α : Type} (t : Lax366625.QuantitativeLogic.QTerm L α)
    (v : α → A) : t.pos.Realize v ↔ t.eval v ≠ 0 := by
  classical
  let := Fintype.ofFinite A
  induction t with
  | ind φ =>
    by_cases h : φ.Realize v <;> simp [pos, Lax366625.QuantitativeLogic.QTerm.eval, h]
  | const s =>
    by_cases h : s = 0 <;> simp [pos, Lax366625.QuantitativeLogic.QTerm.eval, h]
  | add s t hs ht =>
    simp only [pos, Lax366625.QuantitativeLogic.QTerm.eval, Formula.realize_sup, hs, ht]
    omega
  | mul s t hs ht =>
    simp only [pos, Lax366625.QuantitativeLogic.QTerm.eval, Formula.realize_inf, hs, ht, Nat.mul_ne_zero_iff]
  | sum n t ht =>
    simp only [pos, Lax366625.QuantitativeLogic.QTerm.eval, Formula.realize_iExs, ht, finsum_eq_sum_of_fintype]
    rw [Ne, Finset.sum_eq_zero_iff]
    simp
  | prod n t ht =>
    simp only [pos, Lax366625.QuantitativeLogic.QTerm.eval, Formula.realize_iAlls, ht, finprod_eq_prod_of_fintype]
    rw [Finset.prod_ne_zero_iff]
    simp

end QTerm

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.QTerm

export Lax366625Proofs.DescriptiveComplexity.QTerm (realize_pos)

end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

end QTerm

/-! ### FP -/

variable {L : Language.{0, 0}} [L.IsRelational]

theorem fpDefinable_congr {C C' : Lax366625.CountingProblems.CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (hC : Lax366625.QuantitativeLogic.FPDefinable C) :
    Lax366625.QuantitativeLogic.FPDefinable C' := by
  obtain ⟨d, hd⟩ := hC
  exact ⟨d, fun A _ _ _ _ => (h A).symm.trans (hd A)⟩

/-- **A term with no fixed point defines a problem of FP**: a counting problem
that is the value of a QFO term over the ordered vocabulary is in FP. -/
theorem fpDefinable_of_qfo {C : Lax366625.CountingProblems.CountingProblem L} (t : Lax366625.QuantitativeLogic.QTerm (L.sum Language.order) Empty)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = t.value A) : Lax366625.QuantitativeLogic.FPDefinable C := by
  refine ⟨⟨⟨Empty, fun e => e.elim⟩, 0, [], t.onTerm LHom.sumInl⟩, fun A _ _ _ _ => ?_⟩
  let := (⟨Empty, fun e => e.elim⟩ : Lax904597.SecondOrder.SOBlock).structure
    (Lax535992.LeastFixedPoint.lfpAssign (A := A) ([] : List (Lax535992.HornFragment.HornClause (L.sum Language.order) ⟨Empty, fun e => e.elim⟩ 0)))
  exact (h A).trans (QTerm.eval_onTerm LHom.sumInl t default).symm

/-- **The support of a problem of FP is in PTIME**: positivity of the output
term is a first-order formula over the fixed point. -/
theorem support_mem_PTIME_of_fpDefinable {C : Lax366625.CountingProblems.CountingProblem L} (h : Lax366625.QuantitativeLogic.FPDefinable C) :
    C.support ∈ PTIME := by
  obtain ⟨d, hd⟩ := h
  refine (lfpDefinable_iff_mem_PTIME _).mp ⟨⟨d.B, d.k, d.rules, d.out.pos⟩, ?_⟩
  intro A _ _ _ _
  let := d.B.structure (Lax535992.LeastFixedPoint.lfpAssign (A := A) d.rules)
  rw [CountingProblem.support_iff, hd A]
  exact Nat.pos_iff_ne_zero.trans (QTerm.realize_pos d.out (default : Empty → A)).symm

/-- **A problem of FP is not parsimoniously `#P`-hard, unless `NP ⊆ PTIME`.** -/
theorem NP_subset_PTIME_of_parsimoniousHard_of_fpDefinable {C : Lax366625.CountingProblems.CountingProblem L}
    (hard : SharpP.ParsimoniousHard C) (h : Lax366625.QuantitativeLogic.FPDefinable C) : NP ⊆ PTIME :=
  NP_subset_PTIME_of_sharpP_parsimoniousHard hard (support_mem_PTIME_of_fpDefinable h)

end Lax366625Proofs.DescriptiveComplexity


