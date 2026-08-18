/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.PointAtoms

/-!
# Translating a quantifier-free matrix

`DescriptiveComplexity.Exponential.PointAtoms` writes each *atom* of a sentence
over an expansion as a sentence of the quantifier prefix. This file closes the
Boolean connectives over them: a quantifier-free formula whose free variables
range over the points of the expanded universe becomes a sentence of the prefix,
variable `i` read at round `i`.

Two points of technique.

**The recursion is total, the correctness is not.** `IsQF` is a `Prop`, so a
definition cannot recurse on it. `DescriptiveComplexity.ExpExpansion.translQF`
is therefore defined on *every* bounded formula, sending a quantifier node – and
an atom mentioning a bound variable – to `⊥`; correctness is then proved by
induction on `FirstOrder.Language.BoundedFormula.IsQF` at `n = 0`, where no such
node is reachable. This is the shape the abandoned quantifier-free-reduction
track would have used too, and it is the standard way to recurse on a syntactic
class carved out by a `Prop`.

**Function symbols are impossible, not junk.** The expanded vocabulary and the
order vocabulary are both relational, so `FirstOrder.Language.Term.func` is
eliminated by `isEmptyElim` rather than mapped to a default: a term *is* a
variable (`DescriptiveComplexity.ExpExpansion.termVar`). Only the distinction
between a free and a bound variable needs an `Option`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : ExpExpansion L} {m : ℕ}

/-! ### Terms are variables -/

/-- The variable a term is. Over a relational vocabulary there is nothing else
a term can be, so the function case is `isEmptyElim`. -/
def termVar {n : ℕ} : (X.E.sum Language.order).Term (Fin m ⊕ Fin n) → Fin m ⊕ Fin n
  | .var x => x
  | .func f _ => isEmptyElim f

theorem realize_termVar {A : Type} [(X.E.sum Language.order).Structure A] {n : ℕ}
    (v : (Fin m ⊕ Fin n) → A) :
    ∀ t : (X.E.sum Language.order).Term (Fin m ⊕ Fin n), t.realize v = v (termVar t)
  | .var _ => rfl
  | .func f _ => isEmptyElim f

/-! ### The atoms, selected by the relation symbol -/

variable (X m) in
/-- The prefix-level sentence of an atom, given the round each argument names:
a relation of the expanded vocabulary, or the order. -/
noncomputable def atomOf {k : ℕ} (r : (X.E.sum Language.order).Relations k)
    (idx : Fin k → Fin m) :
    ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence :=
  match k, r with
  | _, Sum.inl s => pointRelF X m s idx
  | _, Sum.inr .le => pointLeF X m (idx 0) (idx 1)

/-! ### The translation

The recursion carries a map `bv` sending each *bound* variable to a round. A
quantifier node is sent to `⊥`, so `bv` is never extended and never consulted at
the depth the correctness proof works at – where it is `finZeroElim`, the empty
map. Carrying it is what keeps the definition total without an `Option` in every
atom. -/

variable (X m) in
/-- **The translation of a quantifier-free matrix.** Total, so that it is a
definition; correct on quantifier-free formulas, which is
`DescriptiveComplexity.ExpExpansion.realize_translQF`. -/
noncomputable def translQF :
    ∀ {n : ℕ}, (Fin n → Fin m) → (X.E.sum Language.order).BoundedFormula (Fin m) n →
      ((L.sum Language.order).sum (repMerged X.pointBlock m).lang).Sentence
  | _, _, .falsum => ⊥
  | _, bv, .equal t₁ t₂ =>
      pointEqF X m (Sum.elim id bv (termVar t₁)) (Sum.elim id bv (termVar t₂))
  | _, bv, .rel r ts => atomOf X m r fun j => Sum.elim id bv (termVar (ts j))
  | _, bv, .imp φ ψ => translQF bv φ ⟹ translQF bv ψ
  | _, _, .all _ => ⊥

/-! ### Correctness -/

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- At no bound variables, a valuation of the free variables reads a variable
through its round. -/
theorem elim_finZeroElim (pts : Fin m → X.Map A) (x : Fin m ⊕ Fin 0) :
    letI := X.mapLinearOrder A
    Sum.elim pts (default : Fin 0 → X.Map A) x = pts (Sum.elim id finZeroElim x) := by
  match x with
  | Sum.inl _ => rfl
  | Sum.inr k => exact k.elim0

/-- **The matrix says what it should**: on a quantifier-free formula, the
translated sentence holds of the prefix exactly when the formula holds of the
points the rounds carry. -/
theorem realize_translQF (pts : Fin m → X.Map A)
    {φ : (X.E.sum Language.order).Formula (Fin m)} (hqf : φ.IsQF) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A (prefixStructure pts) (translQF X m finZeroElim φ) ↔
      φ.Realize (M := X.Map A) pts) := by
  let := X.mapLinearOrder A
  let := prefixStructure pts
  induction hqf with
  | falsum => exact Iff.rfl
  | of_isAtomic hat =>
    cases hat with
    | equal t₁ t₂ =>
      refine (realize_pointEqF pts _ _).trans ?_
      rw [Formula.Realize, BoundedFormula.realize_bdEqual, realize_termVar, realize_termVar,
        elim_finZeroElim, elim_finZeroElim]
    | rel r ts =>
      rw [Formula.Realize, BoundedFormula.realize_rel]
      have hv : ∀ j, (ts j).realize (Sum.elim pts (default : Fin 0 → X.Map A)) =
          pts (Sum.elim id finZeroElim (termVar (ts j))) := fun j =>
        (realize_termVar _ (ts j)).trans (elim_finZeroElim pts _)
      cases r with
      | inl s =>
        refine (realize_pointRelF pts s _).trans ?_
        exact iff_of_eq (congrArg _ (funext fun j => (hv j).symm))
      | inr o =>
        cases o with
        | le =>
          refine (realize_pointLeF pts _ _).trans ?_
          exact iff_of_eq (congrArg₂ (fun a b => a ≤ b) (hv 0).symm (hv 1).symm)
  | imp _ _ ih₁ ih₂ =>
    rw [Formula.realize_imp]
    exact imp_congr ih₁ ih₂

end ExpExpansion

end DescriptiveComplexity
