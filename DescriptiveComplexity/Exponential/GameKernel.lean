/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameRounds

/-!
# A defining formula of an interpretation, with its arguments pinned to rounds

`DescriptiveComplexity.ExpExpansion.exists_transl` translates a *prenex* formula
over an exponential expansion into a kernel quantified by the rounds that remain
above `c`, the rounds below `c` holding the values of its free variables. What an
interpretation hands over is not that: it is a
`FirstOrder.Language.Formula (Fin k × Fin dim)`, one free variable per coordinate
of each argument tuple.

This file closes the gap once and for all, for the two-argument case that covers
every relation symbol of `DescriptiveComplexity.Language.andOrGraph` (a unary
symbol simply ignores the second argument):

> **`DescriptiveComplexity.ExpExpansion.exists_paramKernel`** – for every
> `φ : (X.E + ≤).Formula (Fin 2 × Fin d)` there is a round count `D` such that,
> at *any* layout with at least `2 * d` parameter rounds and exactly `D` play
> rounds, a kernel `K` exists whose alternating value over the play rounds is
> `φ`, its argument `(a, b)` read at the round
> `DescriptiveComplexity.ExpExpansion.paramIx a b` – that is, at round
> `a * d + b`, so that the first argument occupies the rounds below `d` and the
> second the rounds below `2 * d`.

The bookkeeping is three renamings and nothing else: the free variables become
bound slots (`FirstOrder.Language.BoundedFormula.relabel`), the result is put in
prenex form (`FirstOrder.Language.BoundedFormula.toPrenex`, whose *proof* is what
`exists_transl` recurses on), and the slots are sent to their rounds by the `hv`
argument of `exists_transl`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-! ### Where an argument coordinate sits -/

variable {X}

/-- Coordinate `b` of argument `a` sits at round `a * d + b`: the first
argument's points occupy the rounds below `d`, the second's the next `d`. -/
def paramIx (d n : ℕ) (h : 2 * d ≤ n) (a : Fin 2) (b : Fin d) : Fin n :=
  ⟨(a : ℕ) * d + (b : ℕ), by
    refine Nat.lt_of_lt_of_le ?_ h
    have ha : (a : ℕ) * d ≤ 1 * d := Nat.mul_le_mul_right d (Nat.lt_succ_iff.mp a.isLt)
    omega⟩

@[simp]
theorem paramIx_val (d n : ℕ) (h : 2 * d ≤ n) (a : Fin 2) (b : Fin d) :
    (paramIx d n h a b : ℕ) = (a : ℕ) * d + (b : ℕ) :=
  rfl

/-! ### The formula, with its arguments freed into slots -/

variable (X) in
/-- The defining formula of an interpretation, its free variables pushed into
bound slots so that `DescriptiveComplexity.ExpExpansion.exists_transl` can
consume it. -/
noncomputable def argsFreed {d : ℕ} (φ : (X.E.sum Language.order).Formula (Fin 2 × Fin d)) :
    (X.E.sum Language.order).BoundedFormula Empty (2 * d) :=
  (BoundedFormula.relabel
    (fun p : Fin 2 × Fin d => (Sum.inr ⟨(p.1 : ℕ) * d + (p.2 : ℕ), by
      have ha : (p.1 : ℕ) * d ≤ 1 * d := Nat.mul_le_mul_right d (Nat.lt_succ_iff.mp p.1.isLt)
      omega⟩ : Empty ⊕ Fin (2 * d))) φ).toPrenex

theorem argsFreed_isPrenex {d : ℕ} (φ : (X.E.sum Language.order).Formula (Fin 2 × Fin d)) :
    (argsFreed X φ).IsPrenex :=
  BoundedFormula.toPrenex_isPrenex _

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **Freeing the arguments changes nothing**: read at any tuple of points, the
freed formula says what the original said of the points its coordinates
name. -/
theorem realize_argsFreed {d : ℕ} (φ : (X.E.sum Language.order).Formula (Fin 2 × Fin d))
    (xs : Fin (2 * d) → X.Map A) :
    letI := X.mapLinearOrder A
    ((argsFreed X φ).Realize (M := X.Map A) default xs ↔
      φ.Realize (M := X.Map A) fun p => xs ⟨(p.1 : ℕ) * d + (p.2 : ℕ), by
        have ha : (p.1 : ℕ) * d ≤ 1 * d := Nat.mul_le_mul_right d (Nat.lt_succ_iff.mp p.1.isLt)
        omega⟩) := by
  let := X.mapLinearOrder A
  have := X.mapNonempty A
  rw [argsFreed, BoundedFormula.realize_toPrenex, BoundedFormula.realize_relabel]
  refine iff_of_eq (congrArg₂ _ (funext fun p => ?_) (Subsingleton.elim _ _))
  rfl

/-! ### The kernel -/

/-- **A defining formula, played as an alternating prefix.** The round count `D`
depends on the formula alone; the layout – how many parameter rounds sit below
the play rounds – is free, so that finitely many formulas can share one block by
padding the short ones. -/
theorem exists_paramKernel (X : ExpExpansion L) {d : ℕ}
    (φ : (X.E.sum Language.order).Formula (Fin 2 × Fin d)) :
    ∃ D : ℕ, ∀ (n c : ℕ) (_hcn : c + D = n) (_h2d : 2 * d ≤ c),
      ∃ K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence,
        ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
          letI := X.mapLinearOrder A
          ∀ (pts : Fin n → X.Map A)
            (ext : (Fin D → X.pointBlock.Assignment A) →
              (Fin n → X.pointBlock.Assignment A)),
            (∀ τs (k : Fin n), (k : ℕ) < c → ext τs k = pointAssign (pts k)) →
            (∀ τs (i : Fin D) (k : Fin n), (k : ℕ) = c + (i : ℕ) → ext τs k = τs i) →
            (altBlockQuant A X.pointBlock D
                (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) K) true ↔
              φ.Realize (M := X.Map A) fun p =>
                pts (paramIx d n (by omega) p.1 p.2)) := by
  obtain ⟨D, hD⟩ := exists_transl (X := X) (argsFreed_isPrenex φ)
  refine ⟨D, fun n c _hcn _h2d => ?_⟩
  have hle : 2 * d ≤ n := by omega
  obtain ⟨K, hK⟩ := hD n c D _hcn rfl
    (fun i => ⟨(i : ℕ), by omega⟩) (fun i => by exact i.isLt.trans_le (by omega))
  refine ⟨K, fun A _ _ _ _ pts ext hfix hemb => ?_⟩
  let := X.mapLinearOrder A
  refine (hK A pts ext hfix hemb).trans ?_
  refine (realize_argsFreed φ fun i => pts ⟨(i : ℕ), by omega⟩).trans ?_
  exact Iff.rfl

end ExpExpansion

end DescriptiveComplexity
