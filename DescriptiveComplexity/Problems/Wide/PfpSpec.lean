/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpRel
import DescriptiveComplexity.Problems.Wide.PfpEnc
import DescriptiveComplexity.FixedPointPartial

/-!
# What one step of the iteration is, on the machine's side of the encoding

The EXPSPACE program computes the next stage of a partial fixed point at every
logical address. This file states *what it computes*, with no machine in sight:
one application of a step formula to a stage is an alternating prefix over the
**block values** of an address, gated to the encodings, over the gated matrix.

Two pieces:

* `DescriptiveComplexity.Pfp.PrenexPack` – a step formula with free variables,
  put once and for all into the prefix normal form of
  `DescriptiveComplexity.altQuantFrom` (`DescriptiveComplexity.Pfp.exists_prenexPack`:
  rebind the free variables as the first bound ones, then
  `FirstOrder.Language.BoundedFormula.toPrenex`);
* `DescriptiveComplexity.Pfp.StepDef.next_iff_gateMat` – the chain: one step of
  `DescriptiveComplexity.StepDef.next` at a tuple of points **is** the prefix
  over block values, read at any valuation whose first coordinates encode the
  tuple. The quantifiers move from points to block values by
  `DescriptiveComplexity.Pfp.altQuantFrom_gateMat`, whose gate is
  `DescriptiveComplexity.Pfp.IsEnc`.

The valuation's deeper coordinates are arbitrary – the machine's inner register
starts them at whatever is left on its tracks – because a prefix only reads the
coordinates below its level (`DescriptiveComplexity.altQuantFrom_congr_val`).

The linear order on the points is a *parameter* here (the step formula reads it
through the structure); which order the reduction chooses – the pullback of the
binary block-value order along the encoding, making order atoms the register
comparison the machine can run – is its own decision, recorded in
`EXPONENTIAL.md` §6.4.4 and discharged where the machine meets the tape.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language

/-! ### The prefix normal form of a formula with free variables -/

section Prenex

variable {M : Language.{0, 0}}

/-- **A formula in prefix normal form**: the polarities and the quantifier-free
matrix of an alternating prefix equivalent to `φ`, the free variables re-bound
as the first `k` coordinates of the valuation. This is the data the machine's
control is built from, so it is a structure rather than an existential. -/
structure PrenexPack {k : ℕ} (φ : M.Formula (Fin k)) : Type 1 where
  /-- The total number of variables: the free ones first, then the prefix. -/
  n : ℕ
  /-- The free variables come first. -/
  kLe : k ≤ n
  /-- The polarity of each level. -/
  pol : ℕ → Bool
  /-- The matrix. -/
  mat : M.BoundedFormula Empty n
  /-- The matrix is quantifier-free. -/
  isQF : mat.IsQF
  /-- The prefix from level `k` on, at a valuation whose first `k` coordinates
  hold the free variables, is the formula. -/
  spec : ∀ (A : Type) [M.Structure A] [Nonempty A] (v : Fin n → A) (xs : Fin k → A),
    (∀ i : Fin k, xs i = v (Fin.castLE kLe i)) →
    (φ.Realize xs ↔ altQuantFrom pol (fun w => mat.Realize default w) k v)

/-- **Every formula has a prefix normal form** with its free variables re-bound
as the first coordinates: relabel them into the context, take
`FirstOrder.Language.BoundedFormula.toPrenex`, and read the prefix as a walk. -/
theorem exists_prenexPack {k : ℕ} (φ : M.Formula (Fin k)) : Nonempty (PrenexPack φ) := by
  obtain ⟨n, hkn, pol, mat, hqf, hspec⟩ :=
    exists_altQuant_of_isPrenex
      (BoundedFormula.toPrenex_isPrenex
        (BoundedFormula.relabel (Sum.inr : Fin k → Empty ⊕ Fin k) φ))
  refine ⟨⟨n, by omega, pol, mat, hqf, ?_⟩⟩
  intro A _ _ v xs hagree
  have h1 := hspec A v xs hagree
  refine Iff.trans ?_ h1
  rw [BoundedFormula.realize_toPrenex, BoundedFormula.realize_relabel]
  refine iff_of_eq (congrArg₂ (fun a b => BoundedFormula.Realize φ a b) ?_ ?_)
  · funext i
    rfl
  · funext i
    exact i.elim0

end Prenex

/-! ### One step of the iteration, over block values -/

section Chain

variable {L : Language.{0, 0}} {X : ExpExpansion L}
variable {dd : ℕ} (ly : EncLayout (PtCode X) (blockArityBound X.B) dd)
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {zero one : A} [LinearOrder (X.Map A)]
variable {d : StepDef (X.E.sum Language.order)}

open Classical in
/-- **One step of the iteration is the gated prefix over block values.** The
first coordinates of the valuation encode the argument tuple; the deeper ones
are arbitrary, the prefix overwriting every coordinate it reads. This is the
statement the machine's inner loop computes, one fold step per increment of its
register. -/
theorem StepDef.next_iff_gateMat (hne : zero ≠ one) {i : d.B.ι}
    (pk : PrenexPack (d.step i)) (σ : d.B.Assignment (X.Map A))
    (x : Fin (d.B.arity i) → X.Map A)
    {V : Fin pk.n → ((Fin dd → A) → Prop)}
    (hV : ∀ j : Fin (d.B.arity i), V (Fin.castLE pk.kLe j) = encMap ly zero one (x j)) :
    d.next σ i x ↔
      altQuantFrom pk.pol
        (gateMat (encMap ly zero one) (IsEnc ly zero one) pk.pol
          fun w => @BoundedFormula.Realize _ (X.Map A)
            (d.B.structure₁ σ) _ _ pk.mat default w)
        (d.B.arity i) V := by
  letI inst : (X.E.sum Language.order).sum d.B.lang |>.Structure (X.Map A) :=
    d.B.structure₁ σ
  -- the valuation over points: the argument tuple, padded with an arbitrary point
  set vB : Fin pk.n → X.Map A := fun j =>
    if h : (j : ℕ) < d.B.arity i then x ⟨j, h⟩ else Classical.arbitrary (X.Map A) with hvB
  have hxs : ∀ j : Fin (d.B.arity i), x j = vB (Fin.castLE pk.kLe j) := by
    intro j
    rw [hvB]
    simp only [Fin.val_castLE]
    rw [dif_pos j.isLt]
  -- 1. the prefix over points
  have h1 : d.next σ i x ↔
      altQuantFrom pk.pol (fun w => @BoundedFormula.Realize _ (X.Map A) inst _ _ pk.mat
        default w) (d.B.arity i) vB :=
    pk.spec (X.Map A) vB x hxs
  -- 2. the prefix over block values, at the encoded valuation
  have h2 := altQuantFrom_gateMat
    (e := encMap ly zero one) (G := IsEnc ly zero one) (pol := pk.pol)
    (P := fun w => @BoundedFormula.Realize _ (X.Map A) inst _ _ pk.mat default w)
    (encMap_injective ly hne) (isEnc_iff ly) (j := d.B.arity i) vB
  -- 3. the given valuation agrees with the encoded one below the level
  have h3 : altQuantFrom pk.pol
      (gateMat (encMap ly zero one) (IsEnc ly zero one) pk.pol
        fun w => @BoundedFormula.Realize _ (X.Map A) inst _ _ pk.mat default w)
      (d.B.arity i) (fun j => encMap ly zero one (vB j)) =
      altQuantFrom pk.pol
        (gateMat (encMap ly zero one) (IsEnc ly zero one) pk.pol
          fun w => @BoundedFormula.Realize _ (X.Map A) inst _ _ pk.mat default w)
        (d.B.arity i) V := by
    refine altQuantFrom_congr_val _ _ fun j hj => ?_
    have hj' : (j : ℕ) < d.B.arity i := hj
    have hjc : j = Fin.castLE pk.kLe ⟨(j : ℕ), hj'⟩ := Fin.ext rfl
    rw [hjc, hV ⟨(j : ℕ), hj'⟩, hvB]
    simp only [Fin.val_castLE]
    rw [dif_pos hj']
  exact h1.trans (h2.symm.trans (iff_of_eq h3))

end Chain

end Pfp

end DescriptiveComplexity
