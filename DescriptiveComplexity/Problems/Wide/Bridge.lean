/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Blocks
import DescriptiveComplexity.Problems.Wide.Fold

/-!
# The blocks of an address are the valuation the fold runs on

The join between the two halves of the sweep. `DescriptiveComplexity.Problems.Wide.Blocks`
reads an address over a block-major universe as a family of blocks and says how
that family changes along one increment; `DescriptiveComplexity.Problems.Wide.Fold`
says how a quantifier prefix folds along one step of the lexicographic enumeration
of its valuations. They are the same step, and this file says so:

> with the block index type taken to be `Fin n` – which a reduction may simply
> choose, one index per variable of its kernel – the family of blocks
> `DescriptiveComplexity.wmBlk s` **is** a valuation, the value order is
> `DescriptiveComplexity.WMSetLe`, and every hypothesis the fold's three step rules
> ask for is read off `DescriptiveComplexity.wmIncr_lexRel_iff`.

So `DescriptiveComplexity.foldFrom_carry_of_wmIncr` is the fold rule at the carry
index, stated about an address increment and nothing else – the form a program's
step obligation will be discharged in. The blocks after the carry are full before
the step and empty after it, which is exactly the fold's “maximal” and “minimal”
hypotheses (`DescriptiveComplexity.wmSetLe_of_full`,
`DescriptiveComplexity.wmSetLe_of_empty`), and the successor hypothesis is
`DescriptiveComplexity.wmSetLt_iff_of_wmIncr` read through
`DescriptiveComplexity.wmLt_wmSetLe_iff`.
-/

namespace DescriptiveComplexity

open FirstOrder

section Bridge

variable {n : ℕ} {V : Type} [Finite V] {LeV : V → V → Prop}

/-- On an initial segment of `ℕ` the order the address layer writes is the
order. -/
theorem wmLt_fin_iff (σ τ : Fin n) : WMLt (α := Fin n) (· ≤ ·) σ τ ↔ σ < τ :=
  ⟨fun h => lt_of_le_of_ne h.1 fun hc => h.2 (hc ▸ le_rfl),
    fun h => ⟨le_of_lt h, not_le_of_gt h⟩⟩

/-- **The address a family of blocks is.** A program's configurations sit at
addresses it has to *build* from the blocks it means them to have, which is the
inverse of `DescriptiveComplexity.wmBlk`. -/
def mkAddr (p : Fin n → V → Prop) : Fin n × V → Prop := fun q => p q.1 q.2

omit [Finite V] in
@[simp]
theorem wmBlk_mkAddr (p : Fin n → V → Prop) : wmBlk (mkAddr p) = p := rfl

omit [Finite V] in
@[simp]
theorem mkAddr_wmBlk (s : Fin n × V → Prop) : mkAddr (wmBlk s) = s := rfl

/-- **An address is its family of blocks**, and nothing else. -/
def addrBlkEquiv : (Fin n × V → Prop) ≃ (Fin n → V → Prop) where
  toFun := wmBlk
  invFun := mkAddr
  left_inv := mkAddr_wmBlk
  right_inv := wmBlk_mkAddr

variable {s s' : Fin n × V → Prop} {τ : Fin n}

omit [Finite V] in
/-- **The blocks before the carry index agree**, which is what the fold asks above
the carry. -/
theorem blocks_agree_le (hbefore : ∀ σ, WMLt (α := Fin n) (· ≤ ·) σ τ → ∀ v,
      (wmBlk s' σ v ↔ wmBlk s σ v)) {j : ℕ} (hj : j < (τ : ℕ)) :
    ∀ i : Fin n, (i : ℕ) ≤ j → wmBlk s i = wmBlk s' i := by
  intro i hi
  refine funext fun v => propext (hbefore i ((wmLt_fin_iff i τ).mpr ?_) v).symm
  exact Fin.lt_def.mpr (by omega)

omit [Finite V] in
/-- The same, at the carry index itself: every strictly earlier block agrees. -/
theorem blocks_agree_lt (hbefore : ∀ σ, WMLt (α := Fin n) (· ≤ ·) σ τ → ∀ v,
      (wmBlk s' σ v ↔ wmBlk s σ v)) :
    ∀ i : Fin n, (i : ℕ) < (τ : ℕ) → wmBlk s i = wmBlk s' i := fun i hi =>
  funext fun v => propext (hbefore i ((wmLt_fin_iff i τ).mpr (Fin.lt_def.mpr hi)) v).symm

/-- **The blocks after the carry index are maximal before the step**: they are
full, and a full block is above every block. -/
theorem blocks_top_after (hV : IsLinOrd LeV)
    (hfull : ∀ σ, WMLt (α := Fin n) (· ≤ ·) τ σ → ∀ v, wmBlk s σ v) :
    ∀ i : Fin n, (τ : ℕ) < (i : ℕ) → ∀ a : V → Prop, WMSetLe LeV a (wmBlk s i) := fun i hi a =>
  wmSetLe_of_full hV (hfull i ((wmLt_fin_iff τ i).mpr (Fin.lt_def.mpr hi))) a

/-- **The blocks after the carry index are minimal after the step**: they have
been emptied, and an empty block is below every block. -/
theorem blocks_bot_after (hV : IsLinOrd LeV)
    (hafter : ∀ σ, WMLt (α := Fin n) (· ≤ ·) τ σ → ∀ v, ¬wmBlk s' σ v) :
    ∀ i : Fin n, (τ : ℕ) < (i : ℕ) → ∀ a : V → Prop, WMSetLe LeV (wmBlk s' i) a := fun i hi a =>
  wmSetLe_of_empty hV (hafter i ((wmLt_fin_iff τ i).mpr (Fin.lt_def.mpr hi))) a

/-- **At the carry index the new block is the successor of the old one**, which is
the successor hypothesis the fold asks for. -/
theorem blocks_succ_at (hV : IsLinOrd LeV) (hincr : WMIncr LeV (wmBlk s τ) (wmBlk s' τ)) :
    ∀ a : V → Prop, WMLt (WMSetLe LeV) a (wmBlk s' τ) ↔ WMSetLe LeV a (wmBlk s τ) := fun a =>
  (wmLt_wmSetLe_iff hV a _).trans (wmSetLt_iff_of_wmIncr hV hincr a)

/-! ### The fold rule of an address increment -/

variable {pol : ℕ → Bool} {P : (Fin n → (V → Prop)) → Prop}

/-- **The fold rule at the carry index of an address increment.** The accumulator
at the carry index absorbs the subtree the sweep has just finished – every deeper
block having been full – and takes in the accumulator one level down, which is the
new leaf. This is the step obligation of a one-pass program, with the address
layer and the fold joined. -/
theorem foldFrom_carry_of_wmIncr (hV : IsLinOrd LeV)
    (hfull : ∀ σ, WMLt (α := Fin n) (· ≤ ·) τ σ → ∀ v, wmBlk s σ v)
    (hincr : WMIncr LeV (wmBlk s τ) (wmBlk s' τ))
    (hbefore : ∀ σ, WMLt (α := Fin n) (· ≤ ·) σ τ → ∀ v, (wmBlk s' σ v ↔ wmBlk s σ v)) :
    (foldFrom pol P (WMSetLe LeV) (τ : ℕ) (wmBlk s') ↔
      (if pol (τ : ℕ) = true then
          foldFrom pol P (WMSetLe LeV) (τ : ℕ) (wmBlk s) ∨
            foldFrom pol P (WMSetLe LeV) ((τ : ℕ) + 1) (wmBlk s')
        else
          foldFrom pol P (WMSetLe LeV) (τ : ℕ) (wmBlk s) ∧
            foldFrom pol P (WMSetLe LeV) ((τ : ℕ) + 1) (wmBlk s'))) :=
  foldFrom_carry (isLinOrd_wmSetLe hV) τ.isLt (blocks_agree_lt hbefore)
    (blocks_top_after hV hfull) (blocks_succ_at hV hincr)

/-- **Below the carry index the accumulators reset to the new leaf**, the blocks
there having been emptied. -/
theorem foldFrom_below_of_wmIncr (hV : IsLinOrd LeV)
    (hafter : ∀ σ, WMLt (α := Fin n) (· ≤ ·) τ σ → ∀ v, ¬wmBlk s' σ v) {j : ℕ}
    (hj : (τ : ℕ) < j) : foldFrom pol P (WMSetLe LeV) j (wmBlk s') ↔ P (wmBlk s') :=
  foldFrom_below (c := (τ : ℕ)) (blocks_bot_after hV hafter) hj

omit [Finite V] in
/-- **Above the carry index only the deeper accumulator changes**, the blocks up to
there being untouched. -/
theorem foldFrom_above_of_wmIncr
    (hbefore : ∀ σ, WMLt (α := Fin n) (· ≤ ·) σ τ → ∀ v, (wmBlk s' σ v ↔ wmBlk s σ v))
    {j : ℕ} (hjn : j < n) (hj : j < (τ : ℕ)) :
    (foldFrom pol P (WMSetLe LeV) j (wmBlk s') ↔
      (if pol j = true then
          (∃ a : V → Prop, WMLt (WMSetLe LeV) a (wmBlk s ⟨j, hjn⟩) ∧
            altQuantFrom pol P (j + 1) (Function.update (wmBlk s) ⟨j, hjn⟩ a)) ∨
            foldFrom pol P (WMSetLe LeV) (j + 1) (wmBlk s')
        else
          (∀ a : V → Prop, WMLt (WMSetLe LeV) a (wmBlk s ⟨j, hjn⟩) →
            altQuantFrom pol P (j + 1) (Function.update (wmBlk s) ⟨j, hjn⟩ a)) ∧
            foldFrom pol P (WMSetLe LeV) (j + 1) (wmBlk s'))) :=
  foldFrom_above hjn (blocks_agree_le hbefore hj)

end Bridge

end DescriptiveComplexity
