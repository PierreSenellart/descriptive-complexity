/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Bridge
import DescriptiveComplexity.OrderWalk

/-!
# The fold on a final segment of the blocks

`DescriptiveComplexity.Problems.Wide.Bridge` joins the fold to the address
increment when the block index type is the whole of `Fin n`. The inner loop of
the EXPSPACE program is not like that: its register enumerates the valuations
of the step formula's quantifier prefix, which live in the **last** `q` blocks
of the address – the `Kin` half of the argument tags – while every other block
of the register stays empty. So the join is restated here for an arbitrary
family of block indices `ι : Fin q → T`, assumed to be an *order embedding onto
a final segment* of the tag order:

* the embedding hypotheses are `DescriptiveComplexity.Draw.IxSeg`;
* `DescriptiveComplexity.Draw.exists_carry_ix` – an increment of the address
  whose image blocks are not all full has its carry **inside** the image (every
  tag after an image tag is an image tag, so the last non-full block cannot
  escape), and decomposes there;
* `DescriptiveComplexity.Draw.foldFrom_carry_of_ix` /
  `foldFrom_above_of_ix` / `foldFrom_below_of_ix` – the three fold rules, at
  the family `DescriptiveComplexity.Draw.ixBlk` of image blocks;
* `DescriptiveComplexity.Draw.foldFrom_bot_of_ix` /
  `foldFrom_top_of_ix` – the two ends: empty image blocks start the sweep at
  the matrix, full ones finish it at the whole prefix.

Everything is about the product order `DescriptiveComplexity.lexRel` on
`T × V`; joining it to the machine's own order is the instance's `le` field, as
everywhere in the layer.
-/

namespace DescriptiveComplexity

namespace Draw

section Inner

variable {T V : Type} {LeT : T → T → Prop} {LeV : V → V → Prop} {q : ℕ}

/-- **A final segment of the blocks**: an order embedding of `Fin q` into the
tags whose image is upward closed – every tag strictly above an image tag is an
image tag. The `Kin` half of the argument tags is one. -/
structure IxSeg (LeT : T → T → Prop) (ι : Fin q → T) : Prop where
  /-- The embedding is strictly monotone, in both directions. -/
  mono : ∀ j j' : Fin q, WMLt LeT (ι j) (ι j') ↔ j < j'
  /-- The image is a final segment of the tag order. -/
  final : ∀ (j : Fin q) (t : T), WMLt LeT (ι j) t → ∃ j' : Fin q, t = ι j'

/-- **The image blocks of an address**, as a valuation of the fold. -/
def ixBlk (ι : Fin q → T) (s : T × V → Prop) : Fin q → V → Prop := fun j => wmBlk s (ι j)

variable {ι : Fin q → T} {s s' : T × V → Prop}

/-- **The carry of an increment stays in a final segment whose blocks are not
all full**: the carry tag is the last tag with a non-full block, every tag
above an image tag is an image tag, and some image block is non-full – so the
carry decomposition of `DescriptiveComplexity.wmIncr_lexRel_iff` happens at an
image tag. -/
theorem exists_carry_ix (hT : IsLinOrd LeT) (hseg : IxSeg LeT ι)
    (hincr : WMIncr (lexRel LeT LeV) s s')
    (hne : ∃ (j : Fin q) (v : V), ¬wmBlk s (ι j) v) :
    ∃ c : Fin q,
      (∀ σ : T, WMLt LeT σ (ι c) → ∀ v : V, (wmBlk s' σ v ↔ wmBlk s σ v)) ∧
      WMIncr LeV (wmBlk s (ι c)) (wmBlk s' (ι c)) ∧
      (∀ σ : T, WMLt LeT (ι c) σ → ∀ v : V, wmBlk s σ v) ∧
      (∀ σ : T, WMLt LeT (ι c) σ → ∀ v : V, ¬wmBlk s' σ v) := by
  obtain ⟨τ, hfull, hstep, hbefore, hafter⟩ := (wmIncr_lexRel_iff hT s s').mp hincr
  obtain ⟨j, v, hv⟩ := hne
  have himg : ∃ c : Fin q, τ = ι c := by
    by_cases hlt : WMLt LeT (ι j) τ
    · exact hseg.final j τ hlt
    · refine ⟨j, ?_⟩
      by_cases hlt' : WMLt LeT τ (ι j)
      · exact absurd (hfull (ι j) hlt' v) hv
      · exact eq_of_not_wmLt hT hlt' hlt
  obtain ⟨c, rfl⟩ := himg
  exact ⟨c, hbefore, hstep, hfull, hafter⟩

/-! ### The fold rules at the image blocks -/

variable {pol : ℕ → Bool} {P : (Fin q → (V → Prop)) → Prop} [Finite V]

/-- **The fold rule at the carry index**, when the carry tag is the `c`-th image
tag: the accumulator there absorbs the finished subtree and takes in the deeper
accumulator, exactly as over a full block index type. -/
theorem foldFrom_carry_of_ix (hV : IsLinOrd LeV) (hseg : IxSeg LeT ι) {c : Fin q}
    (hbefore : ∀ σ : T, WMLt LeT σ (ι c) → ∀ v : V, (wmBlk s' σ v ↔ wmBlk s σ v))
    (hstep : WMIncr LeV (wmBlk s (ι c)) (wmBlk s' (ι c)))
    (hfull : ∀ σ : T, WMLt LeT (ι c) σ → ∀ v : V, wmBlk s σ v) :
    (foldFrom pol P (WMSetLe LeV) (c : ℕ) (ixBlk ι s') ↔
      (if pol (c : ℕ) = true then
          foldFrom pol P (WMSetLe LeV) (c : ℕ) (ixBlk ι s) ∨
            foldFrom pol P (WMSetLe LeV) ((c : ℕ) + 1) (ixBlk ι s')
        else
          foldFrom pol P (WMSetLe LeV) (c : ℕ) (ixBlk ι s) ∧
            foldFrom pol P (WMSetLe LeV) ((c : ℕ) + 1) (ixBlk ι s'))) := by
  refine foldFrom_carry (isLinOrd_wmSetLe hV) c.isLt (fun i hi => ?_) (fun i hi a => ?_) ?_
  · exact funext fun v =>
      propext (hbefore (ι i) ((hseg.mono i c).mpr (Fin.lt_def.mpr hi)) v).symm
  · exact wmSetLe_of_full hV (hfull (ι i) ((hseg.mono c i).mpr (Fin.lt_def.mpr hi))) a
  · exact fun a => (wmLt_wmSetLe_iff hV a _).trans (wmSetLt_iff_of_wmIncr hV hstep a)

/-- **Below the carry index the accumulators reset to the new leaf**: the image
blocks there have been emptied. -/
theorem foldFrom_below_of_ix (hV : IsLinOrd LeV) (hseg : IxSeg LeT ι) {c : Fin q}
    (hafter : ∀ σ : T, WMLt LeT (ι c) σ → ∀ v : V, ¬wmBlk s' σ v) {j : ℕ}
    (hj : (c : ℕ) < j) : foldFrom pol P (WMSetLe LeV) j (ixBlk ι s') ↔ P (ixBlk ι s') :=
  foldFrom_below (c := (c : ℕ))
    (fun i hi a => wmSetLe_of_empty hV
      (hafter (ι i) ((hseg.mono c i).mpr (Fin.lt_def.mpr hi))) a) hj

omit [Finite V] in
/-- **Above the carry index only the deeper accumulator changes**: the image
blocks up to the level are untouched by the increment. -/
theorem foldFrom_above_of_ix (hseg : IxSeg LeT ι) {c : Fin q}
    (hbefore : ∀ σ : T, WMLt LeT σ (ι c) → ∀ v : V, (wmBlk s' σ v ↔ wmBlk s σ v))
    {j : ℕ} (hjq : j < q) (hj : j < (c : ℕ)) :
    (foldFrom pol P (WMSetLe LeV) j (ixBlk ι s') ↔
      (if pol j = true then
          (∃ a : V → Prop, WMLt (WMSetLe LeV) a (ixBlk ι s ⟨j, hjq⟩) ∧
            altQuantFrom pol P (j + 1) (Function.update (ixBlk ι s) ⟨j, hjq⟩ a)) ∨
            foldFrom pol P (WMSetLe LeV) (j + 1) (ixBlk ι s')
        else
          (∀ a : V → Prop, WMLt (WMSetLe LeV) a (ixBlk ι s ⟨j, hjq⟩) →
            altQuantFrom pol P (j + 1) (Function.update (ixBlk ι s) ⟨j, hjq⟩ a)) ∧
            foldFrom pol P (WMSetLe LeV) (j + 1) (ixBlk ι s'))) := by
  refine foldFrom_above hjq fun i hi => ?_
  refine funext fun v => propext (hbefore (ι i) ((hseg.mono i c).mpr ?_) v).symm
  exact Fin.lt_def.mpr (by omega)

/-! ### The two ends of the enumeration -/

/-- **Empty image blocks start the sweep at the matrix**: nothing has been
accumulated yet. -/
theorem foldFrom_bot_of_ix (hV : IsLinOrd LeV)
    (hempty : ∀ (j : Fin q) (v : V), ¬wmBlk s (ι j) v) {j : ℕ} :
    foldFrom pol P (WMSetLe LeV) j (ixBlk ι s) ↔ P (ixBlk ι s) :=
  foldFrom_bot (j₀ := 0) (fun i _ a => wmSetLe_of_empty hV (hempty i) a) (Nat.zero_le j)

/-- **Full image blocks finish the sweep at the whole prefix**: every leaf has
been seen. -/
theorem foldFrom_top_of_ix (hV : IsLinOrd LeV)
    (hfull : ∀ (j : Fin q) (v : V), wmBlk s (ι j) v) {j : ℕ} :
    foldFrom pol P (WMSetLe LeV) j (ixBlk ι s) ↔ altQuantFrom pol P j (ixBlk ι s) :=
  foldFrom_top (j₀ := 0) (isLinOrd_wmSetLe hV)
    (fun i _ a => wmSetLe_of_full hV (hfull i) a) (Nat.zero_le j)

end Inner

/-! ### The fold along a tuple loop

The element loops of the atom subroutines enumerate tuples of *source
elements* in the control, stepping by the lexicographic successor
`DescriptiveComplexity.TupSucc` – whose components are exactly the hypotheses
of the fold's three step rules, at value type the source structure itself.
These are the control-scale twins of the rules above; the two ends need no
twin, `DescriptiveComplexity.foldFrom_bot` / `foldFrom_top` apply as they
stand at an all-minimal / all-maximal tuple. -/

section TupLoop

variable {A : Type} [LinearOrder A] {e : ℕ} {pol : ℕ → Bool} {P : (Fin e → A) → Prop}

/-- The strict form of the order relation the fold reads is the strict
order. -/
theorem wmLt_le_iff {a b : A} : WMLt (· ≤ ·) a b ↔ a < b :=
  ⟨fun h => lt_of_le_not_ge h.1 h.2, fun h => ⟨le_of_lt h, not_le_of_gt h⟩⟩

variable {v v' : Fin e → A} {c : Fin e}

end TupLoop

end Draw

end DescriptiveComplexity
