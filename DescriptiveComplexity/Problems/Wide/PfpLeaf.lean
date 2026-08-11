/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpData
import DescriptiveComplexity.Problems.Wide.PfpPad

/-!
# What the inner loop computes

The VAL register of the EXPSPACE program enumerates addresses supported on
the **inner** argument blocks, from the empty one to the full one, and the
control folds one leaf per address. This file says what that fold is worth:
at the inner top it **is** one step of the iteration at the points the
working address holds.

The dictionary, fixed here once and for all:

* level `j` of a variable's pack is inner block `j` of the register – the
  free levels included, although the machine reads *those* off the working
  address's outer blocks (`DescriptiveComplexity.Pfp.PfpData.levelVal`);
* the leaf is the **gated matrix** of
  `DescriptiveComplexity.Problems.Wide.PfpRel` at that valuation
  (`DescriptiveComplexity.Pfp.PfpData.leafP`), so the encodings' gates are
  part of the leaf and not of the loop.

`DescriptiveComplexity.Pfp.PfpData.altQuantFrom_leafP` is the join: the
prefix of the leaf predicate over *all* `ki` blocks, from level `0`, is
`DescriptiveComplexity.StepDef.next` at the encoded arguments. The two ends
of the mismatch are paid for by
`DescriptiveComplexity.Problems.Wide.PfpPad` – the free levels and the
levels past the pack are skipped, the starting valuation is never read at
level `0` – and the middle by
`DescriptiveComplexity.Pfp.StepDef.next_iff_gateMat`.
`foldFrom_leafP_top` then reads it off the accumulators, at the address the
loop stops at.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A : Type}
variable [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable [LinearOrder (dt.X.Map A)]

/-! ### The leaf predicate -/

variable (zero one : A)

/-- **The valuation the levels of a pack read**: the working address's outer
blocks below the variable's arity – those are the arguments the stage is
being computed at – and the register's inner blocks above it. -/
noncomputable def levelVal (v : dt.VarIx)
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (w : Fin dt.ki → (Fin dt.dd → A) → Prop) :
    Fin (dt.nOf v) → (Fin dt.dd → A) → Prop :=
  fun j => if h : (j : ℕ) < dt.arOf v then mb ⟨(j : ℕ), lt_of_lt_of_le h (dt.arOf_le_ko v)⟩
    else w ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki v)⟩

/-- The same valuation over the pack's own levels: the free ones off the
working address, the quantified ones as given. -/
noncomputable def freeVal (v : dt.VarIx)
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (u : Fin (dt.nOf v) → (Fin dt.dd → A) → Prop) :
    Fin (dt.nOf v) → (Fin dt.dd → A) → Prop :=
  fun j => if h : (j : ℕ) < dt.arOf v then mb ⟨(j : ℕ), lt_of_lt_of_le h (dt.arOf_le_ko v)⟩
    else u j

/-- **The matrix of a variable's pack**, read over points at a stage. -/
noncomputable def matHolds (v : dt.VarIx) (σ : dt.d.B.Assignment (dt.X.Map A)) :
    (Fin (dt.nOf v) → dt.X.Map A) → Prop := fun u =>
  @BoundedFormula.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) _ _ (dt.matOf v) default u

/-- **The gated matrix over block values**: the encodings' gates, then the
matrix at the decoded points – the leaf of the relativized prefix. -/
noncomputable def gateHolds (v : dt.VarIx) (σ : dt.d.B.Assignment (dt.X.Map A)) :
    (Fin (dt.nOf v) → ((Fin dt.dd → A) → Prop)) → Prop :=
  gateMat (encMap dt.ly zero one) (IsEnc dt.ly zero one) (dt.polOf v) (dt.matHolds v σ)

/-- **The leaf the machine folds**, one per address of the VAL register: the
gated matrix at the levels' values. -/
noncomputable def leafP (v : dt.VarIx) (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop) :
    (Fin dt.ki → ((Fin dt.dd → A) → Prop)) → Prop :=
  fun w => dt.gateHolds zero one v σ (dt.levelVal v mb w)

variable {dt zero one}

/-- The leaf is the pack-level predicate padded to the register's blocks. -/
theorem leafP_eq_pad (v : dt.VarIx) (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (w : Fin dt.ki → ((Fin dt.dd → A) → Prop)) :
    dt.leafP zero one v σ mb w =
      (fun u : Fin (dt.nOf v) → ((Fin dt.dd → A) → Prop) =>
        dt.gateHolds zero one v σ (dt.freeVal v mb u))
        (fun j : Fin (dt.nOf v) => w (Fin.castLE (dt.nOf_le_ki v) j)) := rfl

/-- The leaf ignores the register blocks the pack does not quantify: those
below the variable's arity, whose values it reads off the working address,
and those past its prefix, which nothing reads. -/
theorem leafP_irrel (v : dt.VarIx) (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop) {ℓ : Fin dt.ki}
    (hℓ : (ℓ : ℕ) < dt.arOf v ∨ dt.nOf v ≤ (ℓ : ℕ))
    (w : Fin dt.ki → ((Fin dt.dd → A) → Prop)) (a : (Fin dt.dd → A) → Prop) :
    dt.leafP zero one v σ mb (Function.update w ℓ a) ↔ dt.leafP zero one v σ mb w := by
  refine iff_of_eq (congrArg (dt.gateHolds zero one v σ) (funext fun j => ?_))
  rw [levelVal, levelVal]
  by_cases h : (j : ℕ) < dt.arOf v
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    refine Function.update_of_ne (fun hc => ?_) _ _
    have hval : (j : ℕ) = (ℓ : ℕ) := congrArg Fin.val hc
    have := j.isLt
    rcases hℓ with hℓ | hℓ <;> omega

/-! ### The join -/

/-- **The inner loop computes the step formula.** The prefix of the leaf
predicate over *every* block of the register, played from level `0`, is one
step of the iteration at the points the working address's outer blocks
encode – whatever the register held when the loop began, since level `0`
reads nothing.

The three mismatches between what the machine plays and what the pack asks
for are exactly the three lemmas of
`DescriptiveComplexity.Problems.Wide.PfpPad`: the free levels are skipped,
the levels past the prefix are padding, and below the prefix's start the
machine's leaf reads the working address where the pack reads its
valuation. -/
theorem altQuantFrom_leafP (hzo : zero ≠ one) (i : dt.d.B.ι)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (x : Fin (dt.d.B.arity i) → dt.X.Map A)
    (hx : ∀ ℓ : Fin (dt.d.B.arity i),
      mb (Fin.castLE (dt.arOf_le_ko (some i)) ℓ) = encMap dt.ly zero one (x ℓ))
    (w : Fin dt.ki → ((Fin dt.dd → A) → Prop)) :
    altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb) 0 w ↔
      dt.d.next σ i x := by
  classical
  -- the starting valuation is not read at level `0`, so put the arguments in it
  set wA : Fin dt.ki → ((Fin dt.dd → A) → Prop) := fun ℓ =>
    if h : (ℓ : ℕ) < dt.arOf (some i) then
      mb ⟨(ℓ : ℕ), lt_of_lt_of_le h (dt.arOf_le_ko (some i))⟩ else w ℓ
    with hwA
  have h0 : altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb) 0 w =
      altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb) 0 wA :=
    altQuantFrom_congr_val _ _ fun j hj => absurd hj (Nat.not_lt_zero _)
  -- the free levels are played but not read
  have h1 : altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb) 0 wA ↔
      altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb)
        (dt.arOf (some i)) wA :=
    altQuantFrom_skip (Nat.zero_le _)
      (fun ℓ _ h2 => leafP_irrel (some i) σ mb (Or.inl h2)) wA
  -- the levels past the prefix are padding
  have h2 : altQuantFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb)
        (dt.arOf (some i)) wA ↔
      altQuantFrom (dt.polOf (some i))
        (fun u : Fin (dt.nOf (some i)) → ((Fin dt.dd → A) → Prop) =>
          dt.gateHolds zero one (some i) σ (dt.freeVal (some i) mb u)) (dt.arOf (some i))
        (fun j : Fin (dt.nOf (some i)) => wA (Fin.castLE (dt.nOf_le_ki (some i)) j)) := by
    have hfun : dt.leafP zero one (some i) σ mb =
        fun w' : Fin dt.ki → ((Fin dt.dd → A) → Prop) =>
          (fun u : Fin (dt.nOf (some i)) → ((Fin dt.dd → A) → Prop) =>
            dt.gateHolds zero one (some i) σ (dt.freeVal (some i) mb u))
            (fun j : Fin (dt.nOf (some i)) => w' (Fin.castLE (dt.nOf_le_ki (some i)) j)) :=
      funext fun w' => leafP_eq_pad (some i) σ mb w'
    rw [hfun]
    exact altQuantFrom_pad (P := fun u : Fin (dt.nOf (some i)) → ((Fin dt.dd → A) → Prop) =>
      dt.gateHolds zero one (some i) σ (dt.freeVal (some i) mb u))
      (dt.nOf_le_ki (some i)) (dt.arOf_le_nOf (some i)) wA
  -- below the prefix's start the two matrices agree
  have hV : ∀ (j : Fin (dt.nOf (some i))) (hj : (j : ℕ) < dt.arOf (some i)),
      wA (Fin.castLE (dt.nOf_le_ki (some i)) j) =
        mb ⟨(j : ℕ), lt_of_lt_of_le hj (dt.arOf_le_ko (some i))⟩ := by
    intro j hj
    rw [hwA]
    exact dif_pos hj
  have h3 : altQuantFrom (dt.polOf (some i))
        (fun u : Fin (dt.nOf (some i)) → ((Fin dt.dd → A) → Prop) =>
          dt.gateHolds zero one (some i) σ (dt.freeVal (some i) mb u)) (dt.arOf (some i))
        (fun j : Fin (dt.nOf (some i)) => wA (Fin.castLE (dt.nOf_le_ki (some i)) j)) ↔
      altQuantFrom (dt.polOf (some i)) (dt.gateHolds zero one (some i) σ) (dt.arOf (some i))
        (fun j : Fin (dt.nOf (some i)) => wA (Fin.castLE (dt.nOf_le_ki (some i)) j)) := by
    refine altQuantFrom_congr_mat fun u hu => ?_
    refine iff_of_eq (congrArg (dt.gateHolds zero one (some i) σ) (funext fun j => ?_))
    rw [freeVal]
    by_cases h : (j : ℕ) < dt.arOf (some i)
    · rw [dif_pos h, hu j h, hV j h]
    · rw [dif_neg h]
  -- the pack's own statement
  have h4 := StepDef.next_iff_gateMat (ly := dt.ly) (zero := zero) (one := one) hzo
    (pk := dt.pk i) σ x
    (V := fun j : Fin (dt.nOf (some i)) => wA (Fin.castLE (dt.nOf_le_ki (some i)) j))
    (fun ℓ => by
      have hcast : ((Fin.castLE (dt.pk i).kLe ℓ : Fin (dt.nOf (some i))) : ℕ) <
          dt.arOf (some i) := ℓ.isLt
      rw [hV _ hcast, ← hx ℓ]
      rfl)
  rw [h0]
  exact (h1.trans (h2.trans h3)).trans h4.symm

/-! ### Read off the accumulators -/

variable {R' P' : Type}

/-- **At the inner top the fold holds the step's value.** The loop stops when
every inner block of the register is full; there the accumulator at level `0`
is the whole prefix (`DescriptiveComplexity.Pfp.foldFrom_top_of_ix`), hence
one step of the iteration at the working address's points. -/
theorem foldFrom_leafP_top (hzo : zero ≠ one)
    {LeV : (Fin dt.dd → A) → (Fin dt.dd → A) → Prop} (hLeV : IsLinOrd LeV)
    (i : dt.d.B.ι) (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (x : Fin (dt.d.B.arity i) → dt.X.Map A)
    (hx : ∀ ℓ : Fin (dt.d.B.arity i),
      mb (Fin.castLE (dt.arOf_le_ko (some i)) ℓ) = encMap dt.ly zero one (x ℓ))
    {s : Univ A R' P' dt.KIx dt.dd → Prop}
    (hfull : ∀ (j : Fin dt.ki) (v : Fin dt.dd → A),
      wmBlk s (argIn (R := R') (P := P') dt.ko j) v) :
    (foldFrom (dt.polOf (some i)) (dt.leafP zero one (some i) σ mb) (WMSetLe LeV) 0
        (ixBlk (argIn dt.ko) s) ↔ dt.d.next σ i x) :=
  (foldFrom_top_of_ix hLeV hfull).trans
    (altQuantFrom_leafP hzo i σ mb x hx (ixBlk (argIn dt.ko) s))

end PfpData

end Pfp

end DescriptiveComplexity
