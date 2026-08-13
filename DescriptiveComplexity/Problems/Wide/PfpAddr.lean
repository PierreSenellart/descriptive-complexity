/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSpec
import DescriptiveComplexity.Problems.Wide.PfpInner
import DescriptiveComplexity.Problems.Wide.PfpTable

/-!
# The argument blocks, concretely: outer arguments first, inner variables last

The EXPSPACE program keeps two families of argument blocks
(`DescriptiveComplexity.Pfp.PfpTag`'s `K`): the **outer**
ones hold the arguments of the fixed-point variable at the working cell, the
**inner** ones hold the valuations of the step formula's quantifier prefix,
enumerated by the VAL register. This file fixes `K := Fin ko ⊕ₗ Fin ki` and
proves the two facts the choice was made for:

* `DescriptiveComplexity.Pfp.kinSeg` – the inner tags are an **order embedding
  onto a final segment** of the whole tag order, which is what hands the inner
  loop its fold rules (`DescriptiveComplexity.Pfp.exists_carry_ix` and its
  consequences in `DescriptiveComplexity.Problems.Wide.PfpInner`);
* the **stage dictionary** – `DescriptiveComplexity.Pfp.trackOf`, the content of
  a stage track at an address: the stage of the fixed-point variable at the
  decoded outer blocks when they decode, `False` when they do not. It reads
  only the blocks below the variable's arity
  (`DescriptiveComplexity.Pfp.trackOf_of_blocks`), so a track may be read at
  any address with the right prefix – no canonical address, no gating – and
  the all-blank initial tape is exactly stage `0`
  (`DescriptiveComplexity.Pfp.trackOf_botAssign`).

`DescriptiveComplexity.Pfp.outAddr` builds the address a family of outer blocks
is, with every other block empty; it is what the working cell of the sweep
holds, and its non-argument blocks being empty is what puts it in the logical
interval (`DescriptiveComplexity.Pfp.wmSetLe_logicalTop`).
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language

/-! ### The two families of argument tags -/

section Tags

variable {R P : Type} {ko ki : ℕ}

/-- **An outer argument tag**: one block per argument of the fixed-point
variable. -/
def argOut (ki : ℕ) (k : Fin ko) : PfpTag R P (Fin ko ⊕ₗ Fin ki) :=
  .arg (Sum.inlₗ k)

/-- **An inner argument tag**: one block per variable of the quantifier
prefix. -/
def argIn (ko : ℕ) (j : Fin ki) : PfpTag R P (Fin ko ⊕ₗ Fin ki) :=
  .arg (Sum.inrₗ j)

theorem argOut_injective : Function.Injective (argOut (R := R) (P := P) (ko := ko) ki) := by
  intro k k' h
  simp only [argOut, PfpTag.arg.injEq] at h
  exact Sum.inl.inj (toLex.injective h)

variable [LinearOrder R] [LinearOrder P]

/-- The strict tag order through the key. -/
theorem lt_iff_tagKey {K : Type} [LinearOrder K] (σ τ : PfpTag R P K) :
    σ < τ ↔ tagKey σ < tagKey τ := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, le_iff_tagKey, le_iff_tagKey]

/-- Argument tags compare by their block index. -/
theorem arg_lt_arg_iff {K : Type} [LinearOrder K] (i i' : K) :
    (PfpTag.arg i : PfpTag R P K) < .arg i' ↔ i < i' := by
  rw [lt_iff_tagKey]
  simp [tagKey]

/-- **The inner tags are a final segment of the tag order**: strictly monotone,
and everything strictly above an inner tag is an inner tag – the non-argument
tags and the outer arguments all come first. This is the hypothesis pack of the
inner loop's fold rules. -/
theorem kinSeg :
    IxSeg (· ≤ · : PfpTag R P (Fin ko ⊕ₗ Fin ki) → PfpTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
      (argIn ko) := by
  constructor
  · intro j j'
    rw [wmLt_le_iff, argIn, argIn, arg_lt_arg_iff]
    exact Sum.Lex.inr_lt_inr_iff
  · intro j t hlt
    rw [wmLt_le_iff] at hlt
    match t with
    | .ctrl r => exact absurd hlt (asymm (lt_arg _ _ fun _ h => nomatch h))
    | .sym => exact absurd hlt (asymm (lt_arg _ _ fun _ h => nomatch h))
    | .phase p => exact absurd hlt (asymm (lt_arg _ _ fun _ h => nomatch h))
    | .arg i =>
      rcases h' : ofLex i with k | j'
      · have hi : i = Sum.inlₗ k := congrArg toLex h'
        subst hi
        refine absurd hlt (asymm ?_)
        rw [argIn, arg_lt_arg_iff]
        exact Sum.Lex.inl_lt_inr k j
      · have hi : i = Sum.inrₗ j' := congrArg toLex h'
        subst hi
        exact ⟨j', rfl⟩

end Tags

/-! ### The address a family of outer blocks is -/

section Addr

variable {A R P : Type} {ko ki : ℕ} {dd : ℕ}

/-- **The address holding given outer blocks and nothing else**: what the
working cell of the sweep is, its inner and non-argument blocks empty. -/
def outAddr (V : Fin ko → (Fin dd → A) → Prop) :
    Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop :=
  fun u => ∃ k : Fin ko, u.1 = argOut ki k ∧ V k u.2

/-- The outer blocks of `outAddr` are the given family. -/
theorem wmBlk_outAddr (V : Fin ko → (Fin dd → A) → Prop) (k : Fin ko) :
    wmBlk (outAddr (R := R) (P := P) (ki := ki) V) (argOut ki k) = V k := by
  refine funext fun v => propext ?_
  constructor
  · rintro ⟨k', hk', hv⟩
    rwa [argOut_injective hk'.symm] at hv
  · intro hv
    exact ⟨k, rfl, hv⟩

/-- Every other block of `outAddr` is empty. -/
theorem wmBlk_outAddr_of_ne (V : Fin ko → (Fin dd → A) → Prop)
    {t : PfpTag R P (Fin ko ⊕ₗ Fin ki)} (ht : ∀ k : Fin ko, t ≠ argOut ki k) :
    ∀ v : Fin dd → A, ¬wmBlk (outAddr V) t v := by
  rintro v ⟨k, hk, -⟩
  exact ht k hk

/-- The non-argument blocks of `outAddr` are empty, which is what puts the
working cell in the logical interval. -/
theorem outAddr_junk (V : Fin ko → (Fin dd → A) → Prop)
    {t : PfpTag R P (Fin ko ⊕ₗ Fin ki)} (ht : ∀ i, t ≠ PfpTag.arg i) :
    ∀ v : Fin dd → A, ¬outAddr V (t, v) := by
  rintro v ⟨k, hk, -⟩
  exact ht _ hk

end Addr

/-! ### The stage dictionary -/

section Stage

variable {R P : Type} {ko ki : ℕ} {dd : ℕ}
variable {L : Language.{0, 0}} {X : ExpExpansion L}
variable (ly : EncLayout (PtCode X) (blockArityBound X.B) dd)
variable {A : Type} [L.Structure A] [LinearOrder A] (zero one : A)
variable {d : StepDef (X.E.sum Language.order)}

/-- **The content of a stage track at an address**: the stage of the variable at
the decoded outer blocks when the blocks below its arity decode to points,
`False` when they do not. Only those blocks are read, so the track may be read
at any address with the right prefix, and the all-blank initial tape is exactly
stage `0`. -/
def trackOf {i : d.B.ι} (ha : d.B.arity i ≤ ko) (σ : d.B.Assignment (X.Map A))
    (s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) : Prop :=
  ∃ x : Fin (d.B.arity i) → X.Map A,
    (∀ ℓ : Fin (d.B.arity i),
      wmBlk s (argOut ki (Fin.castLE ha ℓ)) = encMap ly zero one (x ℓ)) ∧ σ i x

variable {ly zero one}

/-- **The dictionary reads back**: at an address whose relevant blocks encode a
tuple, the track holds the stage at that tuple. -/
theorem trackOf_of_blocks (hne : zero ≠ one) {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (σ : d.B.Assignment (X.Map A)) {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop}
    {x : Fin (d.B.arity i) → X.Map A}
    (hs : ∀ ℓ : Fin (d.B.arity i),
      wmBlk s (argOut ki (Fin.castLE ha ℓ)) = encMap ly zero one (x ℓ)) :
    trackOf ly zero one ha σ s ↔ σ i x := by
  constructor
  · rintro ⟨x', hx', hσ⟩
    have hxx : x' = x := funext fun ℓ =>
      encMap_injective ly hne ((hx' ℓ).symm.trans (hs ℓ))
    rwa [hxx] at hσ
  · intro hσ
    exact ⟨x, hs, hσ⟩

/-- **A track is empty at an address that encodes no tuple**: one block below
the variable's arity holding no point is enough, whatever the stage. This is
what the junk addresses of a sweep write, and it is why a program may leave
them alone. -/
theorem not_trackOf_of_notEnc {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (σ : d.B.Assignment (X.Map A))
    {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop} {ℓ₀ : Fin (d.B.arity i)}
    (hℓ : ∀ p : X.Map A,
      wmBlk s (argOut ki (Fin.castLE ha ℓ₀)) ≠ encMap ly zero one p) :
    ¬trackOf ly zero one ha σ s := by
  rintro ⟨x, hx, -⟩
  exact hℓ (x ℓ₀) (hx ℓ₀)

/-- **The empty stage writes an empty track**: at the bottom assignment nothing
holds, whatever the address – the all-blank initial tape is stage `0`. -/
theorem trackOf_botAssign {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) :
    ¬trackOf ly zero one ha (d.B.botAssign (X.Map A)) s := by
  rintro ⟨x, -, hσ⟩
  exact hσ

end Stage

end Pfp

end DescriptiveComplexity
