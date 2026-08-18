/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSpec
import DescriptiveComplexity.Problems.Wide.DrawInner
import DescriptiveComplexity.Problems.Wide.DrawTable

/-!
# The argument blocks, concretely: outer arguments first, inner variables last

The EXPSPACE program keeps two families of argument blocks
(`DescriptiveComplexity.Draw.DrawTag`'s `K`): the **outer**
ones hold the arguments of the fixed-point variable at the working cell, the
**inner** ones hold the valuations of the step formula's quantifier prefix,
enumerated by the VAL register. This file fixes `K := Fin ko ⊕ₗ Fin ki` and
proves the two facts the choice was made for:

* `DescriptiveComplexity.Draw.kinSeg` – the inner tags are an **order embedding
  onto a final segment** of the whole tag order, which is what hands the inner
  loop its fold rules (`DescriptiveComplexity.Draw.exists_carry_ix` and its
  consequences in `DescriptiveComplexity.Problems.Wide.DrawInner`);
* the **stage dictionary** – `DescriptiveComplexity.Draw.trackOf`, the content of
  a stage track at an address: the stage of the fixed-point variable at the
  decoded outer blocks when they decode, `False` when they do not. It reads
  only the blocks below the variable's arity
  (`DescriptiveComplexity.Draw.trackOf_of_blocks`), so a track may be read at
  any address with the right prefix – no canonical address, no gating – and
  the all-blank initial tape is exactly stage `0`
  (`DescriptiveComplexity.Draw.trackOf_botAssign`).

`DescriptiveComplexity.Draw.outAddr` builds the address a family of outer blocks
is, with every other block empty; it is what the working cell of the sweep
holds, and its non-argument blocks being empty is what puts it in the logical
interval (`DescriptiveComplexity.Draw.wmSetLe_logicalTop`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

/-! ### The two families of argument tags -/

section Tags

variable {R P : Type} {ko ki : ℕ}

/-- **An outer argument tag**: one block per argument of the fixed-point
variable. -/
def argOut (ki : ℕ) (k : Fin ko) : DrawTag R P (Fin ko ⊕ₗ Fin ki) :=
  .arg (Sum.inlₗ k)

/-- **An inner argument tag**: one block per variable of the quantifier
prefix. -/
def argIn (ko : ℕ) (j : Fin ki) : DrawTag R P (Fin ko ⊕ₗ Fin ki) :=
  .arg (Sum.inrₗ j)

theorem argOut_injective : Function.Injective (argOut (R := R) (P := P) (ko := ko) ki) := by
  intro k k' h
  simp only [argOut, DrawTag.arg.injEq] at h
  exact Sum.inl.inj (toLex.injective h)

variable [LinearOrder R] [LinearOrder P]

/-- The strict tag order through the key. -/
theorem lt_iff_tagKey {K : Type} [LinearOrder K] (σ τ : DrawTag R P K) :
    σ < τ ↔ tagKey σ < tagKey τ := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, le_iff_tagKey, le_iff_tagKey]

/-- Argument tags compare by their block index. -/
theorem arg_lt_arg_iff {K : Type} [LinearOrder K] (i i' : K) :
    (DrawTag.arg i : DrawTag R P K) < .arg i' ↔ i < i' := by
  rw [lt_iff_tagKey]
  simp [tagKey]

/-- **The inner tags are a final segment of the tag order**: strictly monotone,
and everything strictly above an inner tag is an inner tag – the non-argument
tags and the outer arguments all come first. This is the hypothesis pack of the
inner loop's fold rules. -/
theorem kinSeg :
    IxSeg (· ≤ · : DrawTag R P (Fin ko ⊕ₗ Fin ki) → DrawTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
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

/-- **An address that marks outer argument blocks alone is `outAddr` of its
blocks.** This is the uniqueness that turns a reading of the blocks into a
reading of the address, and with it a set of marked addresses into a stage. -/
theorem outAddr_of_blocks {V : Fin ko → (Fin dd → A) → Prop}
    {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop}
    (hblk : ∀ k : Fin ko, wmBlk s (argOut ki k) = V k)
    (hsupp : ∀ u, s u → ∃ k : Fin ko, u.1 = argOut ki k) :
    s = outAddr (R := R) (P := P) (ki := ki) V := by
  funext u
  refine propext ⟨fun hu => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hsupp u hu
    refine ⟨k, hk, ?_⟩
    have hu' : wmBlk s (argOut ki k) u.2 := by
      rw [← hk]
      exact hu
    rw [hblk k] at hu'
    exact hu'
  · rintro ⟨k, hk, hv⟩
    have hv' : wmBlk s (argOut ki k) u.2 := by
      rw [hblk k]
      exact hv
    rw [← hk] at hv'
    exact hv'

/-- Every other block of `outAddr` is empty. -/
theorem wmBlk_outAddr_of_ne (V : Fin ko → (Fin dd → A) → Prop)
    {t : DrawTag R P (Fin ko ⊕ₗ Fin ki)} (ht : ∀ k : Fin ko, t ≠ argOut ki k) :
    ∀ v : Fin dd → A, ¬wmBlk (outAddr V) t v := by
  rintro v ⟨k, hk, -⟩
  exact ht k hk

/-- The non-argument blocks of `outAddr` are empty, which is what puts the
working cell in the logical interval. -/
theorem outAddr_junk (V : Fin ko → (Fin dd → A) → Prop)
    {t : DrawTag R P (Fin ko ⊕ₗ Fin ki)} (ht : ∀ i, t ≠ DrawTag.arg i) :
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

/-- **A track marks no empty address**: a variable of positive arity has a
block below its arity encoding a point, and an encoding always holds its tag's
own tuple, so an address the track marks has an element in that block. This is
what puts a dictionary entry inside a clocked program's *guessed* stretch, whose
bottom is the file's first register and not the empty address. -/
theorem nonempty_of_trackOf {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    {σ : d.B.Assignment (X.Map A)}
    {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop} (ℓ₀ : Fin (d.B.arity i))
    (h : trackOf ly zero one ha σ s) : ∃ y, s y := by
  obtain ⟨x, hx, -⟩ := h
  have hmem : encMap ly zero one (x ℓ₀)
      (encTagTup ly zero one (x ℓ₀).1.1) := Or.inl rfl
  rw [← hx ℓ₀] at hmem
  exact ⟨_, hmem⟩

variable (ly zero one) in
/-- **The address of a tuple of points**: its outer blocks are the tuple's
encodings, everything else empty — where the dictionary of a variable at that
tuple is read. -/
def tupAddr {i : d.B.ι} (_ha : d.B.arity i ≤ ko)
    (x : Fin (d.B.arity i) → X.Map A) :
    Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop :=
  outAddr fun k =>
    if h : (k : ℕ) < d.B.arity i then encMap ly zero one (x ⟨(k : ℕ), h⟩)
    else fun _ => False

/-- Its blocks below the variable's arity are the tuple's encodings. -/
theorem wmBlk_tupAddr {ly : EncLayout (PtCode X) (blockArityBound X.B) dd}
    {zero one : A} {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (x : Fin (d.B.arity i) → X.Map A) (ℓ : Fin (d.B.arity i)) :
    wmBlk (tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x)
        (argOut ki (Fin.castLE ha ℓ)) = encMap ly zero one (x ℓ) := by
  rw [tupAddr, wmBlk_outAddr]
  exact dif_pos ℓ.isLt

/-- **An address whose blocks below the arity are the encodings, and which
marks nothing else, *is* the tuple's address.** The addresses a stage atom
builds are of that kind – written block by block from named registers – so the
dictionary a backward reading needs is asked exactly where
`trackOf_assignOfTrack` answers it. -/
theorem tupAddr_of_blocks {ly : EncLayout (PtCode X) (blockArityBound X.B) dd}
    {zero one : A} {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop}
    {x : Fin (d.B.arity i) → X.Map A}
    (hblk : ∀ ℓ : Fin (d.B.arity i),
      wmBlk s (argOut ki (Fin.castLE ha ℓ)) = encMap ly zero one (x ℓ))
    (hbeyond : ∀ k : Fin ko, d.B.arity i ≤ (k : ℕ) →
      ∀ v : Fin dd → A, ¬wmBlk s (argOut ki k) v)
    (hsupp : ∀ u, s u → ∃ k : Fin ko, u.1 = argOut ki k) :
    s = tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x := by
  refine (outAddr_of_blocks (fun k => ?_) hsupp).trans rfl
  by_cases hk : (k : ℕ) < d.B.arity i
  · rw [dif_pos hk]
    have hcast : k = Fin.castLE ha ⟨(k : ℕ), hk⟩ := Fin.ext rfl
    exact (congrArg (fun k' => wmBlk s (argOut ki k')) hcast).trans
      (hblk ⟨(k : ℕ), hk⟩)
  · rw [dif_neg hk]
    exact funext fun v =>
      propext ⟨fun hv => (hbeyond k (not_lt.mp hk) v hv).elim, False.elim⟩

variable (ly zero one) in
/-- **The assignment a track carries**: a tuple is in the relation exactly when
the address that names it is marked. This is the inverse the forward direction
never needs – it *writes* `trackOf` of an assignment – and the one a backward
reading is built on. -/
def assignOfTrack (ha : ∀ i : d.B.ι, d.B.arity i ≤ ko)
    (T : d.B.ι → (Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) → Prop) :
    d.B.Assignment (X.Map A) :=
  fun i x => T i (tupAddr (R := R) (P := P) (ki := ki) ly zero one (ha i) x)

/-- **And it reads back**: at the address a tuple names, the track of the
assignment a track carries is that track. So a run that left an arbitrary set
of addresses marked has left the stage of a definite assignment, as far as the
evaluation ever looks. -/
theorem trackOf_assignOfTrack (hne : zero ≠ one)
    (ha : ∀ i : d.B.ι, d.B.arity i ≤ ko)
    (T : d.B.ι → (Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) → Prop)
    {i : d.B.ι} (x : Fin (d.B.arity i) → X.Map A) :
    trackOf (R := R) (P := P) (ki := ki) ly zero one (ha i)
        (assignOfTrack (R := R) (P := P) (ki := ki) ly zero one ha T)
        (tupAddr (R := R) (P := P) (ki := ki) ly zero one (ha i) x) ↔
      T i (tupAddr (R := R) (P := P) (ki := ki) ly zero one (ha i) x) :=
  trackOf_of_blocks hne (ha i) _ (fun ℓ => wmBlk_tupAddr (ha i) x ℓ)

/-- **A tuple's address lies in the logical interval**: its non-argument
blocks are empty, which is exactly `wmSetLe_logicalTop`'s hypothesis. What is
*not* automatic is that it lies strictly below the top — the reduction owes
that where it plants the end marker. -/
theorem wmSetLe_tupAddr_logicalTop [LinearOrder R] [LinearOrder P]
    [Finite R] [Finite P] [Finite A]
    (hV : IsLinOrd (tupLeLex (A := A) (d := dd)))
    {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (x : Fin (d.B.arity i) → X.Map A) :
    WMSetLe (lexRel (· ≤ · : DrawTag R P (Fin ko ⊕ₗ Fin ki) →
        DrawTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
      (tupLeLex (A := A) (d := dd)))
      (tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x) logicalTop :=
  wmSetLe_logicalTop hV (fun _ ht v => outAddr_junk _ ht v)

/-- **A tuple's address is strictly below the logical top**: the top's blocks
are full, and an encoding is not (`not_encPt_zeroTup`). One position of the
tuple is enough; at a nullary variable the address is the empty one, which is
strictly below any nonempty top. -/
theorem wmSetLt_tupAddr_logicalTop [LinearOrder R] [LinearOrder P]
    [Finite R] [Finite P] [Finite A] (hne : zero ≠ one)
    (hV : IsLinOrd (tupLeLex (A := A) (d := dd)))
    {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (x : Fin (d.B.arity i) → X.Map A) (ℓ : Fin (d.B.arity i)) :
    WMSetLt (lexRel (· ≤ · : DrawTag R P (Fin ko ⊕ₗ Fin ki) →
        DrawTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
      (tupLeLex (A := A) (d := dd)))
      (tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x) logicalTop := by
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_tupAddr_logicalTop hV ha x, fun hc => ?_⟩
  have hcell : tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x
      (DrawTag.arg (Sum.inlₗ (Fin.castLE ha ℓ)), fun _ => zero) := by
    rw [hc]
    exact logicalTop_arg _ _
  obtain ⟨k, hk, hv⟩ := hcell
  rw [argOut_injective (P := P) (R := R) hk.symm] at hv
  rw [dif_pos (show ((Fin.castLE ha ℓ : Fin ko) : ℕ) < d.B.arity i from ℓ.isLt)]
    at hv
  exact not_encPt_zeroTup ly hne (x ℓ).1 hv

/-- **A padded address of argument cells alone is strictly below the logical
top**: it is at or below it because its non-argument blocks are empty
(`wmSetLe_logicalTop`), and it is not the top itself because the top's blocks
are *full* — they hold the cells whose coordinates beyond the payload are not
`zero`, and a padded address holds none of those. This is what an address a
program *builds* out of padded cells (rather than reads from a register) has
to offer, and it needs one coordinate of slack (`c < dd`) and one argument
block to name (`i`) — the same nonemptiness the interval is given anyway. -/
theorem wmSetLt_logicalTop_of_isPad [LinearOrder R] [LinearOrder P]
    [Finite R] [Finite P] [Finite A] {c : ℕ} {zero one : A} (hne : zero ≠ one)
    (hV : IsLinOrd (tupLeLex (A := A) (d := dd))) (hc : c < dd)
    (i : Fin ko ⊕ₗ Fin ki)
    {s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop}
    (hjunk : ∀ τ : DrawTag R P (Fin ko ⊕ₗ Fin ki),
      (∀ i : Fin ko ⊕ₗ Fin ki, τ ≠ DrawTag.arg i) → ∀ v : Fin dd → A, ¬s (τ, v))
    (hpad : ∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, s y → IsPad c zero y.2) :
    WMSetLt (lexRel (· ≤ · : DrawTag R P (Fin ko ⊕ₗ Fin ki) →
        DrawTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
      (tupLeLex (A := A) (d := dd)))
      s logicalTop := by
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_logicalTop hV hjunk, fun heq => ?_⟩
  have hcell : s (DrawTag.arg i, fun _ => one) := by
    rw [heq]
    exact logicalTop_arg _ _
  exact hne (hpad _ hcell ⟨c, hc⟩ le_rfl).symm

/-- **A tuple's address is strictly below the logical top, at every arity**:
`wmSetLt_tupAddr_logicalTop` at a variable of arity ≥ 1, and at a **nullary**
one the address is the empty one, which is strictly below any nonempty top —
so what the nullary case asks for is an argument block to name, the same
nonemptiness of the interval the run layer is given anyway. This is the form
`assignment_ext_of_trackOf`'s `hS` is discharged in. -/
theorem wmSetLt_tupAddr_logicalTop' [LinearOrder R] [LinearOrder P]
    [Finite R] [Finite P] [Finite A] (hne : zero ≠ one)
    (hV : IsLinOrd (tupLeLex (A := A) (d := dd))) (i₀ : Fin ko ⊕ₗ Fin ki)
    {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (x : Fin (d.B.arity i) → X.Map A) :
    WMSetLt (lexRel (· ≤ · : DrawTag R P (Fin ko ⊕ₗ Fin ki) →
        DrawTag R P (Fin ko ⊕ₗ Fin ki) → Prop)
      (tupLeLex (A := A) (d := dd)))
      (tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x) logicalTop := by
  rcases Nat.eq_zero_or_pos (d.B.arity i) with h0 | hpos
  · refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_tupAddr_logicalTop hV ha x, fun heq => ?_⟩
    have hcell : tupAddr ly zero one (R := R) (P := P) (ki := ki) ha x
        (DrawTag.arg i₀, fun _ => zero) := by
      rw [heq]
      exact logicalTop_arg _ _
    obtain ⟨k, -, hv⟩ := hcell
    rw [dif_neg (by omega : ¬((k : ℕ) < d.B.arity i))] at hv
    exact hv
  · exact wmSetLt_tupAddr_logicalTop hne hV ha x ⟨0, hpos⟩

/-- **The dictionary determines the stage**: two assignments whose tracks agree
at every address of a family that carries every tuple's own address are equal.
This is what turns the machine's convergence test — the tracks of one stage and
the next agreeing over the logical interval — back into «the stages are
equal», which is what `hnotconv` needs. -/
theorem assignment_ext_of_trackOf (hne : zero ≠ one)
    (ha : ∀ i : d.B.ι, d.B.arity i ≤ ko)
    {σ σ' : d.B.Assignment (X.Map A)}
    (S : (Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) → Prop)
    (hS : ∀ (i : d.B.ι) (x : Fin (d.B.arity i) → X.Map A),
      S (tupAddr ly zero one (ha i) x))
    (hagree : ∀ s, S s → ∀ i : d.B.ι,
      (trackOf ly zero one (ha i) σ s ↔ trackOf ly zero one (ha i) σ' s)) :
    σ = σ' := by
  funext i x
  refine propext ?_
  have hb := wmBlk_tupAddr (R := R) (P := P) (ki := ki) (ly := ly)
    (zero := zero) (one := one) (ha i) x
  exact ((trackOf_of_blocks hne (ha i) σ hb).symm.trans
    (hagree _ (hS i x) i)).trans (trackOf_of_blocks hne (ha i) σ' hb)

/-- **The empty stage writes an empty track**: at the bottom assignment nothing
holds, whatever the address – the all-blank initial tape is stage `0`. -/
theorem trackOf_botAssign {i : d.B.ι} (ha : d.B.arity i ≤ ko)
    (s : Univ A R P (Fin ko ⊕ₗ Fin ki) dd → Prop) :
    ¬trackOf ly zero one ha (d.B.botAssign (X.Map A)) s := by
  rintro ⟨x, -, hσ⟩
  exact hσ

end Stage

end Draw

end DescriptiveComplexity
