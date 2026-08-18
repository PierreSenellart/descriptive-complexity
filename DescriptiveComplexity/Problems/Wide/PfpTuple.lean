/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpChain

/-!
# The tuple loop: copying a block bit by bit

The stage atoms of the EXPSPACE program build their TARGET register by
copying a block of VAL or MIRROR into a block of TARGET, one bit per **named
cell**: a loop over the tuples the control enumerates in its loop-variable
slots, each round a read trip at the source cell, a write trip at the
destination cell, and an advance-or-exit dispatch.

This is the first client of the chain combinator
(`DescriptiveComplexity.Problems.Wide.PfpChain`): three checkpoints around
two stages – a `DescriptiveComplexity.Pfp.ReadKit` whose verdict exits store
the bit into the control, and a `DescriptiveComplexity.Pfp.WriteKit` whose
written bit reads it back – with the loop's back edge a plain descriptor
(the combinator's dispatches may target any phase). The loop-variable
updates (`initLv`, `advLv`) and the exhaustion guard (`IsMaxLv`) stay
parameters: their content – the lexicographic enumeration, tied to
`DescriptiveComplexity.Pfp.reflTransGen_of_tupLoop` – is fixed with the
runs.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The stage phases of a tuple loop**: the read trip's and the write
trip's. -/
abbrev TuplePS : Type := ReadPh ⊕ WritePh

/-- **The stage sites**: `false` the read trip, `true` the write trip. -/
abbrev TupleSS : Type := Bool

/-- **The stage shapes**: each kit's rules with its verdict exits. -/
def TupleSh : TupleSS → Type
  | false => ReadRule ⊕ Bool
  | true => WriteRule ⊕ Unit

/-- **The owner of each phase of a tuple loop.** -/
def tupleOwn : ChainPh 3 TuplePS → ChainSite 3 TupleSS
  | .chk k => .chk k
  | .sub (Sum.inl _) => .sub false
  | .sub (Sum.inr _) => .sub true

section Rules

variable {A Q W P : Type} [DecidableEq W]

variable (zero one : A) (wk rg : W)
variable (emb : ChainPh 3 TuplePS → P)
variable (tSrc tDst : W)
variable (MatchS MatchD : (Q → A) → (W → A) → Prop)
variable (bitFlag : (Q → A) → Prop)
variable (setBit : Bool → (Q → A) → (W → A) → (Q → A))
variable (initLv advLv : (Q → A) → (W → A) → (Q → A))
variable (IsMaxLv : (Q → A) → Prop)
variable (exitPh : P)

/-- **The stage rules**: the read kit with its bit-storing verdict exits,
the write kit with its return exit. -/
noncomputable def tupleStageRule :
    ∀ s : TupleSS, TupleSh s → Rule A Q W P
  | false, Sum.inl ρ =>
    (ReadKit.mk tSrc wk MatchS (fun rp => emb (.sub (Sum.inl rp)))).rule one ρ
  | false, Sum.inr b =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      srcPh := emb (.sub (Sum.inl (if b then .ry else .rn)))
      dstPh := emb (.chk 1)
      dstSt := setBit b
      wr := fun _ g => g
      moveRight := True }
  | true, Sum.inl ρ =>
    (WriteKit.mk tDst wk MatchD bitFlag
      (fun wp => emb (.sub (Sum.inr wp)))).rule zero one ρ
  | true, Sum.inr _ =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      srcPh := emb (.sub (Sum.inr .back))
      dstPh := emb (.chk 2)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }

/-- **The dispatch descriptors**: begin the first round (initializing the
loop variables), hand the stored bit to the write trip, and advance or
leave. -/
def tupleDsp : Fin 3 → Bool → PreRule A Q W P
  | ⟨0, _⟩, false =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      dstPh := emb (.sub (Sum.inl .start))
      dstSt := initLv
      wr := fun _ g => g
      moveRight := True }
  | ⟨0, _⟩, true =>
    { guard := fun _ _ => False
      dstPh := emb (.chk 0)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | ⟨1, _⟩, false =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      dstPh := emb (.sub (Sum.inr .start))
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | ⟨1, _⟩, true =>
    { guard := fun _ _ => False
      dstPh := emb (.chk 1)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | ⟨2, _⟩, false =>
    { guard := fun f g => (g wk = one ∧ g rg ≠ one) ∧ ¬IsMaxLv f
      dstPh := emb (.sub (Sum.inl .start))
      dstSt := advLv
      wr := fun _ g => g
      moveRight := True }
  | ⟨2, _⟩, true =>
    { guard := fun f g => (g wk = one ∧ g rg ≠ one) ∧ IsMaxLv f
      dstPh := exitPh
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }

/-- **The rules of a tuple loop**, assembled by the chain combinator. -/
noncomputable def tupleRule :
    ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → Rule A Q W P :=
  chainRule one wk emb
    (tupleStageRule (zero := zero) (one := one) (wk := wk) (rg := rg)
      (emb := emb) (tSrc := tSrc) (tDst := tDst) (MatchS := MatchS)
      (MatchD := MatchD) (bitFlag := bitFlag) (setBit := setBit))
    (tupleDsp (one := one) (wk := wk) (rg := rg) (emb := emb)
      (initLv := initLv) (advLv := advLv) (IsMaxLv := IsMaxLv)
      (exitPh := exitPh))

variable {emb}

/-- **Every rule of a tuple loop fires from a phase its site owns.** -/
theorem tupleHosrc :
    ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
      ∃ p : ChainPh 3 TuplePS,
        (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
          initLv advLv IsMaxLv exitPh i ρ).srcPh = emb p ∧ tupleOwn p = i :=
  chainHosrc id tupleOwn (fun _ => rfl)
    (fun s ρ => by
      match s, ρ with
      | false, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
      | false, Sum.inr b => cases b <;> exact ⟨_, rfl, rfl⟩
      | true, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
      | true, Sum.inr _ => exact ⟨_, rfl, rfl⟩)

/-- **A property of a tuple loop's phases and its exit holds of every phase it
can move to**: the two trips stay inside their own, the checkpoints stay where
they are, and only the last dispatch leaves. -/
theorem tupleRule_dstIn {S : P → Prop} (hemb : ∀ p : ChainPh 3 TuplePS, S (emb p))
    (hexit : S exitPh) (i : ChainSite 3 TupleSS)
    (ρ : ChainSh 3 TupleSS TupleSh i) :
    S (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
      initLv advLv IsMaxLv exitPh i ρ).dstPh := by
  refine chainRule_dstIn hemb (fun k b => ?_) (fun s ρ => ?_) i ρ
  · match k, b with
    | ⟨0, _⟩, false => exact hemb _
    | ⟨0, _⟩, true => exact hemb _
    | ⟨1, _⟩, false => exact hemb _
    | ⟨1, _⟩, true => exact hemb _
    | ⟨2, _⟩, false => exact hemb _
    | ⟨2, _⟩, true => exact hexit
  · match s, ρ with
    | false, Sum.inl σ =>
      obtain ⟨p, hp⟩ := (ReadKit.mk tSrc wk MatchS
        (fun rp => emb (.sub (Sum.inl rp)))).dstPh_emb one σ
      exact hp ▸ hemb _
    | false, Sum.inr b => exact hemb _
    | true, Sum.inl σ =>
      obtain ⟨p, hp⟩ := (WriteKit.mk tDst wk MatchD bitFlag
        (fun wp => emb (.sub (Sum.inr wp)))).dstPh_emb zero one σ
      exact hp ▸ hemb _
    | true, Sum.inr _ => exact hemb _

variable (hemb : Function.Injective emb)

include hemb in
/-- **A tuple loop separates in-shape.** -/
theorem tupleSep :
    ∀ (i : ChainSite 3 TupleSS) (ρ ρ' : ChainSh 3 TupleSS TupleSh i)
      (f : Q → A) (g : W → A),
      (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
        initLv advLv IsMaxLv exitPh i ρ).guard f g →
      (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
        initLv advLv IsMaxLv exitPh i ρ').guard f g →
      (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
        initLv advLv IsMaxLv exitPh i ρ).srcPh =
        (tupleRule zero one wk rg emb tSrc tDst MatchS MatchD bitFlag setBit
          initLv advLv IsMaxLv exitPh i ρ').srcPh →
      ρ = ρ' := by
  have hrd : Function.Injective (fun rp => emb (.sub (Sum.inl rp)) : ReadPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hwr : Function.Injective (fun wp => emb (.sub (Sum.inr wp)) : WritePh → P) :=
    fun x y h => by cases hemb h; rfl
  refine chainSep (fun k b f g hg => ?_) (fun k f g hc => ?_)
    (fun s ρ ρ' f g hg hg' hph => ?_)
  · match k, b with
    | ⟨0, _⟩, false => exact hg.1
    | ⟨0, _⟩, true => exact hg.elim
    | ⟨1, _⟩, false => exact hg.1
    | ⟨1, _⟩, true => exact hg.elim
    | ⟨2, _⟩, false => exact hg.1.1
    | ⟨2, _⟩, true => exact hg.1.1
  · match k with
    | ⟨0, _⟩ => exact hc.2.elim
    | ⟨1, _⟩ => exact hc.2.elim
    | ⟨2, _⟩ => exact hc.1.2 hc.2.2
  · match s, ρ, ρ' with
    | false, Sum.inl σ, Sum.inl σ' =>
      exact congrArg Sum.inl (ReadKit.sep _ one hrd σ σ' f g hg hg' hph)
    | false, Sum.inl σ, Sum.inr b =>
      refine absurd hph (fun hp => ReadKit.exit_disjoint _ one hrd σ f g hg
        hg'.1 ?_)
      cases b
      · exact Or.inr hp
      · exact Or.inl hp
    | false, Sum.inr b, Sum.inl σ =>
      refine absurd hph.symm (fun hp => ReadKit.exit_disjoint _ one hrd σ f g hg'
        hg.1 ?_)
      cases b
      · exact Or.inr hp
      · exact Or.inl hp
    | false, Sum.inr b, Sum.inr b' =>
      have hbb : b = b' := by
        have h2 := hemb hph
        injection h2 with h3
        injection h3 with h4
        cases b <;> cases b' <;> simp_all
      rw [hbb]
    | true, Sum.inl σ, Sum.inl σ' =>
      exact congrArg Sum.inl (WriteKit.sep _ zero one hwr σ σ' f g hg hg' hph)
    | true, Sum.inl σ, Sum.inr _ =>
      exact absurd hph (fun hp =>
        WriteKit.exit_disjoint _ zero one hwr σ f g hg hg'.1 hp)
    | true, Sum.inr _, Sum.inl σ =>
      exact absurd hph.symm (fun hp =>
        WriteKit.exit_disjoint _ zero one hwr σ f g hg' hg.1 hp)
    | true, Sum.inr _, Sum.inr _ => rfl

end Rules

end Pfp

end DescriptiveComplexity
