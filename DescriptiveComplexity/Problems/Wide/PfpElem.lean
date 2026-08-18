/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTuple

/-!
# The element loop: a sub-fold over control-held tuples

The remaining atom subroutines of the EXPSPACE program are all one shape:
enumerate a tuple of **elements** in the control's
loop-variable slots, per tuple run a fixed sequence of named single-bit
read trips – the `ρ`-bit leaves – and fold the leaf's value into the
sub-fold accumulators. The expansion atoms run it over the defining
sentence's prefix with one read per block atom of its matrix; a point
equality or order atom runs it over the coordinate tuples with two reads,
one per compared block; the domain gate runs it for `X.dom`.

The sites: an entry checkpoint (initializing the loop variables and
accumulators), the read trips chained head to tail – each verdict exit
stores its bit and enters the next – and a fold checkpoint whose advance
dispatch folds and re-enters the first read, its exhaustion dispatch folds
and leaves. The base-structure atoms of a leaf – `L`-atoms and order atoms
on the control-held elements – need no tape at all: a guard or a `dstSt`
is any function of the pointer, and the reduction, which writes the
transition table by formulas, may evaluate them there. As everywhere, the
semantic parameters stay abstract.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The phases of an element loop**: the entry checkpoint, the read
trips, the fold checkpoint. -/
inductive ElemPh (nr : ℕ) : Type
  /-- The entry checkpoint. -/
  | e0 : ElemPh nr
  /-- The `j`-th read trip of the current tuple. -/
  | rdP : Fin nr → ReadPh → ElemPh nr
  /-- The fold checkpoint. -/
  | e1 : ElemPh nr

/-- **The sites of an element loop.** -/
inductive ElemSite (nr : ℕ) : Type
  /-- The entry checkpoint. -/
  | e0 : ElemSite nr
  /-- A read trip. -/
  | rd : Fin nr → ElemSite nr
  /-- The fold checkpoint. -/
  | e1 : ElemSite nr

/-- **The rule shape of each site.** -/
def ElemSh (nr : ℕ) : ElemSite nr → Type
  | .e0 => EvalChkRule
  | .rd _ => ReadRule ⊕ Bool
  | .e1 => EvalChkRule

/-- **The owner of each phase of an element loop.** -/
def elemOwn {nr : ℕ} : ElemPh nr → ElemSite nr
  | .e0 => .e0
  | .rdP j _ => .rd j
  | .e1 => .e1

section Rules

variable {A Q W P : Type} {nr : ℕ}
variable (one : A) (wk rg : W)
variable (emb : ElemPh nr → P)
variable (rdTrack : Fin nr → W)
variable (MatchOf : Fin nr → (Q → A) → (W → A) → Prop)
variable (setFlag : Fin nr → Bool → (Q → A) → (W → A) → (Q → A))
variable (initEl advEl exitSt : (Q → A) → (W → A) → (Q → A))
variable (IsMaxEl : (Q → A) → Prop)
variable (exitPh : P)

/-- The first read's entry, or the fold checkpoint when there is no read. -/
def elemFirstRd : P :=
  if h : 0 < nr then emb (.rdP ⟨0, h⟩ .start) else emb .e1

/-- The phase after the `j`-th read. -/
def elemNextRd (j : Fin nr) : P :=
  if h : (j : ℕ) + 1 < nr then emb (.rdP ⟨(j : ℕ) + 1, h⟩ .start)
  else emb .e1

/-- **The rules of an element loop.** -/
def elemRule : ∀ i : ElemSite nr, ElemSh nr i → Rule A Q W P
  | .e0, .stay =>
    { guard := fun _ g => g wk ≠ one
      srcPh := emb .e0
      dstPh := emb .e0
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .e0, .dspA =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      srcPh := emb .e0
      dstPh := elemFirstRd emb
      dstSt := initEl
      wr := fun _ g => g
      moveRight := True }
  | .e0, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .e0
      dstPh := emb .e0
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .rd j, Sum.inl ρ =>
    (ReadKit.mk (rdTrack j) wk (MatchOf j)
      (fun rp => emb (.rdP j rp))).rule one ρ
  | .rd j, Sum.inr b =>
    { guard := fun _ g => g wk = one ∧ g rg ≠ one
      srcPh := emb (.rdP j (if b then .ry else .rn))
      dstPh := elemNextRd emb j
      dstSt := setFlag j b
      wr := fun _ g => g
      moveRight := True }
  | .e1, .stay =>
    { guard := fun _ g => g wk ≠ one
      srcPh := emb .e1
      dstPh := emb .e1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .e1, .dspA =>
    { guard := fun f g => (g wk = one ∧ g rg ≠ one) ∧ ¬IsMaxEl f
      srcPh := emb .e1
      dstPh := elemFirstRd emb
      dstSt := advEl
      wr := fun _ g => g
      moveRight := True }
  | .e1, .dspB =>
    { guard := fun f g => (g wk = one ∧ g rg ≠ one) ∧ IsMaxEl f
      srcPh := emb .e1
      dstPh := exitPh
      dstSt := exitSt
      wr := fun _ g => g
      moveRight := True }

variable {emb}

/-- **An element loop leaves only into its own phases or its exit**: the reads'
trips stay inside the loop's phases (`DescriptiveComplexity.Pfp.ReadKit.dstPh_emb`),
the dispatches land at the next read or the fold checkpoint, and the last one
leaves. This is what a caller reads off a stage to know the phases the machine
can be in. -/
theorem elemRule_dstPh (i : ElemSite nr) (ρ : ElemSh nr i) :
    (∃ p : ElemPh nr,
      (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt IsMaxEl
        exitPh i ρ).dstPh = emb p) ∨
    (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt IsMaxEl
      exitPh i ρ).dstPh = exitPh := by
  have hfirst : ∃ p : ElemPh nr, elemFirstRd emb = emb p := by
    by_cases h : 0 < nr
    · exact ⟨_, dif_pos h⟩
    · exact ⟨_, dif_neg h⟩
  have hnext : ∀ j : Fin nr, ∃ p : ElemPh nr, elemNextRd emb j = emb p := by
    intro j
    by_cases h : (j : ℕ) + 1 < nr
    · exact ⟨_, dif_pos h⟩
    · exact ⟨_, dif_neg h⟩
  match i, ρ with
  | .e0, .stay => exact Or.inl ⟨_, rfl⟩
  | .e0, .dspA => exact Or.inl hfirst
  | .e0, .dspB => exact Or.inl ⟨_, rfl⟩
  | .rd j, Sum.inl ρ' =>
    obtain ⟨p, hp⟩ := (ReadKit.mk (rdTrack j) wk (MatchOf j)
      (fun rp => emb (.rdP j rp))).dstPh_emb one ρ'
    exact Or.inl ⟨.rdP j p, hp⟩
  | .rd j, Sum.inr b => exact Or.inl (hnext j)
  | .e1, .stay => exact Or.inl ⟨_, rfl⟩
  | .e1, .dspA => exact Or.inl hfirst
  | .e1, .dspB => exact Or.inr rfl

/-- **A property of a loop's phases and its exit holds of every phase it can
move to.** This is the form a caller uses: give the property, check it of the
loop's own phases and of the exit, and every rule respects it. -/
theorem elemRule_dstIn {S : P → Prop} (hemb : ∀ p : ElemPh nr, S (emb p))
    (hexit : S exitPh) (i : ElemSite nr) (ρ : ElemSh nr i) :
    S (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt IsMaxEl
      exitPh i ρ).dstPh := by
  rcases elemRule_dstPh one wk rg rdTrack MatchOf setFlag initEl advEl exitSt
    IsMaxEl exitPh i ρ with ⟨p, hp⟩ | hp
  · rw [hp]; exact hemb p
  · rw [hp]; exact hexit

/-- **Every rule of an element loop fires from a phase its site owns.** -/
theorem elemHosrc :
    ∀ (i : ElemSite nr) (ρ : ElemSh nr i),
      ∃ p : ElemPh nr,
        (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt
          IsMaxEl exitPh i ρ).srcPh = emb p ∧ elemOwn p = i := by
  intro i ρ
  match i, ρ with
  | .e0, .stay => exact ⟨.e0, rfl, rfl⟩
  | .e0, .dspA => exact ⟨.e0, rfl, rfl⟩
  | .e0, .dspB => exact ⟨.e0, rfl, rfl⟩
  | .rd j, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .rd j, Sum.inr b => cases b <;> exact ⟨_, rfl, rfl⟩
  | .e1, .stay => exact ⟨.e1, rfl, rfl⟩
  | .e1, .dspA => exact ⟨.e1, rfl, rfl⟩
  | .e1, .dspB => exact ⟨.e1, rfl, rfl⟩

variable (hemb : Function.Injective emb)

include hemb in
/-- **An element loop separates in-shape.** -/
theorem elemSep :
    ∀ (i : ElemSite nr) (ρ ρ' : ElemSh nr i) (f : Q → A) (g : W → A),
      (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt
        IsMaxEl exitPh i ρ).guard f g →
      (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt
        IsMaxEl exitPh i ρ').guard f g →
      (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt
        IsMaxEl exitPh i ρ).srcPh =
        (elemRule one wk rg emb rdTrack MatchOf setFlag initEl advEl exitSt
          IsMaxEl exitPh i ρ').srcPh →
      ρ = ρ' := by
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .e0, .stay, .stay => rfl
  | .e0, .dspA, .dspA => rfl
  | .e0, .dspB, .dspB => rfl
  | .e0, .stay, .dspA => exact absurd hg'.1 hg
  | .e0, .dspA, .stay => exact absurd hg.1 hg'
  | .e0, .stay, .dspB => exact hg'.elim
  | .e0, .dspB, .stay => exact hg.elim
  | .e0, .dspA, .dspB => exact hg'.elim
  | .e0, .dspB, .dspA => exact hg.elim
  | .rd j, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ReadKit.sep _ one
      (fun x y h => by cases hemb h; rfl) σ σ' f g hg hg' hph)
  | .rd j, Sum.inl σ, Sum.inr b =>
    refine absurd hph (fun hp => ReadKit.exit_disjoint _ one
      (fun x y h => by cases hemb h; rfl) σ f g hg hg'.1 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .rd j, Sum.inr b, Sum.inl σ =>
    refine absurd hph.symm (fun hp => ReadKit.exit_disjoint _ one
      (fun x y h => by cases hemb h; rfl) σ f g hg' hg.1 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .rd j, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hemb hph
      injection h2 with h3 h4
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .e1, .stay, .stay => rfl
  | .e1, .dspA, .dspA => rfl
  | .e1, .dspB, .dspB => rfl
  | .e1, .stay, .dspA => exact absurd hg'.1.1 hg
  | .e1, .dspA, .stay => exact absurd hg.1.1 hg'
  | .e1, .stay, .dspB => exact absurd hg'.1.1 hg
  | .e1, .dspB, .stay => exact absurd hg.1.1 hg'
  | .e1, .dspA, .dspB => exact absurd hg'.2 hg.2
  | .e1, .dspB, .dspA => exact absurd hg.2 hg'.2

end Rules

end Pfp

end DescriptiveComplexity
