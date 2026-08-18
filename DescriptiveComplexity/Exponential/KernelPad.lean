/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Kernel

/-!
# Padding a kernel's block

A machine written against a `DescriptiveComplexity.NexKernel` pays for its run
out of the drawing's own size, and the drawing's size is a count of *tags* – one
per rule name, and a rule name of the guessing site carries an assignment of the
guessed block. So a kernel with few relation variables draws a small machine and
buys a short clock, while what the run costs is set by the machine's *tape*,
which the block does not shrink.

The remedy is to pad: give the block extra relation variables that the kernel
never mentions. It says the same thing – an existential block whose extra
variables do not occur is satisfied exactly when the original is – and it
multiplies the guessing site's rule names by `2 ^ (number of extra variables)`.

This file is that padding: the block (`SOBlock.pad`), the language morphism that
reads a kernel over it (`blockPadLHom`), the two directions of the transport
(`realize_blockPad`), and the kernel-level statement
(`NexKernel.pad_holds`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Pad

variable {L : Language.{0, 0}}

/-- **A block with `n` more relation variables**, each of arity `a`, which no
kernel of the original block mentions. -/
def SOBlock.pad (B : SOBlock) (n a : ℕ) : SOBlock where
  ι := B.ι ⊕ Fin n
  arity := Sum.elim B.arity fun _ => a

@[simp]
theorem SOBlock.pad_arity_inl (B : SOBlock) (n a : ℕ) (i : B.ι) :
    (B.pad n a).arity (Sum.inl i) = B.arity i := rfl

/-- **The variables of a padded block**, counted: the original's and the new
ones. This is what a clock's counting hypothesis is discharged by – the guessing
site's rule names are indexed by assignments of the block. -/
theorem SOBlock.card_pad_ι (B : SOBlock) (n a : ℕ) :
    Nat.card (B.pad n a).ι = Nat.card B.ι + n := by
  classical
  haveI : Fintype B.ι := Fintype.ofFinite _
  simp [SOBlock.pad, Nat.card_eq_fintype_card]

/-- **What a padded block's assignment says about the original's**: forget the
new variables. -/
def SOBlock.unpadAssign (B : SOBlock) {n a : ℕ} {M : Type}
    (ρ : (B.pad n a).Assignment M) : B.Assignment M :=
  fun i => ρ (Sum.inl i)

/-- **And back**: the new variables empty. -/
def SOBlock.padAssign (B : SOBlock) (n a : ℕ) {M : Type} (ρ : B.Assignment M) :
    (B.pad n a).Assignment M :=
  Sum.rec ρ fun _ _ => False

@[simp]
theorem SOBlock.unpadAssign_padAssign (B : SOBlock) (n a : ℕ) {M : Type}
    (ρ : B.Assignment M) : B.unpadAssign (B.padAssign n a ρ) = ρ := rfl

/-- **The language morphism reading a kernel of the block over the padded
one**: every symbol goes to itself, and the new relation symbols are simply not
in the image. -/
def blockPadLHom (L : Language.{0, 0}) (B : SOBlock) (n a : ℕ) :
    L.sum B.lang →ᴸ L.sum (B.pad n a).lang where
  onFunction {_m} f :=
    match f with
    | Sum.inl g => Sum.inl g
    | Sum.inr g => nomatch g
  onRelation {_m} r :=
    match r with
    | Sum.inl s => Sum.inl s
    | Sum.inr s => Sum.inr ⟨Sum.inl s.1, s.2⟩

/-- **The padded structure is an expansion along it**: the new symbols are the
only ones added, and no formula in the image mentions them. -/
theorem blockPadLHom_isExpansionOn (L : Language.{0, 0}) (B : SOBlock) (n a : ℕ)
    (M : Type) (instM : L.Structure M) (ρ : (B.pad n a).Assignment M) :
    @LHom.IsExpansionOn _ _ (blockPadLHom L B n a) M
      (@sumStructure L B.lang M instM (B.structure (B.unpadAssign ρ)))
      (@sumStructure L (B.pad n a).lang M instM ((B.pad n a).structure ρ)) := by
  letI := instM
  letI := B.structure (B.unpadAssign ρ)
  letI := (B.pad n a).structure ρ
  exact
    { map_onFunction := fun {_m} f _x => by
        match f with
        | Sum.inl g => rfl
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {_m} r _x => by
        match r with
        | Sum.inl s => rfl
        | Sum.inr s => rfl }

/-- **Padding the block changes no meaning**: a kernel of the original block,
read over the padded one, says of a padded assignment what it said of the
assignment's own part. -/
theorem realize_blockPad (B : SOBlock) (n a : ℕ) (M : Type) [instM : L.Structure M]
    (ρ : (B.pad n a).Assignment M) (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize (L.sum (B.pad n a).lang) M
        (@sumStructure L (B.pad n a).lang M instM ((B.pad n a).structure ρ))
        ((blockPadLHom L B n a).onSentence φ) ↔
      @Sentence.Realize (L.sum B.lang) M
        (@sumStructure L B.lang M instM (B.structure (B.unpadAssign ρ))) φ :=
  @LHom.realize_onSentence _ _ M
    (@sumStructure L B.lang M instM (B.structure (B.unpadAssign ρ)))
    (@sumStructure L (B.pad n a).lang M instM ((B.pad n a).structure ρ))
    (blockPadLHom L B n a) (blockPadLHom_isExpansionOn L B n a M instM ρ) φ

end Pad

/-! ### The padded kernel -/

section KernelPad

variable {L : Language.{0, 0}}

/-- **A kernel with a padded block**: the same expansion, the same sentence read
over more relation variables. -/
def NexKernel.pad (K : NexKernel L) (n a : ℕ) : NexKernel L where
  X := K.X
  B := K.B.pad n a
  ker := (blockPadLHom (K.X.E.sum Language.order) K.B n a).onSentence K.ker

@[simp]
theorem NexKernel.pad_X (K : NexKernel L) (n a : ℕ) : (K.pad n a).X = K.X := rfl

@[simp]
theorem NexKernel.pad_B (K : NexKernel L) (n a : ℕ) :
    (K.pad n a).B = K.B.pad n a := rfl

/-- **A padded kernel says what the kernel said.** The extra variables occur in
no atom, so an assignment satisfying the padded kernel restricts to one
satisfying the kernel, and one satisfying the kernel extends – by the empty
relation – to one satisfying the padded kernel. -/
theorem NexKernel.pad_holds (K : NexKernel L) (n a : ℕ) {M : Type}
    [instM : K.X.E.Structure M] [instO : LinearOrder M] :
    @NexKernel.Holds L (K.pad n a) M instM instO ↔ K.Holds M := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨K.B.unpadAssign ρ,
      (realize_blockPad (L := K.X.E.sum Language.order) K.B n a M ρ K.ker).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨K.B.padAssign n a ρ, ?_⟩
    refine (realize_blockPad (L := K.X.E.sum Language.order) K.B n a M
      (K.B.padAssign n a ρ) K.ker).mpr ?_
    exact hρ

end KernelPad

end DescriptiveComplexity
