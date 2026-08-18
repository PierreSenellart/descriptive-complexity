/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.SecondOrderOrdered

/-!
# What a NEXPTIME source problem looks like

`DescriptiveComplexity.ExpDefinable` `DescriptiveComplexity.NP` is the class the
hardness proof for `DescriptiveComplexity.WideAccept` starts from, and it is
stated as an existential over an expansion and a *problem* of `NP`. A machine
cannot be programmed against that. This file puts it in the normal form a program
is written against:

> **an expansion, one block of guessed relation variables, and a first-order
> kernel** – `DescriptiveComplexity.NexKernel` – the problem holding at a
> structure exactly when some assignment of the block satisfies the kernel over
> its expansion.

That is the same shape as the data of the EXPSPACE program – an expansion, a
block, a first-order body – with the block's relation variables **guessed** once
rather than iterated to a fixed point, which is the whole difference between the
two programs.

## The order

The kernel is stated over `L.sum FirstOrder.Language.order`, one language wider
than `DescriptiveComplexity.SigmaSODefinable` supplies. Nothing is added by that:
a machine has an order on its universe whatever the source says, the atoms of an
ordered kernel are what the program's atom machinery is written for, and a
sentence that mentions no order symbol is a sentence that may. The transport is
`DescriptiveComplexity.orderAddLHom`, the dual of
`DescriptiveComplexity.orderElimLHom` – which eliminates an order symbol by
re-quantifying it inside a block, and is the direction that costs something.

Which linear order is on the expanded universe is left to the consumer: the
normal form holds at **every** one, so a reduction may choose the order its
encoding induces and pay nothing for the choice.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Adding an order symbol to a kernel -/

section AddOrder

variable {L : Language.{0, 0}}

/-- **The language morphism adding an order symbol** to a first-order kernel
over a block: every symbol goes to itself, and the order symbol of the target is
simply not in the image. The dual of
`DescriptiveComplexity.orderElimLHom`. -/
def orderAddLHom (L : Language.{0, 0}) (B : SOBlock) :
    L.sum B.lang →ᴸ (L.sum Language.order).sum B.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => nomatch g
  onRelation {_n} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s => Sum.inr s

/-- **The ordered structure is an expansion along the morphism**, whatever the
order: the order symbol is the only new one and no formula in the image mentions
it. -/
theorem orderAddLHom_isExpansionOn (L : Language.{0, 0}) (B : SOBlock) (A : Type)
    (instA : L.Structure A) (lo : LinearOrder A) (ρ : B.Assignment A) :
    @LHom.IsExpansionOn _ _ (orderAddLHom L B) A
      (@sumStructure L B.lang A instA (B.structure ρ))
      (@sumStructure (L.sum Language.order) B.lang A
        (letI := instA; letI := lo; sumOrderStructure L A) (B.structure ρ)) := by
  let := instA
  let := lo
  let := B.structure ρ
  exact
    { map_onFunction := fun {_n} f _x => by
        match f with
        | Sum.inl g => rfl
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {_n} r _x => by
        match r with
        | Sum.inl s => rfl
        | Sum.inr s => rfl }

/-- **Adding the order symbol changes no meaning.** -/
theorem realize_orderAdd (B : SOBlock) (A : Type) [instA : L.Structure A] [lo : LinearOrder A]
    (ρ : B.Assignment A) (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure (L.sum Language.order) B.lang A (sumOrderStructure L A) (B.structure ρ))
        ((orderAddLHom L B).onSentence φ) ↔
      @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A instA (B.structure ρ)) φ :=
  @LHom.realize_onSentence _ _ A (@sumStructure L B.lang A instA (B.structure ρ))
    (@sumStructure (L.sum Language.order) B.lang A (sumOrderStructure L A) (B.structure ρ))
    (orderAddLHom L B) (orderAddLHom_isExpansionOn L B A instA lo ρ) φ

/-- **A `Σ₁` definition, with its kernel read over the ordered expansion.** The
one block is the certificate the machine guesses; the kernel is what it checks;
and the statement holds at every linear order, so a consumer may impose its
own. -/
theorem exists_orderedKernel [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSODefinable 1 P) :
    ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ ∃ ρ : B.Assignment A, @Sentence.Realize _ A
          (@sumStructure (L.sum Language.order) B.lang A (sumOrderStructure L A)
            (B.structure ρ)) φ := by
  obtain ⟨Bs, hlen, φ, hspec⟩ := h
  match Bs, hlen with
  | [B], _ =>
    refine ⟨B, (orderAddLHom L B).onSentence φ, fun A _ _ _ _ => (hspec A).trans ?_⟩
    -- Satisfaction of a single existential block unfolds definitionally.
    exact exists_congr fun ρ => (realize_orderAdd B A ρ φ).symm

end AddOrder

/-! ### The normal form of a NEXPTIME source -/

section Kernel

variable {L : Language.{0, 0}}

/-- **The data a NEXPTIME hardness program is written against**: an exponential
expansion, one block of guessed relation variables, and a first-order kernel over
the expanded vocabulary, its order, and the block. -/
structure NexKernel (L : Language.{0, 0}) : Type 1 where
  /-- The exponential expansion whose points the machine's tape addresses. -/
  X : ExpExpansion L
  /-- The relation variables the machine guesses. -/
  B : SOBlock
  /-- The first-order sentence the machine checks. -/
  ker : ((X.E.sum Language.order).sum B.lang).Sentence

namespace NexKernel

variable (K : NexKernel L)

/-- **What the kernel says**: some assignment of the guessed block satisfies it.
This is the predicate the machine's run has to be equivalent to – guess, then
check – and it is stated at an arbitrary linear order on the universe, the
reduction's own being one. -/
def Holds (M : Type) [instM : K.X.E.Structure M] [LinearOrder M] : Prop :=
  ∃ ρ : K.B.Assignment M, @Sentence.Realize _ M
    (@sumStructure (K.X.E.sum Language.order) K.B.lang M
      (sumOrderStructure K.X.E M) (K.B.structure ρ)) K.ker

end NexKernel

/-- **Every NEXPTIME source problem has a kernel.** Unfold
`DescriptiveComplexity.ExpDefinable` `DescriptiveComplexity.NP` into an
expansion and a `Σ₁` problem over it, then the `Σ₁` problem into a block and a
kernel: what is left is *guess an assignment over the expanded universe and check
a first-order sentence*, which is what a program can be written for.

The equivalence is stated at every linear order on the expanded universe, so the
reduction that consumes it is free to impose the order its encoding induces
(compare `DescriptiveComplexity.Draw.encOrder`). -/
theorem exists_nexKernel [L.IsRelational] {P : DecisionProblem L}
    (h : ExpDefinable NP P) :
    ∃ K : NexKernel L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
      [LinearOrder (K.X.Map A)], P A ↔ K.Holds (K.X.Map A) := by
  obtain ⟨X, Q, hQ, hspec⟩ := h
  obtain ⟨B, φ, hker⟩ := exists_orderedKernel (P := Q) hQ
  refine ⟨⟨X, B, φ⟩, fun A _ _ _ _ _ => ?_⟩
  have := X.mapFinite A
  have := X.mapNonempty A
  exact (hspec A).trans (hker (X.Map A))

end Kernel

end DescriptiveComplexity
