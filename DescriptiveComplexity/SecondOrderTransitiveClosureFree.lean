/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.PSpace
import DescriptiveComplexity.SecondOrderOrdered

/-!
# SO(TC) needs no order: the order is a guessed state component

`DescriptiveComplexity.SOTCDefinable`, like the clausal fragments and the
reachability logics, reads its three sentences over the *ordered* expansion of
the vocabulary and asks for the equivalence at every linear order on the
universe. For SO(TC) that hypothesis is removable, and this file removes it.

The reason it is removable here and not for SO-Horn, SO-Krom, FO(TC) or
FO(DTC) is the reason Fagin's theorem needs no order either: a walk over
assignments of a block can **guess** the order and carry it along. A state of
the walk is an assignment of relation variables, so one more binary variable
holds a candidate order; the source condition checks that it is a linear one
(`DescriptiveComplexity.linearGuard`), the transition condition says it does
not change, and every sentence of the original specification reads it in place
of the order symbol (`DescriptiveComplexity.orderElimLHom` and its two-copy
analogue below). The order is then a *component of the certificate*, exactly as
it is in the first block of a `Σₖ₊₁` sentence
(`DescriptiveComplexity.SecondOrderOrdered`), and nothing outside the
specification sees it.

A deterministic fragment cannot do this – guessing is what the Horn and Krom
kernels do not have, and their capture theorems are genuinely statements about
ordered structures – so `DescriptiveComplexity.PTIME`,
`DescriptiveComplexity.NL` and `DescriptiveComplexity.LOGSPACE` keep the
hypothesis while `DescriptiveComplexity.PSPACE` loses it.

## What this file contains

* `DescriptiveComplexity.SOTCSpecFree`, an SO(TC) specification whose three
  sentences live over the bare vocabulary expanded by copies of the block, with
  its semantics: acceptance is defined on structures carrying **no order at
  all**.
* `DescriptiveComplexity.SOTCSpecFree.toSpec`, reading such a specification as
  an ordinary one (the order symbol is simply never used), and
  `DescriptiveComplexity.SOTCSpecFree.accepts_toSpec_iff`.
* `DescriptiveComplexity.SOTCSpec.orderFree`, the converse construction: the
  order is guessed into the state, guarded at the source and frozen by every
  step (`DescriptiveComplexity.SOTCSpec.orderFree_accepts_iff`).
* `DescriptiveComplexity.SOTCDefinableFree` and the equivalence
  `DescriptiveComplexity.sotcDefinable_iff_free`, whence
  `DescriptiveComplexity.mem_PSPACE_iff_sotcDefinableFree`: membership in
  `PSPACE` is definability by an order-free specification.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Order-free specifications -/

/-- An SO(TC) specification that does **not** see a linear order: as in
`DescriptiveComplexity.SOTCSpec`, the states of the walk are the assignments of
a block, but the three sentences live over the bare vocabulary expanded by
copies of the block, with no order symbol available. -/
structure SOTCSpecFree (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : ((L.sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : (L.sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : (L.sum B.lang).Sentence

namespace SOTCSpecFree

section Semantics

variable (spec : SOTCSpecFree L) {A : Type} [L.Structure A]

variable (A) in
/-- A state of the walk: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- One step of the walk: the transition sentence, read with the current state
in the first copy of the block and the next state in the second. -/
def Step (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₂ (L := L) ρ σ) spec.step

/-- Reachability in the walk: the reflexive-transitive closure of
`DescriptiveComplexity.SOTCSpecFree.Step`. -/
abbrev Reach : spec.State A → spec.State A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A state is a starting state when it satisfies the source sentence. -/
def IsSrc (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L) ρ) spec.src

/-- A state is accepting when it satisfies the target sentence. -/
def IsTgt (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L) ρ) spec.tgt

variable (A) in
/-- The structure is accepted: some accepting state is reachable from some
starting state. No order on `A` is involved. -/
def Accepts : Prop :=
  ∃ ρ σ : spec.State A, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ spec.Reach ρ σ

end Semantics

end SOTCSpecFree

/-! ### Reading an order-free specification as an ordinary one

The easy direction: a specification that does not mention the order is one that
happens never to use it. The language morphism below adds the order symbol to
the vocabulary, and the two structures agree on everything else. -/

section AddOrder

variable (L) (B : SOBlock)

/-- Adding the order to the vocabulary, over one copy of a block. -/
def addOrderOne : (L.sum B.lang) →ᴸ ((L.sum Language.order).sum B.lang) where
  onFunction {_n} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => isEmptyElim g
  onRelation {_n} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s => Sum.inr s

/-- Adding the order to the vocabulary, over two copies of a block. -/
def addOrderTwo :
    ((L.sum B.lang).sum B.lang) →ᴸ (((L.sum Language.order).sum B.lang).sum B.lang) where
  onFunction {_n} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl (Sum.inl (Sum.inl g))
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_n} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl (Sum.inl (Sum.inl s))
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
    | Sum.inr s => Sum.inr s

variable {L B} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem addOrderOne_isExpansionOn (ρ : B.Assignment A) :
    @LHom.IsExpansionOn _ _ (addOrderOne L B) A
      (B.structure₁ (L := L) ρ)
      (@SOBlock.structure₁ (L.sum Language.order) B A (@sumOrderStructure L A instL _) ρ) := by
  let := B.structure₁ (L := L) ρ
  let := @SOBlock.structure₁ (L.sum Language.order) B A (@sumOrderStructure L A instL _) ρ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl g => rfl
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl s => rfl
    | Sum.inr s => rfl

theorem addOrderTwo_isExpansionOn (ρ σ : B.Assignment A) :
    @LHom.IsExpansionOn _ _ (addOrderTwo L B) A
      (B.structure₂ (L := L) ρ σ)
      (@SOBlock.structure₂ (L.sum Language.order) B A (@sumOrderStructure L A instL _) ρ σ) := by
  let := B.structure₂ (L := L) ρ σ
  let := @SOBlock.structure₂ (L.sum Language.order) B A (@sumOrderStructure L A instL _) ρ σ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl g) => rfl
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl (Sum.inl s) => rfl
    | Sum.inl (Sum.inr s) => rfl
    | Sum.inr s => rfl

end AddOrder

namespace SOTCSpecFree

/-- An order-free specification, read as an ordinary one: the three sentences
are transported along `DescriptiveComplexity.addOrderOne` and
`DescriptiveComplexity.addOrderTwo`, so the order symbol is present in the
vocabulary and used nowhere. -/
def toSpec (spec : SOTCSpecFree L) : SOTCSpec L where
  B := spec.B
  step := (addOrderTwo L spec.B).onSentence spec.step
  src := (addOrderOne L spec.B).onSentence spec.src
  tgt := (addOrderOne L spec.B).onSentence spec.tgt

variable {spec : SOTCSpecFree L} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem toSpec_step_iff (ρ σ : spec.State A) : spec.toSpec.Step ρ σ ↔ spec.Step ρ σ := by
  let := spec.B.structure₂ (L := L) ρ σ
  let := @SOBlock.structure₂ (L.sum Language.order) spec.B A (@sumOrderStructure L A instL _) ρ σ
  have := addOrderTwo_isExpansionOn (L := L) (B := spec.B) ρ σ
  exact LHom.realize_onSentence (M := A) (addOrderTwo L spec.B) spec.step

theorem toSpec_isSrc_iff (ρ : spec.State A) : spec.toSpec.IsSrc ρ ↔ spec.IsSrc ρ := by
  let := spec.B.structure₁ (L := L) ρ
  let := @SOBlock.structure₁ (L.sum Language.order) spec.B A (@sumOrderStructure L A instL _) ρ
  have := addOrderOne_isExpansionOn (L := L) (B := spec.B) ρ
  exact LHom.realize_onSentence (M := A) (addOrderOne L spec.B) spec.src

theorem toSpec_isTgt_iff (ρ : spec.State A) : spec.toSpec.IsTgt ρ ↔ spec.IsTgt ρ := by
  let := spec.B.structure₁ (L := L) ρ
  let := @SOBlock.structure₁ (L.sum Language.order) spec.B A (@sumOrderStructure L A instL _) ρ
  have := addOrderOne_isExpansionOn (L := L) (B := spec.B) ρ
  exact LHom.realize_onSentence (M := A) (addOrderOne L spec.B) spec.tgt

/-- **Acceptance does not depend on the order**, for a specification that does
not mention it. -/
theorem accepts_toSpec_iff : spec.toSpec.Accepts A ↔ spec.Accepts A := by
  have hreach : ∀ ρ σ : spec.State A, spec.toSpec.Reach ρ σ ↔ spec.Reach ρ σ := by
    refine fun ρ σ => ⟨fun h => ?_, fun h => ?_⟩
    · induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hcd ih => exact ih.tail ((toSpec_step_iff _ _).mp hcd)
    · induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hcd ih => exact ih.tail ((toSpec_step_iff _ _).mpr hcd)
  constructor
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    exact ⟨ρ, σ, (toSpec_isSrc_iff ρ).mp hρ, (toSpec_isTgt_iff σ).mp hσ, (hreach ρ σ).mp h⟩
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    exact ⟨ρ, σ, (toSpec_isSrc_iff ρ).mpr hρ, (toSpec_isTgt_iff σ).mpr hσ, (hreach ρ σ).mpr h⟩

end SOTCSpecFree

/-! ### The order symbol, eliminated in favor of a state component

The hard direction. The block of the walk is extended by one binary relation
variable (`DescriptiveComplexity.SOBlock.withOrder`, shared with the
order elimination of `DescriptiveComplexity.SecondOrderOrdered`), the three
sentences read that variable in place of the order symbol, the source condition
adds `DescriptiveComplexity.linearGuard` and the transition condition adds that
the variable does not change. -/

section OrderElim

variable (L) (B : SOBlock)

/-- The order variable of the *current* state, as a symbol of the two-copy
expansion. -/
abbrev ordFstSym : ((L.sum B.withOrder.lang).sum B.withOrder.lang).Relations 2 :=
  Sum.inl (ordVarSym L B)

/-- The order variable of the *next* state, as a symbol of the two-copy
expansion. -/
abbrev ordSndSym : ((L.sum B.withOrder.lang).sum B.withOrder.lang).Relations 2 :=
  Sum.inr B.orderSym

/-- `x ≤ y` for the order variable of the current state. -/
private def leFstF {α : Type} (x y : α) :
    ((L.sum B.withOrder.lang).sum B.withOrder.lang).Formula α :=
  Relations.formula₂ (ordFstSym L B) (Term.var x) (Term.var y)

/-- `x ≤ y` for the order variable of the next state. -/
private def leSndF {α : Type} (x y : α) :
    ((L.sum B.withOrder.lang).sum B.withOrder.lang).Formula α :=
  Relations.formula₂ (ordSndSym L B) (Term.var x) (Term.var y)

/-- The guessed order does not change: the order variables of the two copies of
the block agree. -/
noncomputable def fixedOrdS : ((L.sum B.withOrder.lang).sum B.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
    ((leFstF L B (Sum.inr 0) (Sum.inr 1) ⟹ leSndF L B (Sum.inr 0) (Sum.inr 1)) ⊓
      (leSndF L B (Sum.inr 0) (Sum.inr 1) ⟹ leFstF L B (Sum.inr 0) (Sum.inr 1)))

/-- The language morphism eliminating the order symbol of the ordered
expansion, over *two* copies of a block: the order is read in the copy holding
the current state. -/
def orderElimTwoLHom :
    (((L.sum Language.order).sum B.lang).sum B.lang) →ᴸ
      ((L.sum B.withOrder.lang).sum B.withOrder.lang) where
  onFunction {_n} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => Sum.inl (Sum.inl g)
    | Sum.inl (Sum.inl (Sum.inr g)) => nomatch g
    | Sum.inl (Sum.inr g) => nomatch g
    | Sum.inr g => nomatch g
  onRelation {_n} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => Sum.inl (Sum.inl s)
    | Sum.inl (Sum.inl (Sum.inr .le)) => ordFstSym L B
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr ⟨Sum.inr s.1, s.2⟩)
    | Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

variable {L B} {A : Type}

private theorem vec_eta₂ (w : Fin 2 → A) : ![w 0, w 1] = w := by
  funext j
  fin_cases j <;> simp

/-- Realization of `DescriptiveComplexity.fixedOrdS`: the two copies assign the
same relation to the order variable. -/
theorem realize_fixedOrdS (instA : L.Structure A) (ρ σ : B.withOrder.Assignment A) :
    @Sentence.Realize _ A (@SOBlock.structure₂ L B.withOrder A instA ρ σ) (fixedOrdS L B) ↔
      ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ σ (Sum.inl ()) w := by
  let := instA
  let := @SOBlock.structure₂ L B.withOrder A instA ρ σ
  have hfst : ∀ w : Fin 2 → A,
      RelMap (L := (L.sum B.withOrder.lang).sum B.withOrder.lang) (M := A) (ordFstSym L B) w ↔
        ρ (Sum.inl ()) w := fun _ => Iff.rfl
  have hsnd : ∀ w : Fin 2 → A,
      RelMap (L := (L.sum B.withOrder.lang).sum B.withOrder.lang) (M := A) (ordSndSym L B) w ↔
        σ (Sum.inl ()) w := fun _ => Iff.rfl
  simp only [fixedOrdS, leFstF, leSndF, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, hfst, hsnd]
  constructor
  · intro h w
    have hw := h w
    rw [vec_eta₂] at hw
    exact ⟨hw.1, hw.2⟩
  · intro h x
    exact ⟨(h _).mp, (h _).mpr⟩

/-- The two-copy analogue of
`DescriptiveComplexity.orderElimLHom_isExpansionOn`: when the *current* state
assigns the linear order of the structure to the order variable, the two-copy
block expansion is an expansion along `DescriptiveComplexity.orderElimTwoLHom`
of the ordered one. -/
theorem orderElimTwoLHom_isExpansionOn (L : Language.{0, 0}) (B : SOBlock) (A : Type)
    (instA : L.Structure A) (lo : LinearOrder A) (ρ σ : B.withOrder.Assignment A)
    (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1) :
    @LHom.IsExpansionOn _ _ (orderElimTwoLHom L B) A
      (@SOBlock.structure₂ (L.sum Language.order) B A
        (letI := instA; letI := lo; sumOrderStructure L A) (B.restPart ρ) (B.restPart σ))
      (@SOBlock.structure₂ L B.withOrder A instA ρ σ) := by
  let := instA
  let := lo
  let := @SOBlock.structure₂ (L.sum Language.order) B A (sumOrderStructure L A)
    (B.restPart ρ) (B.restPart σ)
  let := @SOBlock.structure₂ L B.withOrder A instA ρ σ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => rfl
    | Sum.inl (Sum.inl (Sum.inr g)) => exact nomatch g
    | Sum.inl (Sum.inr g) => exact nomatch g
    | Sum.inr g => exact nomatch g
  · match n, r with
    | _, Sum.inl (Sum.inl (Sum.inl s)) => rfl
    | _, Sum.inl (Sum.inl (Sum.inr .le)) => exact propext (hord x)
    | _, Sum.inl (Sum.inr s) => rfl
    | _, Sum.inr s => rfl

end OrderElim

/-! ### The order-free reading of a specification -/

section Free

variable (spec : SOTCSpec L)

/-- **The order-free reading of an SO(TC) specification**: its state carries one
extra binary relation variable holding a guessed order, the source condition
checks that the guess is a linear order, every step freezes it, and the three
sentences read it in place of the order symbol. -/
noncomputable def SOTCSpec.orderFree : SOTCSpecFree L where
  B := spec.B.withOrder
  step := fixedOrdS L spec.B ⊓ (orderElimTwoLHom L spec.B).onSentence spec.step
  src := linearGuard L spec.B ⊓ (orderElimLHom L spec.B).onSentence spec.src
  tgt := (orderElimLHom L spec.B).onSentence spec.tgt

variable {spec} {A : Type} [instL : L.Structure A]

section Transport

variable [lo : LinearOrder A] {B : SOBlock} (ρ σ : B.withOrder.Assignment A)
  (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1)

include hord

/-- A sentence over the ordered expansion and one copy of a block says, read
through `DescriptiveComplexity.orderElimLHom` at a state whose order variable
holds the order, what it says of the underlying assignment. -/
theorem realize_orderElim_one (φ : ((L.sum Language.order).sum B.lang).Sentence) :
    @Sentence.Realize _ A (@SOBlock.structure₁ L B.withOrder A instL ρ)
        ((orderElimLHom L B).onSentence φ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) B A (sumOrderStructure L A) (B.restPart ρ))
        φ := by
  let := @SOBlock.structure₁ (L.sum Language.order) B A (sumOrderStructure L A) (B.restPart ρ)
  let := @SOBlock.structure₁ L B.withOrder A instL ρ
  have : @LHom.IsExpansionOn _ _ (orderElimLHom L B) A
      (@SOBlock.structure₁ (L.sum Language.order) B A (sumOrderStructure L A) (B.restPart ρ))
      (@SOBlock.structure₁ L B.withOrder A instL ρ) :=
    orderElimLHom_isExpansionOn L B A instL lo ρ hord
  exact LHom.realize_onSentence (M := A) (orderElimLHom L B) φ

/-- The two-copy analogue of `DescriptiveComplexity.realize_orderElim_one`: the
order is read in the copy holding the current state. -/
theorem realize_orderElim_two (φ : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence) :
    @Sentence.Realize _ A (@SOBlock.structure₂ L B.withOrder A instL ρ σ)
        ((orderElimTwoLHom L B).onSentence φ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) B A (sumOrderStructure L A)
          (B.restPart ρ) (B.restPart σ)) φ := by
  let := @SOBlock.structure₂ (L.sum Language.order) B A (sumOrderStructure L A)
    (B.restPart ρ) (B.restPart σ)
  let := @SOBlock.structure₂ L B.withOrder A instL ρ σ
  have : @LHom.IsExpansionOn _ _ (orderElimTwoLHom L B) A
      (@SOBlock.structure₂ (L.sum Language.order) B A (sumOrderStructure L A)
        (B.restPart ρ) (B.restPart σ))
      (@SOBlock.structure₂ L B.withOrder A instL ρ σ) :=
    orderElimTwoLHom_isExpansionOn L B A instL lo ρ σ hord
  exact LHom.realize_onSentence (M := A) (orderElimTwoLHom L B) φ

end Transport

section Semantics

variable [lo : LinearOrder A] {ρ σ : spec.B.withOrder.Assignment A}
  (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1)

include hord

omit instL in
/-- The guessed order, read as a relation between two elements. -/
private theorem hord_pair (a b : A) : ρ (Sum.inl ()) ![a, b] ↔ a ≤ b := by
  simpa using hord ![a, b]

/-- At a state whose order variable holds the order of the structure, the
guard of `DescriptiveComplexity.SOTCSpec.orderFree` is satisfied. -/
theorem realize_linearGuard_of_hord :
    @Sentence.Realize _ A (@SOBlock.structure₁ L spec.B.withOrder A instL ρ)
      (linearGuard L spec.B) :=
  (realize_linearGuard L spec.B instL ρ).mpr
    ⟨fun a => (hord_pair hord a a).mpr le_rfl,
      ⟨fun a b c hab hbc =>
          (hord_pair hord a c).mpr (le_trans ((hord_pair hord a b).mp hab)
            ((hord_pair hord b c).mp hbc)),
        ⟨fun a b hab hba =>
            le_antisymm ((hord_pair hord a b).mp hab) ((hord_pair hord b a).mp hba),
          fun a b => (le_total a b).imp (hord_pair hord a b).mpr (hord_pair hord b a).mpr⟩⟩⟩

theorem SOTCSpec.orderFree_isSrc_iff :
    spec.orderFree.IsSrc ρ ↔ spec.IsSrc (spec.B.restPart ρ) := by
  let := @SOBlock.structure₁ L spec.orderFree.B A instL ρ
  have hinf : spec.orderFree.IsSrc ρ ↔
      (@Sentence.Realize _ A (@SOBlock.structure₁ L spec.B.withOrder A instL ρ)
          (linearGuard L spec.B) ∧
        @Sentence.Realize _ A (@SOBlock.structure₁ L spec.B.withOrder A instL ρ)
          ((orderElimLHom L spec.B).onSentence spec.src)) := Formula.realize_inf
  rw [hinf]
  constructor
  · rintro ⟨-, h⟩
    exact (realize_orderElim_one ρ hord spec.src).mp h
  · intro h
    exact ⟨realize_linearGuard_of_hord hord, (realize_orderElim_one ρ hord spec.src).mpr h⟩

theorem SOTCSpec.orderFree_isTgt_iff :
    spec.orderFree.IsTgt ρ ↔ spec.IsTgt (spec.B.restPart ρ) :=
  realize_orderElim_one ρ hord spec.tgt

theorem SOTCSpec.orderFree_step_iff :
    spec.orderFree.Step ρ σ ↔
      ((∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ σ (Sum.inl ()) w) ∧
        spec.Step (spec.B.restPart ρ) (spec.B.restPart σ)) := by
  let := @SOBlock.structure₂ L spec.orderFree.B A instL ρ σ
  have hinf : spec.orderFree.Step ρ σ ↔
      (@Sentence.Realize _ A (@SOBlock.structure₂ L spec.B.withOrder A instL ρ σ)
          (fixedOrdS L spec.B) ∧
        @Sentence.Realize _ A (@SOBlock.structure₂ L spec.B.withOrder A instL ρ σ)
          ((orderElimTwoLHom L spec.B).onSentence spec.step)) := Formula.realize_inf
  rw [hinf]
  exact and_congr (realize_fixedOrdS instL ρ σ) (realize_orderElim_two ρ σ hord spec.step)

/-- **The guessed order is the same all along a walk**, and the rest of the
state walks in the original specification. -/
theorem SOTCSpec.orderFree_reach (h : spec.orderFree.Reach ρ σ) :
    (∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ σ (Sum.inl ()) w) ∧
      spec.Reach (spec.B.restPart ρ) (spec.B.restPart σ) := by
  induction h with
  | refl => exact ⟨fun _ => Iff.rfl, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨heq, hreach⟩ := ih
    have hordc : ∀ w : Fin 2 → A, c (Sum.inl ()) w ↔ w 0 ≤ w 1 :=
      fun w => (heq w).symm.trans (hord w)
    obtain ⟨heq', hstep⟩ := (SOTCSpec.orderFree_step_iff (spec := spec) hordc).mp hcd
    exact ⟨fun w => (heq w).trans (heq' w), hreach.tail hstep⟩

end Semantics

/-- The converse walk: a walk of the original specification, run with the order
of the structure guessed into every state. -/
theorem SOTCSpec.orderFree_reach_of [LinearOrder A] {ρ₁ σ₁ : spec.B.Assignment A}
    (h : spec.Reach ρ₁ σ₁) :
    spec.orderFree.Reach (spec.B.joinOrder (fun w => w 0 ≤ w 1) ρ₁)
      (spec.B.joinOrder (fun w => w 0 ≤ w 1) σ₁) := by
  have hord : ∀ (x : spec.B.Assignment A) (w : Fin 2 → A),
      spec.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) x (Sum.inl ()) w ↔ w 0 ≤ w 1 :=
    fun _ _ => Iff.rfl
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    exact ih.tail ((SOTCSpec.orderFree_step_iff (spec := spec) (hord c)).mpr
      ⟨fun _ => Iff.rfl, hcd⟩)

variable (A) in
/-- **Acceptance by the order-free reading is acceptance under a guessed
order**: the walk accepts exactly when the original one accepts for *some*
linear order on the universe. Together with order-invariance – the equivalence
required at *every* linear order in `DescriptiveComplexity.SOTCDefinable` –
this is what removes the hypothesis. -/
theorem SOTCSpec.orderFree_accepts_iff :
    spec.orderFree.Accepts A ↔ ∃ lo : LinearOrder A, @SOTCSpec.Accepts L spec A instL lo := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    let := @SOBlock.structure₁ L spec.orderFree.B A instL ρ
    have hinf : spec.orderFree.IsSrc ρ ↔
        (@Sentence.Realize _ A (@SOBlock.structure₁ L spec.B.withOrder A instL ρ)
            (linearGuard L spec.B) ∧
          @Sentence.Realize _ A (@SOBlock.structure₁ L spec.B.withOrder A instL ρ)
            ((orderElimLHom L spec.B).onSentence spec.src)) := Formula.realize_inf
    obtain ⟨hrefl, htrans, hantisymm, htotal⟩ :=
      (realize_linearGuard L spec.B instL ρ).mp (hinf.mp hsrc).1
    let lo : LinearOrder A :=
      linearOrderOfGuard (ρ (Sum.inl ())) hrefl htrans hantisymm htotal
    have hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1 := by
      intro w
      change ρ (Sum.inl ()) w ↔ ρ (Sum.inl ()) ![w 0, w 1]
      rw [vec_eta₂]
    obtain ⟨heq, hreach'⟩ := SOTCSpec.orderFree_reach (spec := spec) hord hreach
    have hordσ : ∀ w : Fin 2 → A, σ (Sum.inl ()) w ↔ w 0 ≤ w 1 :=
      fun w => (heq w).symm.trans (hord w)
    exact ⟨lo, spec.B.restPart ρ, spec.B.restPart σ,
      (SOTCSpec.orderFree_isSrc_iff (spec := spec) hord).mp hsrc,
      (SOTCSpec.orderFree_isTgt_iff (spec := spec) hordσ).mp htgt, hreach'⟩
  · rintro ⟨lo, ρ₁, σ₁, hsrc, htgt, hreach⟩
    let := lo
    have hord : ∀ w : Fin 2 → A,
        spec.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) ρ₁ (Sum.inl ()) w ↔ w 0 ≤ w 1 :=
      fun _ => Iff.rfl
    have hordσ : ∀ w : Fin 2 → A,
        spec.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) σ₁ (Sum.inl ()) w ↔ w 0 ≤ w 1 :=
      fun _ => Iff.rfl
    refine ⟨spec.B.joinOrder (fun w => w 0 ≤ w 1) ρ₁, spec.B.joinOrder (fun w => w 0 ≤ w 1) σ₁,
      (SOTCSpec.orderFree_isSrc_iff (spec := spec) hord).mpr ?_,
      (SOTCSpec.orderFree_isTgt_iff (spec := spec) hordσ).mpr ?_,
      SOTCSpec.orderFree_reach_of hreach⟩
    · exact hsrc
    · exact htgt

end Free

/-! ### Order-free SO(TC) definability -/

/-- A decision problem is *order-free SO(TC) definable* if it is defined by a
`DescriptiveComplexity.SOTCSpecFree` on nonempty finite structures – with **no
linear order in the statement at all**, unlike
`DescriptiveComplexity.SOTCDefinable`. -/
def SOTCDefinableFree [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : SOTCSpecFree L,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ spec.Accepts A

/-- **The order of SO(TC) can be guessed**: order-invariant SO(TC) definability
over ordered structures and order-free SO(TC) definability are the same notion.
Left to right the order is guessed into the state
(`DescriptiveComplexity.SOTCSpec.orderFree`) – a linear order exists on every
finite universe, and by order-invariance any one of them will do; right to left
a specification that never mentions the order is one that ignores it. -/
theorem sotcDefinable_iff_free [L.IsRelational] {P : DecisionProblem L} :
    SOTCDefinable P ↔ SOTCDefinableFree P := by
  constructor
  · rintro ⟨spec, hspec⟩
    refine ⟨spec.orderFree, fun A _ _ _ => ?_⟩
    rw [SOTCSpec.orderFree_accepts_iff]
    constructor
    · intro hP
      let := Fintype.ofFinite A
      let lo : LinearOrder A :=
        LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
      exact ⟨lo, (hspec A).mp hP⟩
    · rintro ⟨lo, h⟩
      let := lo
      exact (hspec A).mpr h
  · rintro ⟨spec, hspec⟩
    refine ⟨spec.toSpec, fun A _ _ _ _ => ?_⟩
    rw [SOTCSpecFree.accepts_toSpec_iff]
    exact hspec A

/-- **PSPACE needs no order**: membership is definability by an order-free
SO(TC) specification. -/
theorem mem_PSPACE_iff_sotcDefinableFree [L.IsRelational] (P : DecisionProblem L) :
    P ∈ PSPACE ↔ SOTCDefinableFree P :=
  (mem_PSPACE_iff P).trans sotcDefinable_iff_free

end DescriptiveComplexity
