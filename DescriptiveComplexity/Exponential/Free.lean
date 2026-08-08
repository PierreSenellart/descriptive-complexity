/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.PSpace
import DescriptiveComplexity.SecondOrderTransitiveClosureFree

/-!
# Exponential expansions that see no order

`DescriptiveComplexity.ExpExpansion` reads its domain and defining sentences
over the **ordered** expansion of the base vocabulary, and
`DescriptiveComplexity.ExpDefinable` asks for the equivalence at every linear
order of the instance. That is why `DescriptiveComplexity.EXPTIME` and
`DescriptiveComplexity.EXPSPACE` are written `SO(≤, LFP)` and `SO(≤, PFP)`.

This file introduces the order-free notion — an expansion whose sentences live
over the bare vocabulary, so that its universe is defined on a structure
carrying **no order at all** — and proves the easy half of the comparison: an
order-free expansion *is* an expansion, its sentences simply never mentioning
the order symbol
(`DescriptiveComplexity.ExpExpansionFree.toExp`), and its expanded structure is
the same one (`DescriptiveComplexity.ExpExpansionFree.toExpLEquiv`), whence
`DescriptiveComplexity.ExpDefinableFree.expDefinable`.

It then builds the converse construction: the order is **guessed into the
block**, as `DescriptiveComplexity.sotcDefinable_iff_free` guesses it into the
state of a walk. `DescriptiveComplexity.ExpExpansion.orderFree` adds one binary
variable to the block, guards it to be a linear order in the domain sentence,
reads every defining sentence through it, and requires all the arguments of a
symbol to carry the *same* order. The obstruction this leaves is that the
expanded universe becomes the **disjoint union, over the linear orders of the
instance, of copies** of the intended one; the copies are the classes of the new
symbol `DescriptiveComplexity.ExpExpansion.sameSym`, and each is the expanded
universe at the order it carries
(`DescriptiveComplexity.ExpExpansion.copyIn`,
`DescriptiveComplexity.ExpExpansion.exists_copyIn`). Reading the inner problem
inside one of them is `DescriptiveComplexity.Exponential.FreeCopy`; staying
inside the class while doing so is `DescriptiveComplexity.Exponential.FreeSpace`
for `PSPACE`, which guesses the copy as a relation, and
`DescriptiveComplexity.Exponential.FreeTime` for `PTIME`, which names it by one
of its points. They conclude `EXPSPACE = SO(PFP)` and `EXPTIME = SO(LFP)`, with
no order in either statement.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### The data -/

/-- An **order-free exponential expansion**: as
`DescriptiveComplexity.ExpExpansion`, except that the domain sentence and the
defining sentences live over the bare vocabulary expanded by copies of the
block, with no order symbol available. Its universe is therefore defined on a
structure carrying no order. -/
structure ExpExpansionFree (L : Language.{0, 0}) : Type 1 where
  /-- The tags: finitely many copies of the space of block assignments. -/
  Tag : Type
  /-- Tags are finite, so that finite structures expand to finite
  structures. -/
  [tagFinite : Finite Tag]
  /-- The block whose assignments are the points of the expanded universe. -/
  B : SOBlock
  /-- The vocabulary of the expanded structure. -/
  E : Language.{0, 0}
  /-- The expanded vocabulary is relational, as every vocabulary of this
  library. -/
  [eRelational : E.IsRelational]
  /-- The domain sentence of each tag, over the bare vocabulary. -/
  dom : Tag → (L.sum B.lang).Sentence
  /-- The defining sentence of each relation symbol at each tuple of tags, over
  the bare vocabulary and as many copies of the block as the symbol has
  arguments. -/
  relSentence : ∀ {n : ℕ}, E.Relations n → (Fin n → Tag) →
    (L.sum (B.replicate n).lang).Sentence
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (ρ : B.Assignment A),
      @Sentence.Realize _ A (B.structure₁ (L := L) ρ) (dom t)

attribute [instance] ExpExpansionFree.tagFinite ExpExpansionFree.eRelational

namespace ExpExpansionFree

variable (X : ExpExpansionFree L)

/-! ### The expanded universe -/

/-- A candidate point: a tagged assignment of the block. -/
protected abbrev Point (A : Type) : Type := X.Tag × X.B.Assignment A

variable {X}

/-- The domain condition on a candidate point. -/
def DomHolds {A : Type} [L.Structure A] (p : X.Point A) : Prop :=
  @Sentence.Realize _ A (X.B.structure₁ (L := L) p.2) (X.dom p.1)

variable (X)

/-- **The expanded universe**: the tagged block assignments satisfying their
tag's domain sentence. No order on `A` is involved. -/
protected def Map (A : Type) [L.Structure A] : Type := {p : X.Point A // DomHolds p}

variable {X}

/-- Two points of the expanded universe are equal as soon as their tags and
their assignments are. -/
theorem map_ext {A : Type} [L.Structure A] {x y : X.Map A}
    (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext_iff.mpr ⟨h₁, h₂⟩)

variable (X)

/-- **The expanded structure.** -/
instance mapStructure (A : Type) [L.Structure A] : X.E.Structure (X.Map A) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    @Sentence.Realize _ A
      ((X.B.replicate n).structure₁ (L := L)
        (X.B.replicateAssign fun i => (xs i).1.2))
      (X.relSentence r fun i => (xs i).1.1)

theorem relMap_map {A : Type} [L.Structure A] {n : ℕ} (r : X.E.Relations n)
    (xs : Fin n → X.Map A) :
    RelMap r xs ↔
      @Sentence.Realize _ A
        ((X.B.replicate n).structure₁ (L := L)
          (X.B.replicateAssign fun i => (xs i).1.2))
        (X.relSentence r fun i => (xs i).1.1) :=
  Iff.rfl

instance mapFinite (A : Type) [L.Structure A] [Finite A] : Finite (X.Map A) :=
  inferInstanceAs (Finite {p : X.Point A // DomHolds p})

instance mapNonempty (A : Type) [L.Structure A] [Finite A] [Nonempty A] :
    Nonempty (X.Map A) :=
  let ⟨t, ρ, h⟩ := X.dom_nonempty A
  ⟨⟨(t, ρ), h⟩⟩

/-! ### An order-free expansion is an expansion -/

/-- The same expansion, with the order symbol inserted into every sentence and
never used. -/
def toExp : ExpExpansion L where
  Tag := X.Tag
  B := X.B
  E := X.E
  dom t := (blockOrderLift L X.B).onSentence (X.dom t)
  relSentence {n} r τ := (blockOrderLift L (X.B.replicate n)).onSentence (X.relSentence r τ)
  dom_nonempty := by
    intro A _ _ _ _
    obtain ⟨t, ρ, h⟩ := X.dom_nonempty A
    exact ⟨t, ρ, (realize_blockOrderLift X.B ρ (X.dom t)).mpr h⟩

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- The two domain conditions agree: the order is inserted and never read. -/
theorem domHolds_toExp_iff (p : X.Point A) :
    ExpExpansion.DomHolds (X := X.toExp) p ↔ DomHolds p :=
  realize_blockOrderLift X.B p.2 (X.dom p.1)

/-- **The two expanded universes are the same set.** -/
def toExpEquiv : X.toExp.Map A ≃ X.Map A :=
  Equiv.subtypeEquivRight fun p => domHolds_toExp_iff p

variable (X A)

/-- The expanded structure of `DescriptiveComplexity.ExpExpansionFree.toExp` –
equal to the order-free one by definition, but not syntactically, so instance
search has to be handed it. -/
@[instance_reducible]
def toExpStructure : X.E.Structure (X.toExp.Map A) := X.toExp.mapStructure A

/-- **The two expanded structures are the same structure**: the order-free
expansion, read as an ordinary one, interprets every symbol as it did. -/
def toExpLEquiv :
    letI := toExpStructure X A
    X.toExp.Map A ≃[X.E] X.Map A :=
  letI := toExpStructure X A
  { toEquiv := toExpEquiv
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} r x => by
      first
        | exact realize_blockOrderLift (X.B.replicate n) _ (X.relSentence r _)
        | exact (realize_blockOrderLift (X.B.replicate n) _ (X.relSentence r _)).symm }

end ExpExpansionFree

/-! ### Order-free definability over an expanded universe -/

variable [L.IsRelational]

/-- **Order-free definability over an expanded universe**: the problem `P`
holds of `A` exactly when a fixed `Q ∈ C` holds of `X.Map A`, for an expansion
whose sentences see no order — so the equivalence is asked of structures
carrying no order at all. -/
def ExpDefinableFree (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansionFree L) (Q : DecisionProblem X.E), C.Mem Q ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

/-- **Order-free definability is definability**: the easy half of the
comparison. The order-free expansion is read as an ordinary one, and its
expanded structure is the same, so the same `Q` witnesses both. -/
theorem ExpDefinableFree.expDefinable {C : ComplexityClass} {P : DecisionProblem L}
    (h : ExpDefinableFree C P) : ExpDefinable C P := by
  obtain ⟨X, Q, hQ, hX⟩ := h
  letI hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      X.E.Structure (X.toExp.Map A) := fun A => X.toExpStructure A
  refine ⟨X.toExp, Q, hQ, ?_⟩
  intro A _ _ _ _
  exact (hX A).trans (Q.iso_invariant (X.toExpLEquiv A)).symm

/-! ### Eliminating the order at `n` copies of a block

`DescriptiveComplexity.orderElimLHom` and
`DescriptiveComplexity.orderElimTwoLHom` replace the order symbol by a block's
order variable at *one* and at *two* copies, which is what an
`DescriptiveComplexity.SOTCSpec` needs. An expansion's defining sentences live
over `DescriptiveComplexity.SOBlock.replicate n` instead, so they need the
`n`-copy analogue: the order is read in the copy `k`, and each original variable
of a copy becomes that copy's variable of the extended block. -/

section OrderElimRep

variable (L : Language.{0, 0}) (B : SOBlock) {n : ℕ} (k : Fin n)

/-- The language morphism eliminating the order symbol over `n` copies of a
block: the order is read in the copy `k`. -/
def orderElimRepLHom :
    ((L.sum Language.order).sum (B.replicate n).lang) →ᴸ
      (L.sum (B.withOrder.replicate n).lang) where
  onFunction {_m} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl g
    | Sum.inl (Sum.inr g) => nomatch g
    | Sum.inr g => nomatch g
  onRelation {_m} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl s
    | Sum.inl (Sum.inr .le) => Sum.inr ⟨(k, Sum.inl ()), rfl⟩
    | Sum.inr s => Sum.inr ⟨(s.1.1, Sum.inr s.1.2), s.2⟩

variable {L B k} {A : Type}

/-- **The `n`-copy elimination is an expansion**, when the copy `k` assigns the
structure's own order to its order variable. -/
theorem orderElimRepLHom_isExpansionOn (instA : L.Structure A) (lo : LinearOrder A)
    (ρs : Fin n → B.withOrder.Assignment A)
    (hord : ∀ w : Fin 2 → A, ρs k (Sum.inl ()) w ↔ (letI := lo; w 0 ≤ w 1)) :
    @LHom.IsExpansionOn _ _ (orderElimRepLHom L B k) A
      (@SOBlock.structure₁ (L.sum Language.order) (B.replicate n) A
        (letI := instA; letI := lo; sumOrderStructure L A)
        (B.replicateAssign fun j => B.restPart (ρs j)))
      (@SOBlock.structure₁ L (B.withOrder.replicate n) A instA
        (B.withOrder.replicateAssign ρs)) := by
  letI := instA
  letI := lo
  letI := @SOBlock.structure₁ (L.sum Language.order) (B.replicate n) A (sumOrderStructure L A)
    (B.replicateAssign fun j => B.restPart (ρs j))
  letI := @SOBlock.structure₁ L (B.withOrder.replicate n) A instA
    (B.withOrder.replicateAssign ρs)
  refine ⟨fun {m} f x => ?_, fun {m} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl g) => rfl
    | Sum.inl (Sum.inr g) => exact nomatch g
    | Sum.inr g => exact nomatch g
  · match m, r with
    | _, Sum.inl (Sum.inl s) => rfl
    | _, Sum.inl (Sum.inr .le) => exact propext (hord x)
    | _, Sum.inr s => rfl

/-- **The `n`-copy elimination is correct**: a sentence over the ordered
expansion and `n` copies of a block says, read through
`DescriptiveComplexity.orderElimRepLHom` at assignments whose copy `k` holds the
order, what it said of the underlying assignments. -/
theorem realize_orderElimRep (instA : L.Structure A) (lo : LinearOrder A)
    (ρs : Fin n → B.withOrder.Assignment A)
    (hord : ∀ w : Fin 2 → A, ρs k (Sum.inl ()) w ↔ (letI := lo; w 0 ≤ w 1))
    (φ : ((L.sum Language.order).sum (B.replicate n).lang).Sentence) :
    @Sentence.Realize _ A
        (@SOBlock.structure₁ L (B.withOrder.replicate n) A instA
          (B.withOrder.replicateAssign ρs))
        ((orderElimRepLHom L B k).onSentence φ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) (B.replicate n) A
          (letI := instA; letI := lo; sumOrderStructure L A)
          (B.replicateAssign fun j => B.restPart (ρs j))) φ := by
  letI := instA
  letI := lo
  letI := @SOBlock.structure₁ (L.sum Language.order) (B.replicate n) A (sumOrderStructure L A)
    (B.replicateAssign fun j => B.restPart (ρs j))
  letI := @SOBlock.structure₁ L (B.withOrder.replicate n) A instA
    (B.withOrder.replicateAssign ρs)
  haveI := orderElimRepLHom_isExpansionOn (L := L) (B := B) (k := k) instA lo ρs hord
  exact LHom.realize_onSentence (M := A) (orderElimRepLHom L B k) φ

end OrderElimRep

/-! ### The nullary symbols, shifted to arity one

A defining sentence of a **nullary** symbol has no copy of the block to read a
guessed order from, so an order-guessing expansion cannot define one. It
defines the *unary shift* of the symbol instead: a symbol whose single argument
names the point – hence the copy – the value is read in. The vocabulary
carrying those shifts is `DescriptiveComplexity.nullShiftLang`, and
`DescriptiveComplexity.rep0LHom` is what places a nullary sentence in the one
copy the shift provides. -/

section NullShift

/-- Relation symbols of the nullary-shift vocabulary: one **unary** symbol per
nullary symbol of `E`. -/
inductive nullShiftRel (T : Type) : ℕ → Type
  /-- The nullary symbol `s`, read at arity one. -/
  | shift : T → nullShiftRel T 1

/-- The vocabulary carrying the nullary symbols of `E` at arity one. -/
def nullShiftLang (E : Language.{0, 0}) : Language.{0, 0} :=
  ⟨fun _ => Empty, nullShiftRel (E.Relations 0)⟩

instance (E : Language.{0, 0}) : (nullShiftLang E).IsRelational :=
  fun _ => ⟨fun f => f.elim⟩

variable (L₀ : Language.{0, 0}) (B : SOBlock)

/-- The map of relation variables placing *no* copy of a block inside one
copy. Its source is empty, so there is nothing to choose. -/
def rep01Hom : (B.replicate 0).ι → (B.replicate 1).ι :=
  fun p => (0, p.2)

theorem rep01Hom_arity :
    ∀ i, (B.replicate 1).arity (rep01Hom B i) = (B.replicate 0).arity i :=
  fun _ => rfl

/-- Reading a sentence over *no* copy of a block inside one copy – the shape a
nullary defining sentence has, placed where the order can be read. -/
def rep0LHom :
    (L₀.sum (B.replicate 0).lang) →ᴸ (L₀.sum (B.replicate 1).lang) :=
  LHom.sumMap (LHom.id L₀) (SOBlock.homLHom (rep01Hom B) (rep01Hom_arity B))

variable {L₀ B} {A : Type}

/-- Any two assignments of a block replicated *zero* times agree: the index
type is empty. -/
theorem replicate_zero_assign_eq (ρ σ : (B.replicate 0).Assignment A) : ρ = σ :=
  funext fun i => i.1.elim0

/-- **Placing a nullary sentence in one copy is correct**: it says there what
it said with no copy at all. -/
theorem realize_rep0LHom [inst : L₀.Structure A] (σ : (B.replicate 1).Assignment A)
    (σ₀ : (B.replicate 0).Assignment A) (φ : (L₀.sum (B.replicate 0).lang).Sentence) :
    @Sentence.Realize _ A ((B.replicate 1).structure₁ (L := L₀) σ)
        ((rep0LHom L₀ B).onSentence φ) ↔
      @Sentence.Realize _ A ((B.replicate 0).structure₁ (L := L₀) σ₀) φ := by
  have h : (B.replicate 0).homAssign (rep01Hom B) (rep01Hom_arity B) σ = σ₀ :=
    replicate_zero_assign_eq _ _
  exact h ▸ SOBlock.realize_homSentence (L := L₀) (rep01Hom B) (rep01Hom_arity B) σ φ

end NullShift

/-! ### Guessing the order into the block

The hard direction, at the level of the expansion. The block is extended by one
binary variable, the domain sentence guards it to be a linear order and reads
the old domain through it, and every defining sentence requires all of its
arguments to carry the *same* order before reading the old sentence through the
first of them. The expanded universe becomes the disjoint union, over the linear
orders of the instance, of copies of the intended one, and the new binary symbol
`same` marks the copies.

A *nullary* symbol of the original vocabulary has no copy of the block to read
an order from, so the guessing expansion cannot define it: it defines its
**unary shift** instead (`DescriptiveComplexity.nullShiftLang`), whose one
argument names the copy the value is read in, and leaves the nullary symbol
itself at `⊥`. Nothing is lost — a reader of the expanded structure finds the
value of a nullary symbol inside a copy where the shift holds — and the
construction needs no hypothesis on the arities. -/

section Guess

/-- Relation symbols of the same-order vocabulary: one binary symbol. -/
inductive sameRel : ℕ → Type
  /-- `same x y`: the points `x` and `y` carry the same guessed order. -/
  | same : sameRel 2
  deriving DecidableEq

/-- The vocabulary of a single binary symbol, marking the points of an
order-guessing expansion that carry the same order. -/
def sameLang : Language.{0, 0} := ⟨fun _ => Empty, sameRel⟩
  deriving IsRelational

/-- The order variable of the copy `j`, as a symbol of the replicated
vocabulary. -/
abbrev ordCopySym (B : SOBlock) {n : ℕ} (j : Fin n) :
    (B.withOrder.replicate n).lang.Relations 2 :=
  ⟨(j, Sum.inl ()), rfl⟩

variable (L : Language.{0, 0}) (B : SOBlock)

/-- The copies `0` and `j` carry the same order. -/
noncomputable def ordAgreeS {n : ℕ} (j : Fin (n + 1)) :
    (L.sum (B.withOrder.replicate (n + 1)).lang).Sentence :=
  Formula.iAlls (Fin 2)
    (Relations.formula₂ (Sum.inr (ordCopySym B (0 : Fin (n + 1))))
        (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⇔
      Relations.formula₂ (Sum.inr (ordCopySym B j))
        (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- All the copies carry the same order. -/
noncomputable def allSameOrdS (n : ℕ) :
    (L.sum (B.withOrder.replicate (n + 1)).lang).Sentence :=
  listInf ((List.finRange (n + 1)).map (ordAgreeS L B))

variable {L B} {A : Type} [L.Structure A]

theorem realize_allSameOrdS {n : ℕ} (ρs : Fin (n + 1) → B.withOrder.Assignment A) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₁ L (B.withOrder.replicate (n + 1)) A ‹_›
          (B.withOrder.replicateAssign ρs)) (allSameOrdS L B n) ↔
      ∀ (j : Fin (n + 1)) (w : Fin 2 → A), ρs 0 (Sum.inl ()) w ↔ ρs j (Sum.inl ()) w) := by
  letI := @SOBlock.structure₁ L (B.withOrder.replicate (n + 1)) A ‹_›
    (B.withOrder.replicateAssign ρs)
  have hvec : ∀ w : Fin 2 → A, (![w 0, w 1] : Fin 2 → A) = w := by
    intro w
    funext j
    fin_cases j <;> rfl
  have hatom : ∀ (j : Fin (n + 1)) (w : Fin 2 → A),
      ((Relations.formula₂ (L := L.sum (B.withOrder.replicate (n + 1)).lang)
            (Sum.inr (ordCopySym B j))
            (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).Realize
        (Sum.elim (default : Empty → A) w) ↔ ρs j (Sum.inl ()) w) := by
    intro j w
    refine Iff.trans Formula.realize_rel₂ ?_
    simp only [Term.realize_var, Sum.elim_inr]
    rw [hvec]
    exact Iff.rfl
  rw [allSameOrdS, Sentence.Realize, realize_listInf]
  constructor
  · intro h j w
    have hj := Formula.realize_iff.mp
      (Formula.realize_iAlls.mp (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)) w)
    exact ((hatom 0 w).symm.trans hj).trans (hatom j w)
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    refine Formula.realize_iAlls.mpr fun w => Formula.realize_iff.mpr ?_
    exact ((hatom 0 w).trans (h j w)).trans (hatom j w).symm

end Guess

/-! ### The order-guessing expansion -/

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-- **The order, guessed into the block**: the same expansion with one binary
variable added, its domain sentence guarding that variable to be a linear order
and reading the old domain through it, and each defining sentence requiring all
of its arguments to carry the *same* order before reading the old sentence
through the first of them. A nullary symbol keeps no value – it has no copy to
read the order in – and its content moves to its unary shift, read in the copy
its argument names. -/
noncomputable def orderFree : ExpExpansionFree L where
  Tag := X.Tag
  B := X.B.withOrder
  E := (X.E.sum (nullShiftLang X.E)).sum sameLang
  dom t := linearGuard L X.B ⊓ (orderElimLHom L X.B).onSentence (X.dom t)
  relSentence {n} r τ :=
    match n, r with
    | 0, Sum.inl (Sum.inl _) => ⊥
    | (m + 1), Sum.inl (Sum.inl s) =>
        allSameOrdS L X.B m ⊓
          (orderElimRepLHom L X.B (0 : Fin (m + 1))).onSentence (X.relSentence s τ)
    | _, Sum.inl (Sum.inr (.shift s)) =>
        (orderElimRepLHom L X.B (0 : Fin 1)).onSentence
          ((rep0LHom (L.sum Language.order) X.B).onSentence
            (X.relSentence s fun i => i.elim0))
    | _, Sum.inr .same => allSameOrdS L X.B 1
  dom_nonempty := by
    intro A _ _ _
    letI := finiteLinearOrder A
    obtain ⟨t, ρ₀, h⟩ := X.dom_nonempty A
    refine ⟨t, X.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) ρ₀, ?_⟩
    letI := @SOBlock.structure₁ L X.B.withOrder A ‹_›
      (X.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) ρ₀)
    refine Formula.realize_inf.mpr ⟨?_, ?_⟩
    · exact (realize_linearGuard L X.B ‹L.Structure A›
        (X.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) ρ₀)).mpr
        ⟨fun a => le_rfl, fun a b c => le_trans, fun a b => le_antisymm,
          fun a b => le_total a b⟩
    · exact (realize_orderElim_one (L := L) (B := X.B)
        (X.B.joinOrder (fun w : Fin 2 → A => w 0 ≤ w 1) ρ₀)
        (fun _ => Iff.rfl) (X.dom t)).mpr h

/-! ### The symbols of the order-guessing vocabulary -/

/-- A relation symbol of the original vocabulary, read in the order-guessing
one. -/
abbrev origSym {n : ℕ} (r : X.E.Relations n) : X.orderFree.E.Relations n :=
  Sum.inl (Sum.inl r)

/-- The unary shift of a nullary symbol of the original vocabulary: it holds of
the points of a copy exactly when the symbol held in that copy. -/
abbrev nullSym (s : X.E.Relations 0) : X.orderFree.E.Relations 1 :=
  Sum.inl (Sum.inr (.shift s))

/-- The symbol marking two points that carry the same guessed order. -/
abbrev sameSym : X.orderFree.E.Relations 2 :=
  Sum.inr .same

/-! ### The guessed order of a point

Everything in this section is stated on a structure carrying **no order**: it
is what a reader of the order-guessing expansion sees. -/

section NoOrder

variable {X} {A : Type} [L.Structure A]

/-- **The order a point carries**: the value of the guessed order variable in
its assignment. -/
def pointOrd (p : X.orderFree.Map A) : (Fin 2 → A) → Prop :=
  p.1.2 (Sum.inl ())

/-- **The `same` symbol compares the guessed orders.** -/
theorem relMap_sameSym (xs : Fin 2 → X.orderFree.Map A) :
    (@RelMap X.orderFree.E (X.orderFree.Map A) (X.orderFree.mapStructure A) 2 X.sameSym xs ↔
      ∀ w : Fin 2 → A, pointOrd (xs 0) w ↔ pointOrd (xs 1) w) := by
  have hrel := ExpExpansionFree.relMap_map (X := X.orderFree) (A := A) X.sameSym xs
  have h := realize_allSameOrdS (L := L) (B := X.B) (n := 1) fun i => (xs i).1.2
  refine Iff.trans (Iff.trans hrel h) ?_
  exact ⟨fun hh w => hh 1 w, fun hh j w => by fin_cases j <;> [exact Iff.rfl; exact hh w]⟩

/-- The guessed order of a point satisfies the linear-order axioms: its domain
sentence guards it. -/
theorem pointOrd_linear (p : X.orderFree.Map A) :
    (∀ a : A, pointOrd p ![a, a]) ∧
      ((∀ a b c : A, pointOrd p ![a, b] → pointOrd p ![b, c] → pointOrd p ![a, c]) ∧
        ((∀ a b : A, pointOrd p ![a, b] → pointOrd p ![b, a] → a = b) ∧
          ∀ a b : A, pointOrd p ![a, b] ∨ pointOrd p ![b, a])) := by
  letI := @SOBlock.structure₁ L X.B.withOrder A ‹_› p.1.2
  have hdom : @Sentence.Realize _ A (@SOBlock.structure₁ L X.B.withOrder A ‹_› p.1.2)
      (linearGuard L X.B ⊓ (orderElimLHom L X.B).onSentence (X.dom p.1.1)) := p.2
  refine (realize_linearGuard L X.B ‹L.Structure A› p.1.2).mp ?_
  exact (Formula.realize_inf.mp hdom).1

/-- The linear order a point carries. -/
@[instance_reducible]
noncomputable def guessedLinearOrder (p : X.orderFree.Map A) : LinearOrder A :=
  let h := pointOrd_linear p
  linearOrderOfGuard (pointOrd p) h.1 h.2.1 h.2.2.1 h.2.2.2

theorem le_guessedLinearOrder (p : X.orderFree.Map A) (w : Fin 2 → A) :
    (letI := guessedLinearOrder p; w 0 ≤ w 1) ↔ pointOrd p w := by
  change pointOrd p ![w 0, w 1] ↔ pointOrd p w
  have hvec : (![w 0, w 1] : Fin 2 → A) = w := by
    funext j
    fin_cases j <;> rfl
  rw [hvec]

end NoOrder

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- The ambient order, as a binary relation on tuples. -/
def loRel : (Fin 2 → A) → Prop := fun w => w 0 ≤ w 1

omit [L.Structure A] in
theorem joinOrder_ord (ρ : X.B.Assignment A) :
    (X.B.joinOrder (loRel (A := A)) ρ) (Sum.inl ()) = loRel := rfl

/-- The guessed order of a placed point is the ambient one. -/
theorem domHolds_copyIn (x : X.Map A) :
    ExpExpansionFree.DomHolds (X := X.orderFree)
      (x.1.1, X.B.joinOrder (loRel (A := A)) x.1.2) := by
  letI := @SOBlock.structure₁ L X.B.withOrder A ‹_› (X.B.joinOrder (loRel (A := A)) x.1.2)
  change @Sentence.Realize _ A
    (@SOBlock.structure₁ L X.B.withOrder A ‹_› (X.B.joinOrder (loRel (A := A)) x.1.2))
    (linearGuard L X.B ⊓ (orderElimLHom L X.B).onSentence (X.dom x.1.1))
  refine Formula.realize_inf.mpr ⟨?_, ?_⟩
  · exact (realize_linearGuard L X.B ‹L.Structure A›
      (X.B.joinOrder (loRel (A := A)) x.1.2)).mpr
      ⟨fun a => le_rfl, fun a b c => le_trans, fun a b => le_antisymm,
        fun a b => le_total a b⟩
  · exact (realize_orderElim_one (L := L) (B := X.B)
      (X.B.joinOrder (loRel (A := A)) x.1.2) (fun _ => Iff.rfl) (X.dom x.1.1)).mpr x.2

/-- **A point of the expansion, placed in the copy of the ambient order.** -/
def copyIn (x : X.Map A) : X.orderFree.Map A :=
  ⟨(x.1.1, X.B.joinOrder loRel x.1.2), domHolds_copyIn x⟩

@[simp]
theorem copyIn_tag (x : X.Map A) : (copyIn x).1.1 = x.1.1 := rfl

@[simp]
theorem copyIn_rest (x : X.Map A) : X.B.restPart (copyIn x).1.2 = x.1.2 := rfl

theorem copyIn_injective : Function.Injective (copyIn (X := X) (A := A)) := by
  intro x y h
  refine ExpExpansion.map_ext (congrArg (fun p => p.1.1) h) ?_
  exact congrArg (fun p => X.B.restPart p.1.2) h

/-- The guessed order of a placed point is the ambient one. -/
theorem pointOrd_copyIn (x : X.Map A) (w : Fin 2 → A) :
    pointOrd (copyIn x) w ↔ w 0 ≤ w 1 :=
  Iff.rfl

/-- **The relations are unchanged inside a copy**: a relation of the original
vocabulary, of arity at least one, holds of points of one copy exactly when it
held of them. -/
theorem relMap_copyIn {m : ℕ} (r : X.E.Relations (m + 1)) (xs : Fin (m + 1) → X.Map A) :
    (@RelMap (X.orderFree.E) (X.orderFree.Map A) (X.orderFree.mapStructure A) (m + 1)
        (X.origSym r) (fun i => copyIn (xs i)) ↔
      @RelMap X.E (X.Map A) (X.mapStructure A) (m + 1) r xs) := by
  letI := @SOBlock.structure₁ L (X.B.withOrder.replicate (m + 1)) A ‹_›
    (X.B.withOrder.replicateAssign fun i => (copyIn (xs i)).1.2)
  change (@Sentence.Realize _ A
    (@SOBlock.structure₁ L (X.B.withOrder.replicate (m + 1)) A ‹_›
      (X.B.withOrder.replicateAssign fun i => (copyIn (xs i)).1.2))
    (allSameOrdS L X.B m ⊓
      (orderElimRepLHom L X.B (0 : Fin (m + 1))).onSentence
        (X.relSentence r fun i => (xs i).1.1))) ↔ _
  refine Iff.trans Formula.realize_inf ?_
  refine Iff.trans (and_iff_right ?_) ?_
  · exact (realize_allSameOrdS (L := L) (B := X.B) _).mpr fun _ _ => Iff.rfl
  · exact realize_orderElimRep (L := L) (B := X.B) (k := (0 : Fin (m + 1))) ‹L.Structure A›
      ‹LinearOrder A› (fun i => (copyIn (xs i)).1.2) (fun _ => Iff.rfl)
      (X.relSentence r fun i => (xs i).1.1)

/-- **The unary shift carries the nullary symbols inside a copy**: it holds of
a placed point exactly when the nullary symbol held. -/
theorem relMap_nullCopyIn (s : X.E.Relations 0) (xs : Fin 1 → X.Map A)
    (ys : Fin 0 → X.Map A) :
    (@RelMap (X.orderFree.E) (X.orderFree.Map A) (X.orderFree.mapStructure A) 1
        (X.nullSym s) (fun i => copyIn (xs i)) ↔
      @RelMap X.E (X.Map A) (X.mapStructure A) 0 s ys) := by
  letI := sumOrderStructure L A
  have htag : (fun i : Fin 0 => (ys i).1.1) = fun i => i.elim0 := funext fun i => i.elim0
  have h1 := realize_orderElimRep (L := L) (B := X.B) (k := (0 : Fin 1)) ‹L.Structure A›
    ‹LinearOrder A› (fun i => (copyIn (xs i)).1.2) (fun _ => Iff.rfl)
    ((rep0LHom (L.sum Language.order) X.B).onSentence (X.relSentence s fun i => i.elim0))
  have h2 := realize_rep0LHom (L₀ := L.sum Language.order) (B := X.B)
    (X.B.replicateAssign fun j => X.B.restPart ((copyIn (xs j)).1.2))
    (X.B.replicateAssign fun i => (ys i).1.2) (X.relSentence s fun i => i.elim0)
  have h3 : (@RelMap X.E (X.Map A) (X.mapStructure A) 0 s ys) ↔
      @Sentence.Realize _ A
        ((X.B.replicate 0).structure₁ (L := L.sum Language.order)
          (X.B.replicateAssign fun i => (ys i).1.2))
        (X.relSentence s fun i => i.elim0) := by
    rw [← htag]
    exact X.relMap_map s ys
  exact h1.trans (h2.trans h3.symm)

/-! ### Reading a copy back

The converse of `DescriptiveComplexity.ExpExpansion.copyIn`: a point whose
guessed order is the ambient one *is* a placed point, so the copies of the
order-guessing expansion are exactly the images of the copy maps, one per
linear order of the instance. -/

omit [L.Structure A] in
/-- Rebuilding an assignment from its order variable and the rest. -/
theorem joinOrder_restPart {ρ : X.B.withOrder.Assignment A}
    (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ loRel w) :
    X.B.joinOrder (loRel (A := A)) (X.B.restPart ρ) = ρ := by
  funext i
  match i with
  | Sum.inl () => exact funext fun w => propext (hord w).symm
  | Sum.inr _ => rfl

/-- The domain condition survives reading a point back at the order it
carries. -/
theorem domHolds_of_pointOrd {p : X.orderFree.Map A}
    (hord : ∀ w : Fin 2 → A, pointOrd p w ↔ loRel w) :
    DomHolds (X := X) (p.1.1, X.B.restPart p.1.2) := by
  letI := @SOBlock.structure₁ L X.B.withOrder A ‹L.Structure A› p.1.2
  have hdom : @Sentence.Realize _ A
      (@SOBlock.structure₁ L X.B.withOrder A ‹L.Structure A› p.1.2)
      (linearGuard L X.B ⊓ (orderElimLHom L X.B).onSentence (X.dom p.1.1)) := p.2
  exact (realize_orderElim_one (L := L) (B := X.B) p.1.2 hord (X.dom p.1.1)).mp
    (Formula.realize_inf.mp hdom).2

/-- **A point carrying the ambient order is a placed point.** -/
theorem exists_copyIn {p : X.orderFree.Map A}
    (hord : ∀ w : Fin 2 → A, pointOrd p w ↔ loRel w) : ∃ x : X.Map A, copyIn x = p := by
  refine ⟨⟨(p.1.1, X.B.restPart p.1.2), domHolds_of_pointOrd hord⟩, ?_⟩
  refine ExpExpansionFree.map_ext rfl ?_
  exact joinOrder_restPart hord

end ExpExpansion

end DescriptiveComplexity
