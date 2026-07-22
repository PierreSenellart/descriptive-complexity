/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Complexity

/-!
# Second-order definability with bounded alternation

Foundation for *defining* the levels `Σₖ`/`Πₖ` (`k ≥ 1`) of the polynomial
hierarchy logically, by Fagin's and Stockmeyer's theorems: `Σₖᵖ` consists of
the problems definable by a second-order sentence with `k` alternating blocks
of second-order quantifiers starting existentially – on unordered finite
structures (the first existential block can guess a linear order, so the
order-free definition is equivalent to the classical ordered one).

No object-level second-order syntax is needed: a second-order quantifier
block (`DescriptiveComplexity.SOBlock`) is a finite family of relation variables with
given arities, its instantiations are Lean-level (`SOBlock.structure` turns
an assignment of relations into a structure over the block's vocabulary
`SOBlock.lang`), and only the first-order kernel is object-level – a sentence
over the base language expanded by all blocks (`DescriptiveComplexity.soLang`).
`DescriptiveComplexity.SORealize` evaluates the alternating quantification, and
`DescriptiveComplexity.SigmaSODefinable` / `DescriptiveComplexity.PiSODefinable` state that a
decision problem is defined by such a sentence *on nonempty finite
structures*.

This file proves the two structural facts about these notions that do not
involve reductions:

* isomorphism-invariance (`DescriptiveComplexity.sorealize_iso`) – so second-order
  definable properties are bona fide decision problems;
* the duality `Πₖ = co-Σₖ` (`DescriptiveComplexity.piSODefinable_iff_compl`), by
  negating the kernel and flipping the quantifiers.

The rest of the definitional theory lives in dedicated files: functoriality
and padding in `DescriptiveComplexity.SecondOrderLift`, closure under FO reductions in
`DescriptiveComplexity.SecondOrderPull`, closure under ordered FO reductions in
`DescriptiveComplexity.SecondOrderOrdered`, and the resulting definition of the levels
`Σₖᵖ`/`Πₖᵖ` for `k ≥ 1` in `DescriptiveComplexity.Hierarchy`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Second-order quantifier blocks -/

/-- A second-order quantifier block: finitely many relation variables, with
given arities. (The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks – e.g. pulling a block back through an
interpretation – can build their natural index types directly.) -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

/-- The (relational) vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

instance (B : SOBlock) : IsRelational B.lang :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- An assignment of actual relations (on a universe `A`) to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

/-- The structure over the block's vocabulary determined by an assignment. -/
@[instance_reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

/-- The base language expanded by the vocabularies of a list of blocks. -/
def soLang (L : Language.{0, 0}) : List SOBlock → Language.{0, 0}
  | [] => L
  | B :: Bs => soLang (L.sum B.lang) Bs

/-- Alternating second-order satisfaction: `SORealize L A Bs φ pol` states
that the sentence obtained from the first-order kernel `φ` by quantifying the
blocks `Bs` alternately – existentially first if `pol` is `true` – holds in
the `L`-structure `A`. -/
def SORealize (L : Language.{0, 0}) (A : Type) [inst : L.Structure A] :
    ∀ (Bs : List SOBlock), (soLang L Bs).Sentence → Bool → Prop
  | [], φ, _ => @Sentence.Realize L A inst φ
  | B :: Bs, φ, true =>
      ∃ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ false
  | B :: Bs, φ, false =>
      ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ true

variable {L : Language.{0, 0}}

/-- A decision problem is `Σₖ`-definable if, on nonempty finite structures, it
is defined by a second-order sentence with `k` alternating blocks of
second-order quantifiers, starting existentially. (As everywhere in this
development, complexity notions are about nonempty finite structures.) -/
def SigmaSODefinable (k : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ Bs : List SOBlock, Bs.length = k ∧
    ∃ φ : (soLang L Bs).Sentence,
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ SORealize L A Bs φ true

/-- A decision problem is `Πₖ`-definable if, on nonempty finite structures, it
is defined by a second-order sentence with `k` alternating blocks of
second-order quantifiers, starting universally. -/
def PiSODefinable (k : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ Bs : List SOBlock, Bs.length = k ∧
    ∃ φ : (soLang L Bs).Sentence,
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ SORealize L A Bs φ false

/-! ### Isomorphism-invariance -/

section Iso

/-- Transport of a block assignment along an equivalence. -/
def SOBlock.mapAssign (B : SOBlock) {A A' : Type} (e : A ≃ A') (ρ : B.Assignment A) :
    B.Assignment A' :=
  fun i x => ρ i fun j => e.symm (x j)

/-- An `L`-isomorphism extends to the vocabulary expanded by a block, when
the block is interpreted by an assignment on one side and its transport on
the other. -/
def SOBlock.extendEquiv (B : SOBlock) {A A' : Type} [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (ρ : B.Assignment A) :
    @Language.Equiv (L.sum B.lang) A A'
      (@sumStructure L B.lang A _ (B.structure ρ))
      (@sumStructure L B.lang A' _ (B.structure (B.mapAssign e.toEquiv ρ))) :=
  letI := B.structure ρ
  letI := B.structure (B.mapAssign e.toEquiv ρ)
  { toEquiv := e.toEquiv
    map_fun' := fun {n} f => by
      cases f with
      | inl f => exact HomClass.map_fun e.toHom f
      | inr f => exact isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r => exact StrongHomClass.map_rel e r x
      | inr r =>
        change B.mapAssign e.toEquiv ρ r.1 _ ↔ ρ r.1 _
        rw [SOBlock.mapAssign]
        refine iff_of_eq (congrArg _ (funext fun j => ?_))
        exact e.toEquiv.symm_apply_apply _ }

private theorem sorealize_iso_aux :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A A' : Type) (instA : L.Structure A)
      (instA' : L.Structure A'), @Language.Equiv L A A' instA instA' →
      ∀ (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A instA Bs φ pol → @SORealize L A' instA' Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A A' instA instA' e φ pol h
    exact (StrongHomClass.realize_sentence (L := L) e φ).mp h
  | cons B Bs ih =>
    intro L A A' instA instA' e φ pol h
    cases pol with
    | true =>
      obtain ⟨ρ, hρ⟩ := h
      exact ⟨B.mapAssign e.toEquiv ρ, ih _ _ _ _ _ (B.extendEquiv e ρ) φ false hρ⟩
    | false =>
      intro ρ'
      have key : B.mapAssign e.toEquiv (B.mapAssign e.toEquiv.symm ρ') = ρ' := by
        funext i x
        rw [SOBlock.mapAssign, SOBlock.mapAssign]
        exact congrArg _ (funext fun j => e.toEquiv.apply_symm_apply _)
      have h' := ih _ _ _ _ _ (B.extendEquiv e (B.mapAssign e.toEquiv.symm ρ')) φ true
        (h (B.mapAssign e.toEquiv.symm ρ'))
      rwa [key] at h'

/-- Alternating second-order satisfaction is isomorphism-invariant: what a
second-order sentence expresses is a decision problem. -/
theorem sorealize_iso {A A' : Type} [L.Structure A] [L.Structure A'] (e : A ≃[L] A')
    (Bs : List SOBlock) (φ : (soLang L Bs).Sentence) (pol : Bool) :
    SORealize L A Bs φ pol ↔ SORealize L A' Bs φ pol :=
  ⟨sorealize_iso_aux Bs L A A' _ _ e φ pol,
    sorealize_iso_aux Bs L A' A _ _ e.symm φ pol⟩

end Iso

/-! ### Duality: `Πₖ` is co-`Σₖ` -/

section Duality

private theorem sorealize_not :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (inst : L.Structure A)
      (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A inst Bs (∼φ) pol ↔ ¬@SORealize L A inst Bs φ (!pol) := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A inst φ pol
    exact Sentence.realize_not A
  | cons B Bs ih =>
    intro L A inst φ pol
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, hρ⟩ h
        exact ((ih _ _ _ φ false).mp hρ) (h ρ)
      · intro h
        rcases Classical.em (∃ ρ : B.Assignment A,
            ¬@SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
              Bs φ true) with ⟨ρ, hρ⟩ | hne
        · exact ⟨ρ, (ih _ _ _ φ false).mpr hρ⟩
        · exact absurd (fun ρ => not_not.mp fun hn => hne ⟨ρ, hn⟩) h
    | false =>
      constructor
      · rintro h ⟨ρ, hρ⟩
        exact ((ih _ _ _ φ true).mp (h ρ)) hρ
      · intro h ρ
        exact (ih _ _ _ φ true).mpr fun hρ => h ⟨ρ, hρ⟩

/-- A problem is `Πₖ`-definable iff its complement is `Σₖ`-definable. -/
theorem piSODefinable_iff_compl (k : ℕ) (P : DecisionProblem L) :
    PiSODefinable k P ↔ SigmaSODefinable k Pᶜ := by
  constructor
  · rintro ⟨Bs, hk, φ, hφ⟩
    refine ⟨Bs, hk, ∼φ, ?_⟩
    intro A _ _ _
    have hd := sorealize_not Bs L A inferInstance φ true
    simp only [Bool.not_true] at hd
    exact (not_congr (hφ A)).trans hd.symm
  · rintro ⟨Bs, hk, φ, hφ⟩
    refine ⟨Bs, hk, ∼φ, ?_⟩
    intro A _ _ _
    have hd := sorealize_not Bs L A inferInstance φ false
    simp only [Bool.not_false] at hd
    exact (not_not.symm.trans (not_congr (hφ A))).trans hd.symm

/-- A problem is `Σₖ`-definable iff its complement is `Πₖ`-definable. -/
theorem sigmaSODefinable_iff_compl (k : ℕ) (P : DecisionProblem L) :
    SigmaSODefinable k P ↔ PiSODefinable k Pᶜ := by
  rw [piSODefinable_iff_compl, DecisionProblem.compl_compl]

end Duality

end DescriptiveComplexity
