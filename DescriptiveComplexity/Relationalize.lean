/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.RecursivelyEnumerable

/-!
# Relationalizing an `∃SO[new]` definition

Hardness proofs whose target reads the *source* structure through the defining
formulas of an interpretation cope with function symbols for free; one whose
target has to *name* what a function does – as the encoded sentence of
`DescriptiveComplexity.FINSAT` must, since it carries its own quantifiers – does
not. This file removes function symbols from the source once and for all:

> every `∃SO[new]`-definable problem admits a first-order reduction to an
> `∃SO[new]`-definable problem over a **relational** vocabulary
> (`DescriptiveComplexity.exists_relational_of_sigmaSONewDefinable`).

Composed with a hardness result proved for relational sources, it gives the
hardness result for all of them, which is what
`DescriptiveComplexity.CofinalHard` asks for.

## The two obstacles, and how they are removed

**The junk value.** An extended universe `A ⊕ Fin m` interprets a function
symbol on a tuple with an invented argument by applying `f^A` to
`DescriptiveComplexity.oldPart`, which sends every invented value to
`Classical.arbitrary A`. That element depends on the *carrier type* only, so no
formula can name it, and a translation that has to mention it is stuck. The way
out is that the definability equivalence quantifies over every `L`-structure
*instance* on the carrier: transporting the structure along a transposition
gives a second instance, isomorphic to the first, whose junk element is whatever
we like. Hence `DescriptiveComplexity.sigmaSONewDefinable_junk`: an `∃SO[new]`
definition may be read with *any* junk element.

**The terms.** The relational vocabulary is the **atomic diagram language**
`DescriptiveComplexity.atomLang`: one relation symbol of arity `n` per atomic
formula of `L` in `n` variables. An `L`-structure carries one canonically, and
the map is a one-dimensional first-order interpretation, since “this atomic
formula holds of this tuple” is a first-order property of the tuple. The kernel
is then translated atom by atom, *in place*: an atom at context length `n`
becomes an existential block of `n + 1` variables – the coerced arguments, and
the junk element the block guesses – followed by the corresponding symbol of the
atomic diagram language. Nothing else in the kernel changes, so no de Bruijn
index is ever shifted.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### An extended universe with a chosen junk value -/

section Junk

variable {L : Language.{0, 0}} {A : Type}

/-- The original-element part of an extended universe, reading an invented value
as a *given* element rather than `Classical.arbitrary`. -/
def oldPartAt (A : Type) (m : ℕ) (z : A) : A ⊕ Fin m → A := Sum.elim id fun _ => z

/-- The base structure carried by an extended universe with a chosen junk
value. -/
@[instance_reducible]
def extBaseAt (L : Language.{0, 0}) (A : Type) [L.Structure A] (m : ℕ) (z : A) :
    L.Structure (A ⊕ Fin m) where
  funMap f x := Sum.inl (funMap f fun i => oldPartAt A m z (x i))
  RelMap {_k} r x := ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y

/-- The extended structure with a chosen junk value. -/
@[instance_reducible]
def extStructureAt (L : Language.{0, 0}) (A : Type) [L.Structure A] (m : ℕ) (z : A) :
    (newLang L).Structure (A ⊕ Fin m) :=
  @sumStructure L Language.oldMark (A ⊕ Fin m) (extBaseAt L A m z) (oldMarkStructure A m)

/-- At the arbitrary element it is the extended structure of
`DescriptiveComplexity.extStructure`. -/
theorem extStructureAt_arbitrary (L : Language.{0, 0}) (A : Type) [L.Structure A]
    [Nonempty A] (m : ℕ) :
    extStructureAt L A m (Classical.arbitrary A) = extStructure L A m := rfl

/-! The three defining equations of the extended structure, stated with the
instance explicit: two structures on one carrier are in play below, so no
occurrence of `funMap` or `RelMap` may be left to instance synthesis. -/

theorem funMap_extAt {m : ℕ} (z : A) (inst : L.Structure A) {n : ℕ} (g : L.Functions n)
    (x : Fin n → A ⊕ Fin m) :
    @funMap (newLang L) (A ⊕ Fin m) (@extStructureAt L A inst m z) n (Sum.inl g) x =
      Sum.inl (@funMap L A inst n g fun i => oldPartAt A m z (x i)) := rfl

theorem relMap_extAt {m : ℕ} (z : A) (inst : L.Structure A) {n : ℕ} (s : L.Relations n)
    (x : Fin n → A ⊕ Fin m) :
    @RelMap (newLang L) (A ⊕ Fin m) (@extStructureAt L A inst m z) n (Sum.inl s) x ↔
      ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ @RelMap L A inst n s y := Iff.rfl

theorem relMap_extAt_old {m : ℕ} (z : A) (inst : L.Structure A) (x : Fin 1 → A ⊕ Fin m) :
    @RelMap (newLang L) (A ⊕ Fin m) (@extStructureAt L A inst m z) 1
      (Sum.inr Language.oldSym) x ↔ IsOld (x 0) := Iff.rfl

/-- **Transporting a structure along a permutation of its carrier**: a second
structure on the same type, isomorphic to the first. -/
@[instance_reducible]
def transportStruct (π : A ≃ A) (inst : L.Structure A) : L.Structure A where
  funMap f x := π.symm (funMap f fun i => π (x i))
  RelMap {_k} r x := RelMap r fun i => π (x i)

theorem funMap_transport (π : A ≃ A) (inst : L.Structure A) {n : ℕ} (g : L.Functions n)
    (x : Fin n → A) :
    @funMap L A (transportStruct π inst) n g x =
      π.symm (@funMap L A inst n g fun i => π (x i)) := rfl

theorem relMap_transport (π : A ≃ A) (inst : L.Structure A) {n : ℕ} (s : L.Relations n)
    (x : Fin n → A) :
    @RelMap L A (transportStruct π inst) n s x ↔
      @RelMap L A inst n s fun i => π (x i) := Iff.rfl

/-- The permutation *is* that isomorphism. -/
def transportEquiv (π : A ≃ A) (inst : L.Structure A) :
    @Language.Equiv L A A (transportStruct π inst) inst :=
  @Language.Equiv.mk L A A (transportStruct π inst) inst π
    (fun {_n} _ _ => Equiv.apply_symm_apply π _) (fun {_n} _ _ => Iff.rfl)

/-- **The junk value moves with the permutation**: the extended structure of the
transported instance, with junk `z`, is the extended structure of the original
instance with junk `π z`. This is what lets a definition be read at any junk
value at all. -/
def extIsoTransport (π : A ≃ A) (inst : L.Structure A) (m : ℕ) (z : A) :
    @Language.Equiv (newLang L) (A ⊕ Fin m) (A ⊕ Fin m)
      (@extStructureAt L A (transportStruct π inst) m z)
      (@extStructureAt L A inst m (π z)) :=
  @Language.Equiv.mk (newLang L) (A ⊕ Fin m) (A ⊕ Fin m)
    (@extStructureAt L A (transportStruct π inst) m z)
    (@extStructureAt L A inst m (π z))
    (Equiv.sumCongr π (Equiv.refl (Fin m)))
    (fun {_n} f x => by
      have hmap : ∀ w : A ⊕ Fin m,
          (Equiv.sumCongr π (Equiv.refl (Fin m))).toFun w = Sum.map π id w := fun _ => rfl
      cases f with
      | inr e => exact isEmptyElim e
      | inl g =>
        have hold : ∀ w : A ⊕ Fin m,
            π (oldPartAt A m z w) = oldPartAt A m (π z) (Sum.map π id w) := by
          rintro (a | j) <;> rfl
        rw [funMap_extAt, funMap_extAt, funMap_transport]
        simp only [Function.comp_apply, hmap, Sum.map_inl, Equiv.apply_symm_apply]
        exact congrArg (fun u => Sum.inl (@funMap L A inst _ g u)) (funext fun i => hold (x i)))
    (fun {_n} r x => by
      have hmap : ∀ w : A ⊕ Fin m,
          (Equiv.sumCongr π (Equiv.refl (Fin m))).toFun w = Sum.map π id w := fun _ => rfl
      cases r with
      | inl s =>
        rw [relMap_extAt, relMap_extAt]
        simp only [relMap_transport, Function.comp_apply, hmap]
        constructor
        · rintro ⟨y, hy, hr⟩
          refine ⟨fun i => π.symm (y i), fun i => ?_, ?_⟩
          · have h := hy i
            cases hxi : x i with
            | inl a =>
              rw [hxi] at h
              refine congrArg Sum.inl ?_
              change a = π.symm (y i)
              rw [← Sum.inl_injective h, Equiv.symm_apply_apply]
            | inr j =>
              rw [hxi] at h
              exact absurd h (by simp)
          · simpa only [Equiv.apply_symm_apply] using hr
        · rintro ⟨y, hy, hr⟩
          refine ⟨fun i => π (y i), fun i => ?_, hr⟩
          rw [hy i]
          rfl
      | inr s =>
        cases s
        rw [relMap_extAt_old, relMap_extAt_old]
        simp only [Function.comp_apply, hmap]
        cases x 0 <;> simp)

/-- **An `∃SO[new]` definition may be read with any junk value**: the extended
universe interpreting a function symbol on an invented argument through the
given element `z` rather than through `Classical.arbitrary`.

This is what makes the undefinability of `Classical.arbitrary A` harmless: the
junk element is not a feature of the problem, only of one presentation of the
extended universe. -/
theorem sigmaSONewDefinable_junk {P : DecisionProblem L} (h : SigmaSONewDefinable P) :
    ∃ (B : SOBlock) (φ : (soLang (newLang L) [B]).Sentence),
      ∀ (A : Type) [_inst : L.Structure A] [Finite A] [Nonempty A] (z : A),
        P A ↔ ∃ m : ℕ,
          @SORealize (newLang L) (A ⊕ Fin m) (extStructureAt L A m z) [B] φ true := by
  obtain ⟨B, φ, hφ⟩ := h
  refine ⟨B, φ, fun A inst _ _ z => ?_⟩
  classical
  set a₀ : A := Classical.arbitrary A with ha₀
  set π : A ≃ A := Equiv.swap a₀ z with hπ
  letI instπ : L.Structure A := transportStruct π inst
  have h1 : @DecisionProblem.Holds L P A instπ ↔ @DecisionProblem.Holds L P A inst :=
    @DecisionProblem.iso_invariant L P A A instπ inst (transportEquiv π inst)
  have h2 := @hφ A instπ ‹Finite A› ‹Nonempty A›
  refine (h1.symm.trans (h2.trans (exists_congr fun m => ?_)))
  have hiso := @sorealize_iso (newLang L) (A ⊕ Fin m) (A ⊕ Fin m)
    (@extStructureAt L A instπ m a₀) (@extStructureAt L A inst m (π a₀))
    (extIsoTransport π inst m a₀) [B] φ true
  rw [show π a₀ = z from Equiv.swap_apply_left a₀ z] at hiso
  exact hiso

end Junk

/-! ### The atomic diagram language

The relational vocabulary the source is moved to: one relation symbol of arity
`n` per atomic formula of `L` in `n` variables. Every structure carries one
canonically, and “this atomic formula holds of this tuple” is a first-order
property of the tuple, so the map is a one-dimensional interpretation. -/

section Atoms

variable {L : Language.{0, 0}}

/-- **The atomic diagram language**: a relation symbol of arity `n` for each
atom `r(t₁, …, t_l)` and each equality `t₁ = t₂` of `L` in `n` variables. -/
def atomLang (L : Language.{0, 0}) : Language.{0, 0} where
  Functions _ := Empty
  Relations n :=
    (Σ l : ℕ, L.Relations l × (Fin l → L.Term (Fin n))) ⊕ (L.Term (Fin n) × L.Term (Fin n))

instance atomLang_isRelational : (atomLang L).IsRelational := fun _ => ⟨fun e => e.elim⟩

/-- **The atomic diagram of a structure**: each symbol holds of the tuples
satisfying the atomic formula it names. -/
@[instance_reducible]
def atomStructure (L : Language.{0, 0}) (A : Type) [L.Structure A] :
    (atomLang L).Structure A where
  funMap f := isEmptyElim f
  RelMap {_n} R x :=
    match R with
    | Sum.inl ⟨_, r, ts⟩ => RelMap r fun j => (ts j).realize x
    | Sum.inr (t₁, t₂) => (t₁.realize x) = (t₂.realize x)

theorem relMap_atomStructure_rel {A : Type} [L.Structure A] {n l : ℕ} (r : L.Relations l)
    (ts : Fin l → L.Term (Fin n)) (x : Fin n → A) :
    @RelMap (atomLang L) A (atomStructure L A) n (Sum.inl ⟨l, r, ts⟩) x ↔
      RelMap r fun j => (ts j).realize x := Iff.rfl

theorem relMap_atomStructure_eq {A : Type} [L.Structure A] {n : ℕ}
    (t₁ t₂ : L.Term (Fin n)) (x : Fin n → A) :
    @RelMap (atomLang L) A (atomStructure L A) n (Sum.inr (t₁, t₂)) x ↔
      t₁.realize x = t₂.realize x := Iff.rfl

/-- The defining formula of a symbol of the atomic diagram language: the atomic
formula it names, read at the one-dimensional tuple. -/
def atomFml {n : ℕ} (R : (atomLang L).Relations n) : L.Formula (Fin n × Fin 1) :=
  match R with
  | Sum.inl ⟨_, r, ts⟩ => Relations.formula r fun j => (ts j).relabel fun i => (i, 0)
  | Sum.inr (t₁, t₂) =>
      Term.equal (t₁.relabel fun i => (i, 0)) (t₂.relabel fun i => (i, 0))

/-- **The atomic diagram, as a one-dimensional first-order interpretation.** -/
def atomInterp (L : Language.{0, 0}) : FOInterpretation L (atomLang L) Unit 1 where
  relFormula R _ := atomFml R

/-- What the defining formula of an atomic-diagram symbol says: the symbol
holds of the tuple. -/
theorem realize_atomFml {n : ℕ} (R : (atomLang L).Relations n) {A : Type} [L.Structure A]
    (v : Fin n × Fin 1 → A) :
    (atomFml R).Realize v ↔
      @RelMap (atomLang L) A (atomStructure L A) n R fun i => v (i, 0) := by
  classical
  cases R with
  | inl R₁ =>
    obtain ⟨l, r, ts⟩ := R₁
    change (Relations.formula r fun j => (ts j).relabel fun i => (i, 0)).Realize v ↔ _
    rw [Formula.realize_rel, relMap_atomStructure_rel]
    exact iff_of_eq (congrArg (RelMap r) (funext fun j => by rw [Term.realize_relabel]; rfl))
  | inr R₂ =>
    obtain ⟨t₁, t₂⟩ := R₂
    change (Term.equal (t₁.relabel fun i => (i, 0)) (t₂.relabel fun i => (i, 0))).Realize v ↔ _
    rw [Formula.realize_equal, relMap_atomStructure_eq, Term.realize_relabel,
      Term.realize_relabel]
    rfl

/-- **The interpreted structure is the atomic diagram**, through the equivalence
of a one-dimensional single-tag universe with its own carrier. -/
def atomMapEquiv (A : Type) [L.Structure A] :
    @Language.Equiv (atomLang L) ((atomInterp L).Map A) A
      (FOInterpretation.mapStructure (atomInterp L) A) (atomStructure L A) :=
  @Language.Equiv.mk (atomLang L) ((atomInterp L).Map A) A
    (FOInterpretation.mapStructure (atomInterp L) A) (atomStructure L A)
    ((atomInterp L).mapEquivSelf A)
    (fun {_n} f _ => isEmptyElim f)
    (fun {_n} R x => by
      rw [FOInterpretation.relMap_map]
      exact (realize_atomFml (A := A) R fun p => (x p.1).2 p.2).symm)

/-- **The relationalizing reduction**: any problem reduces, first-order, to a
problem over the atomic diagram language that agrees with it on the atomic
diagrams of finite structures. -/
def atomReduction (P : DecisionProblem L) (Q : DecisionProblem (atomLang L))
    (h : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ @DecisionProblem.Holds (atomLang L) Q A (atomStructure L A)) : P ≤ᶠᵒ Q where
  Tag := Unit
  dim := 1
  toInterpretation := atomInterp L
  correct A _ _ _ :=
    (h A).trans (@DecisionProblem.iso_invariant (atomLang L) Q ((atomInterp L).Map A) A
      (FOInterpretation.mapStructure (atomInterp L) A) (atomStructure L A)
      (atomMapEquiv A)).symm

end Atoms

/-! ### Blocks of existential quantifiers

The translation of an atom introduces a fixed number of fresh variables at the
*end* of the context, which is what makes it a purely local rewriting: nothing
already in the kernel is shifted. -/

section ExBlock

variable {L : Language.{0, 0}} {α M : Type} [L.Structure M]

/-- A block of `k` existential quantifiers. -/
def exs : ∀ {n : ℕ} (k : ℕ), L.BoundedFormula α (n + k) → L.BoundedFormula α n
  | _, 0, ψ => ψ
  | _, _ + 1, ψ => exs _ ψ.ex

/-- **What a block of existential quantifiers says**: the context is extended by
`k` values, the ones already there being kept. -/
theorem realize_exs :
    ∀ {n : ℕ} (k : ℕ) (ψ : L.BoundedFormula α (n + k)) (v : α → M) (xs : Fin n → M),
      (exs k ψ).Realize v xs ↔
        ∃ ys : Fin (n + k) → M, (∀ i : Fin n, ys (Fin.castAdd k i) = xs i) ∧ ψ.Realize v ys
  | _, 0, ψ, v, xs => by
      refine ⟨fun h => ⟨xs, fun i => congrArg xs (Fin.ext rfl), h⟩, ?_⟩
      rintro ⟨ys, hys, h⟩
      have : ys = xs := funext fun i => (congrArg ys (Fin.ext rfl)).symm.trans (hys _)
      rwa [this] at h
  | n, k + 1, ψ, v, xs => by
      rw [show exs (k + 1) ψ = exs k ψ.ex from rfl, realize_exs k ψ.ex v xs]
      simp only [BoundedFormula.realize_ex]
      constructor
      · rintro ⟨ys, hys, a, h⟩
        refine ⟨Fin.snoc ys a, fun i => ?_, h⟩
        rw [show (Fin.castAdd (k + 1) i : Fin (n + k + 1)) =
          Fin.castSucc (Fin.castAdd k i) from Fin.ext rfl, Fin.snoc_castSucc]
        exact hys i
      · rintro ⟨zs, hzs, h⟩
        refine ⟨zs ∘ Fin.castSucc, fun i => ?_, zs (Fin.last _), ?_⟩
        · exact (congrArg zs (Fin.ext rfl)).trans (hzs i)
        · exact cast (congrArg (fun w => ψ.Realize v w) (Fin.snoc_init_self zs)).symm h

end ExBlock

/-! ### The shadow of a term

The translation replaces a term by the value it takes; the point of the
construction is that this value is computed *in the instance*, on the tuple the
junk convention leaves behind. -/

section Shadow

variable {L : Language.{0, 0}} {B : SOBlock}

/-- The kernel language of an `∃SO[new]` definition. -/
abbrev srcLang (L : Language.{0, 0}) (B : SOBlock) : Language.{0, 0} := (newLang L).sum B.lang

/-- The block, extended by the unary relation variable naming the junk
element. -/
def jBlock (B : SOBlock) : SOBlock where
  ι := B.ι ⊕ Unit
  arity := Sum.elim B.arity fun _ => 1

/-- The kernel language the translation lands in: the atomic diagram language,
extended and expanded by the enlarged block. -/
abbrev tgtLang (L : Language.{0, 0}) (B : SOBlock) : Language.{0, 0} :=
  (newLang (atomLang L)).sum (jBlock B).lang

/-- **The `L`-term a term of the kernel language shadows**: neither the marker
nor the vocabulary of a block has function symbols, so every function
application is one of `L`. -/
def termDown {α : Type} : (srcLang L B).Term α → L.Term α
  | .var x => .var x
  | .func (Sum.inl (Sum.inl g)) ts => .func g fun j => termDown (ts j)
  | .func (Sum.inl (Sum.inr e)) _ => e.elim
  | .func (Sum.inr e) _ => e.elim

/-- The shadow of a term of the kernel, as an `L`-term in the context
variables: the index of a symbol of the atomic diagram language. -/
def termShadow {n : ℕ} (t : (srcLang L B).Term (Empty ⊕ Fin n)) : L.Term (Fin n) :=
  (termDown t).relabel (Sum.elim Empty.elim id)

variable {A : Type} [instA : L.Structure A] {m : ℕ}

theorem realize_termShadow {n : ℕ} (t : (srcLang L B).Term (Empty ⊕ Fin n))
    (v : Fin n → A) :
    (termShadow t).realize v = (termDown t).realize (Sum.elim isEmptyElim v) := by
  rw [termShadow, Term.realize_relabel]
  refine congrArg (fun u => Term.realize u (termDown t)) (funext ?_)
  rintro (e | i)
  · exact e.elim
  · rfl

/-- The structure a certificate puts on an extended universe: the instance with
its junk convention, expanded by the assignment of the block. -/
@[instance_reducible]
noncomputable def srcStruct (z : A) (μ : B.Assignment (A ⊕ Fin m)) :
    (srcLang L B).Structure (A ⊕ Fin m) :=
  @sumStructure (newLang L) B.lang (A ⊕ Fin m) (extStructureAt L A m z) (B.structure μ)

/-- **The value of a term, up to the junk convention**: forgetting which
invented values a term's value came from is computing its shadow in the
instance, on the context with the same forgetting applied. -/
theorem oldPartAt_realize (z : A) (μ : B.Assignment (A ⊕ Fin m)) :
    ∀ {α : Type} (t : (srcLang L B).Term α) (w : α → A ⊕ Fin m),
      oldPartAt A m z (@Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ w t) =
        (termDown t).realize fun i => oldPartAt A m z (w i) := by
  intro α t
  induction t with
  | var x => intro w; rfl
  | func f ts ih =>
    intro w
    cases f with
    | inr e => exact e.elim
    | inl f' =>
      cases f' with
      | inr e => exact e.elim
      | inl g =>
        change oldPartAt A m z (@funMap (newLang L) (A ⊕ Fin m) (extStructureAt L A m z) _
          (Sum.inl g) _) = _
        rw [funMap_extAt]
        exact congrArg (@funMap L A instA _ g) (funext fun j => ih j w)

/-- The value of a term that is a *function application* is an original
element: only a variable can take an invented value. -/
theorem realize_func_eq_inl (z : A) (μ : B.Assignment (A ⊕ Fin m)) {α : Type} {l : ℕ}
    (g : L.Functions l) (ts : Fin l → (srcLang L B).Term α) (w : α → A ⊕ Fin m) :
    @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ w
        (Term.func (Sum.inl (Sum.inl g)) ts) =
      Sum.inl ((termDown (L := L) (B := B) (Term.func (Sum.inl (Sum.inl g)) ts)).realize
        fun i => oldPartAt A m z (w i)) := by
  change @funMap (newLang L) (A ⊕ Fin m) (extStructureAt L A m z) _ (Sum.inl g) _ = _
  rw [funMap_extAt]
  refine congrArg Sum.inl (congrArg (@funMap L A instA _ g) (funext fun j => ?_))
  exact oldPartAt_realize z μ (ts j) w

end Shadow

/-! ### Finite conjunctions -/

section FinConj

variable {L : Language.{0, 0}} {α M : Type} [L.Structure M] {N : ℕ}

/-- The conjunction of finitely many bounded formulas. -/
def finConj : ∀ {p : ℕ}, (Fin p → L.BoundedFormula α N) → L.BoundedFormula α N
  | 0, _ => ⊤
  | _ + 1, f => f 0 ⊓ finConj fun j => f j.succ

theorem realize_finConj :
    ∀ {p : ℕ} (f : Fin p → L.BoundedFormula α N) (v : α → M) (xs : Fin N → M),
      (finConj f).Realize v xs ↔ ∀ j, (f j).Realize v xs
  | 0, f, v, xs => by
      simp only [finConj, BoundedFormula.realize_top, true_iff]
      exact fun j => j.elim0
  | p + 1, f, v, xs => by
      rw [show finConj f = f 0 ⊓ finConj fun j => f j.succ from rfl,
        BoundedFormula.realize_inf, realize_finConj (fun j => f j.succ) v xs]
      constructor
      · rintro ⟨h0, hs⟩ j
        refine Fin.cases ?_ ?_ j
        · exact h0
        · exact hs
      · intro h
        exact ⟨h 0, fun j => h j.succ⟩

end FinConj

/-! ### The translation

Each atom is rewritten **in place**: a block of `n + 1 + l` existentials at the
end of the context holds the coerced context, the guessed junk element and the
values of the `l` arguments, and the atom itself is then a symbol of the atomic
diagram language – or of the marker, or of the block – applied to those values.
`⊥`, `→` and `∀` are structural, so no de Bruijn index of the kernel moves. -/

section Flatten

variable {L : Language.{0, 0}} {B : SOBlock}

/-- A variable of the body of a translated atom. -/
def vr {N : ℕ} (i : Fin N) : (tgtLang L B).Term (Empty ⊕ Fin N) := Term.var (Sum.inr i)

variable (n l : ℕ)

/-- The `i`-th variable of the original context. -/
def xIdx (i : Fin n) : Fin (n + (n + 1 + l)) := Fin.castAdd _ i

/-- The `i`-th variable of the context, coerced to an original element. -/
def uIdx (i : Fin n) : Fin (n + (n + 1 + l)) := ⟨n + (i : ℕ), by have := i.isLt; omega⟩

/-- The guessed junk element. -/
def zIdx : Fin (n + (n + 1 + l)) := ⟨n + n, by omega⟩

/-- The value of the `j`-th argument of the atom. -/
def yIdx (j : Fin l) : Fin (n + (n + 1 + l)) := ⟨n + n + 1 + (j : ℕ), by have := j.isLt; omega⟩

/-- `old x`, in the target kernel language. -/
def oldOf {N : ℕ} (i : Fin N) : (tgtLang L B).BoundedFormula Empty N :=
  BoundedFormula.rel (Sum.inl (Sum.inr Language.oldSym)) ![vr i]

/-- The relation variable naming the junk element, applied to one variable. -/
def zOf {N : ℕ} (i : Fin N) : (tgtLang L B).BoundedFormula Empty N :=
  BoundedFormula.rel (Sum.inr ⟨Sum.inr (), rfl⟩) fun _ => vr i

/-- An equality of two variables. -/
def eqOf {N : ℕ} (a b : Fin N) : (tgtLang L B).BoundedFormula Empty N :=
  BoundedFormula.equal (vr a) (vr b)

/-- **The graph of a term, as a symbol of the atomic diagram language**: the
equality `t(x̄) = xₙ` in `n + 1` variables. -/
def graphSym (t : (srcLang L B).Term (Empty ⊕ Fin n)) : (atomLang L).Relations (n + 1) :=
  Sum.inr ((termShadow t).relabel Fin.castSucc, Term.var (Fin.last n))

/-- **What pins the value of one argument**: a variable takes the value the
context gives it – which may be an invented one – and a function application the
value its graph gives on the *coerced* context. -/
def argCl : (srcLang L B).Term (Empty ⊕ Fin n) → Fin l →
    (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l))
  | .var (Sum.inl e), _ => e.elim
  | .var (Sum.inr i), j => eqOf (yIdx n l j) (xIdx n l i)
  | .func f ts, j =>
      BoundedFormula.rel (Sum.inl (Sum.inl (graphSym n (Term.func f ts))))
        (Fin.snoc (fun i : Fin n => vr (uIdx n l i)) (vr (yIdx n l j)))

/-- The body of a translated atom. -/
def atomBody (ts : Fin l → (srcLang L B).Term (Empty ⊕ Fin n))
    (core : (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l))) :
    (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l)) :=
  zOf (zIdx n l) ⊓
    (finConj (fun i : Fin n =>
        (oldOf (xIdx n l i) ⟹ eqOf (uIdx n l i) (xIdx n l i)) ⊓
          (∼(oldOf (xIdx n l i)) ⟹ eqOf (uIdx n l i) (zIdx n l))) ⊓
      (finConj (fun j : Fin l => argCl n l (ts j) j) ⊓ core))

/-- **A translated atom.** -/
def flatAtom (ts : Fin l → (srcLang L B).Term (Empty ⊕ Fin n))
    (core : (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l))) :
    (tgtLang L B).BoundedFormula Empty n :=
  exs (n + 1 + l) (atomBody n l ts core)

variable {n l}

/-- **The translation of the kernel**: atom by atom, in place. -/
def flat : ∀ {n : ℕ}, (srcLang L B).BoundedFormula Empty n →
    (tgtLang L B).BoundedFormula Empty n
  | _, .falsum => .falsum
  | n, .equal t₁ t₂ => flatAtom n 2 ![t₁, t₂] (eqOf (yIdx n 2 0) (yIdx n 2 1))
  | n, .rel (l := l) R ts =>
      match R with
      | Sum.inl (Sum.inl r) =>
          flatAtom n l ts (BoundedFormula.rel
            (Sum.inl (Sum.inl (Sum.inl ⟨l, r, fun j => Term.var j⟩)))
            fun j => vr (yIdx n l j))
      | Sum.inl (Sum.inr o) =>
          match o with
          | .old => flatAtom n 1 ts (oldOf (yIdx n 1 0))
      | Sum.inr b =>
          flatAtom n l ts (BoundedFormula.rel (Sum.inr ⟨Sum.inl b.1, b.2⟩)
            fun j => vr (yIdx n l j))
  | _, .imp f₁ f₂ => (flat f₁).imp (flat f₂)
  | _, .all f => (flat f).all

/-! ### The intended values of the fresh variables -/

variable {A : Type} [instA : L.Structure A] [Nonempty A] {m : ℕ}

/-- The structure the translated kernel is read in: the atomic diagram,
extended, and expanded by the enlarged block. -/
@[instance_reducible]
noncomputable def tgtStruct (μ' : (jBlock B).Assignment (A ⊕ Fin m)) :
    (tgtLang L B).Structure (A ⊕ Fin m) :=
  @sumStructure (newLang (atomLang L)) (jBlock B).lang (A ⊕ Fin m)
    (@extStructure (atomLang L) A (atomStructure L A) _ m) ((jBlock B).structure μ')

/-- The enlarged assignment: the given one, plus the singleton naming the junk
element. -/
def jAssign (z : A) (μ : B.Assignment (A ⊕ Fin m)) : (jBlock B).Assignment (A ⊕ Fin m) :=
  fun i => match i with
    | Sum.inl b => μ b
    | Sum.inr _ => fun u => u ⟨0, Nat.zero_lt_one⟩ = Sum.inl z

open Classical in
/-- **The values the body of a translated atom forces on its fresh variables**:
the context is kept, the coerced context is the context with the invented values
replaced by the junk, and each argument variable holds the value of its term. -/
noncomputable def canonYs (z : A) (μ : B.Assignment (A ⊕ Fin m)) {n l : ℕ}
    (ts : Fin l → (srcLang L B).Term (Empty ⊕ Fin n)) (w : Fin n → A ⊕ Fin m) :
    Fin (n + (n + 1 + l)) → A ⊕ Fin m := fun p =>
  if h : (p : ℕ) < n then w ⟨(p : ℕ), h⟩
  else if h2 : (p : ℕ) < n + n then Sum.inl (oldPartAt A m z (w ⟨(p : ℕ) - n, by omega⟩))
  else if _h3 : (p : ℕ) = n + n then Sum.inl z
  else @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ (Sum.elim isEmptyElim w)
    (ts ⟨(p : ℕ) - (n + n + 1), by have := p.isLt; omega⟩)

variable (z : A) (μ : B.Assignment (A ⊕ Fin m)) {n l : ℕ}
variable (ts : Fin l → (srcLang L B).Term (Empty ⊕ Fin n)) (w : Fin n → A ⊕ Fin m)

omit [Nonempty A] in
theorem canonYs_x (i : Fin n) : canonYs z μ ts w (xIdx n l i) = w i := by
  classical
  have hv : ((xIdx n l i : Fin (n + (n + 1 + l))) : ℕ) = (i : ℕ) := rfl
  have hi := i.isLt
  simp only [canonYs]
  rw [dif_pos (by omega : ((xIdx n l i : Fin (n + (n + 1 + l))) : ℕ) < n)]
  refine congrArg w (Fin.ext ?_)
  change ((xIdx n l i : Fin (n + (n + 1 + l))) : ℕ) = (i : ℕ)
  omega

omit [Nonempty A] in
theorem canonYs_u (i : Fin n) :
    canonYs z μ ts w (uIdx n l i) = Sum.inl (oldPartAt A m z (w i)) := by
  classical
  have hv : ((uIdx n l i : Fin (n + (n + 1 + l))) : ℕ) = n + (i : ℕ) := rfl
  have hi := i.isLt
  simp only [canonYs]
  rw [dif_neg (by omega : ¬((uIdx n l i : Fin (n + (n + 1 + l))) : ℕ) < n),
    dif_pos (by omega : ((uIdx n l i : Fin (n + (n + 1 + l))) : ℕ) < n + n)]
  refine congrArg (fun a => Sum.inl (oldPartAt A m z (w a))) (Fin.ext ?_)
  change ((uIdx n l i : Fin (n + (n + 1 + l))) : ℕ) - n = (i : ℕ)
  omega

omit [Nonempty A] in
omit [Nonempty A] in
theorem canonYs_z : canonYs z μ ts w (zIdx n l) = Sum.inl z := by
  classical
  have hv : ((zIdx n l : Fin (n + (n + 1 + l))) : ℕ) = n + n := rfl
  simp only [canonYs]
  rw [dif_neg (by omega : ¬((zIdx n l : Fin (n + (n + 1 + l))) : ℕ) < n),
    dif_neg (by omega : ¬((zIdx n l : Fin (n + (n + 1 + l))) : ℕ) < n + n),
    dif_pos hv]

omit [Nonempty A] in
theorem canonYs_y (j : Fin l) :
    canonYs z μ ts w (yIdx n l j) =
      @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ (Sum.elim isEmptyElim w)
        (ts j) := by
  classical
  have hv : ((yIdx n l j : Fin (n + (n + 1 + l))) : ℕ) = n + n + 1 + (j : ℕ) := rfl
  simp only [canonYs]
  rw [dif_neg (by omega : ¬((yIdx n l j : Fin (n + (n + 1 + l))) : ℕ) < n),
    dif_neg (by omega : ¬((yIdx n l j : Fin (n + (n + 1 + l))) : ℕ) < n + n),
    dif_neg (by omega : ¬((yIdx n l j : Fin (n + (n + 1 + l))) : ℕ) = n + n)]
  refine congrArg (fun a => @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _
    (Sum.elim isEmptyElim w) (ts a)) (Fin.ext ?_)
  change ((yIdx n l j : Fin (n + (n + 1 + l))) : ℕ) - (n + n + 1) = (j : ℕ)
  omega

omit [L.Structure A] [Nonempty A] in
/-- The four families of indices exhaust the body's context. -/
theorem idx_cases (p : Fin (n + (n + 1 + l))) :
    (∃ i : Fin n, p = xIdx n l i) ∨ (∃ i : Fin n, p = uIdx n l i) ∨
      p = zIdx n l ∨ ∃ j : Fin l, p = yIdx n l j := by
  have hp := p.isLt
  by_cases h : (p : ℕ) < n
  · exact Or.inl ⟨⟨(p : ℕ), h⟩, Fin.ext rfl⟩
  by_cases h2 : (p : ℕ) < n + n
  · refine Or.inr (Or.inl ⟨⟨(p : ℕ) - n, by omega⟩, Fin.ext ?_⟩)
    change (p : ℕ) = n + ((p : ℕ) - n)
    omega
  by_cases h3 : (p : ℕ) = n + n
  · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
    change (p : ℕ) = n + n
    omega
  · refine Or.inr (Or.inr (Or.inr ⟨⟨(p : ℕ) - (n + n + 1), by omega⟩, Fin.ext ?_⟩))
    change (p : ℕ) = n + n + 1 + ((p : ℕ) - (n + n + 1))
    omega

/-! ### What the body of a translated atom says -/

theorem realize_zOf' {N : ℕ} (i : Fin N) (ys : Fin N → A ⊕ Fin m)
    (μ' : (jBlock B).Assignment (A ⊕ Fin m)) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _
      (zOf i) isEmptyElim ys ↔ μ' (Sum.inr ()) (fun _ => ys i) := Iff.rfl

theorem realize_zOf {N : ℕ} (i : Fin N) (ys : Fin N → A ⊕ Fin m) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
      (zOf i) isEmptyElim ys ↔ ys i = Sum.inl z := Iff.rfl

theorem realize_oldOf {N : ℕ} (i : Fin N) (ys : Fin N → A ⊕ Fin m)
    (μ' : (jBlock B).Assignment (A ⊕ Fin m)) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _
      (oldOf i) isEmptyElim ys ↔ IsOld (ys i) := Iff.rfl

theorem realize_eqOf {N : ℕ} (a b : Fin N) (ys : Fin N → A ⊕ Fin m)
    (μ' : (jBlock B).Assignment (A ⊕ Fin m)) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _
      (eqOf a b) isEmptyElim ys ↔ ys a = ys b := Iff.rfl

theorem realize_argCl_var (i : Fin n) (j : Fin l)
    (ys : Fin (n + (n + 1 + l)) → A ⊕ Fin m) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (argCl n l (Term.var (Sum.inr i)) j) isEmptyElim ys ↔
      ys (yIdx n l j) = ys (xIdx n l i) := Iff.rfl

theorem realize_argCl_func {k : ℕ} (g : L.Functions k)
    (ts' : Fin k → (srcLang L B).Term (Empty ⊕ Fin n)) (j : Fin l)
    (ys : Fin (n + (n + 1 + l)) → A ⊕ Fin m) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (argCl n l (Term.func (Sum.inl (Sum.inl g)) ts') j) isEmptyElim ys ↔
      ∃ y : Fin (n + 1) → A,
        (∀ i : Fin n, ys (uIdx n l i) = Sum.inl (y (Fin.castSucc i))) ∧
          ys (yIdx n l j) = Sum.inl (y (Fin.last n)) ∧
            (termShadow (Term.func (Sum.inl (Sum.inl g)) ts')).realize
              (fun i => y (Fin.castSucc i)) = y (Fin.last n) := by
  have hargs : ∀ k' : Fin (n + 1),
      @Term.realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _
          (Sum.elim isEmptyElim ys)
          (Fin.snoc (α := fun _ => (tgtLang L B).Term (Empty ⊕ Fin (n + (n + 1 + l))))
            (fun i : Fin n => vr (uIdx n l i)) (vr (yIdx n l j)) k') =
        Fin.snoc (α := fun _ => A ⊕ Fin m) (fun i : Fin n => ys (uIdx n l i))
          (ys (yIdx n l j)) k' := by
    intro k'
    refine Fin.lastCases ?_ ?_ k'
    · rw [Fin.snoc_last, Fin.snoc_last]; rfl
    · intro i; rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  refine Iff.trans Iff.rfl (exists_congr fun y => ?_)
  constructor
  · rintro ⟨hy, hr⟩
    simp only [hargs] at hy
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have h := hy (Fin.castSucc i)
      rwa [Fin.snoc_castSucc] at h
    · have h := hy (Fin.last n)
      rwa [Fin.snoc_last] at h
    · exact (Term.realize_relabel).symm.trans hr
  · rintro ⟨hu, hlast, hr⟩
    refine ⟨fun k' => ?_, (Term.realize_relabel).trans hr⟩
    simp only [hargs]
    refine Fin.lastCases ?_ ?_ k'
    · rw [Fin.snoc_last]; exact hlast
    · intro i; rw [Fin.snoc_castSucc]; exact hu i

/-- The coerced context, as a tuple of the instance. -/
def ubar : Fin n → A := fun i => oldPartAt A m z (w i)

omit [Nonempty A] in
theorem elim_ubar :
    (fun x : Empty ⊕ Fin n => oldPartAt A m z (Sum.elim isEmptyElim w x)) =
      Sum.elim isEmptyElim (ubar z w) := by
  funext x
  rcases x with e | i
  · exact e.elim
  · rfl

omit [Nonempty A] in
/-- **The value of a term is its shadow's, on the coerced context.** -/
theorem realize_termShadow_ubar (t : (srcLang L B).Term (Empty ⊕ Fin n)) :
    (termShadow t).realize (ubar z w) =
      oldPartAt A m z (@Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _
        (Sum.elim isEmptyElim w) t) := by
  rw [realize_termShadow, oldPartAt_realize z μ t (Sum.elim isEmptyElim w), elim_ubar]

omit [Nonempty A] in
/-- A term that is a function application takes the value its shadow names. -/
theorem realize_eq_inl_shadow {k : ℕ} (g : L.Functions k)
    (ts' : Fin k → (srcLang L B).Term (Empty ⊕ Fin n)) :
    @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ (Sum.elim isEmptyElim w)
        (Term.func (Sum.inl (Sum.inl g)) ts') =
      Sum.inl ((termShadow (Term.func (Sum.inl (Sum.inl g)) ts')).realize (ubar z w)) := by
  rw [realize_termShadow_ubar z μ w, realize_func_eq_inl z μ g ts' (Sum.elim isEmptyElim w)]
  rfl

/-- **What an argument clause says**, once the coerced context is known: the
argument variable holds the value of its term. -/
theorem realize_argCl_iff (t : (srcLang L B).Term (Empty ⊕ Fin n)) (j : Fin l)
    (ys : Fin (n + (n + 1 + l)) → A ⊕ Fin m) (hys : ∀ i, ys (xIdx n l i) = w i)
    (hu : ∀ i, ys (uIdx n l i) = Sum.inl (ubar z w i)) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (argCl n l t j) isEmptyElim ys ↔
      ys (yIdx n l j) = @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _
        (Sum.elim isEmptyElim w) t := by
  cases t with
  | var x =>
    cases x with
    | inl e => exact e.elim
    | inr i =>
      rw [realize_argCl_var z μ i j ys, hys i]
      exact Iff.rfl
  | func f ts' =>
    cases f with
    | inr e => exact e.elim
    | inl f' =>
      cases f' with
      | inr e => exact e.elim
      | inl g =>
        rw [realize_argCl_func z μ g ts' j ys, realize_eq_inl_shadow z μ w g ts']
        constructor
        · rintro ⟨y, hy, hlast, hr⟩
          have hyc : (fun i => y (Fin.castSucc i)) = ubar z w := by
            funext i
            exact (Sum.inl_injective ((hu i).symm.trans (hy i))).symm
          rw [hlast, ← hr, hyc]
        · intro h
          refine ⟨Fin.snoc (α := fun _ => A) (ubar z w)
            ((termShadow (Term.func (Sum.inl (Sum.inl g)) ts')).realize (ubar z w)),
            fun i => ?_, ?_, ?_⟩
          · rw [Fin.snoc_castSucc]; exact hu i
          · rw [Fin.snoc_last]; exact h
          · rw [Fin.snoc_last]
            refine congrArg (fun v => Term.realize v
              (termShadow (Term.func (Sum.inl (Sum.inl g)) ts'))) (funext fun i => ?_)
            exact Fin.snoc_castSucc _ _ i

omit [Nonempty A] in
theorem inl_oldPartAt_of_isOld {x : A ⊕ Fin m} (h : IsOld x) :
    Sum.inl (oldPartAt A m z x) = x := by
  obtain ⟨a, rfl⟩ := isOld_iff.mp h
  rfl

omit [Nonempty A] in
theorem inl_oldPartAt_of_not {x : A ⊕ Fin m} (h : ¬IsOld x) :
    (Sum.inl (oldPartAt A m z x) : A ⊕ Fin m) = Sum.inl z := by
  cases x with
  | inl a => exact absurd (isOld_inl a) h
  | inr j => rfl

/-- **What the body of a translated atom says**, conjunct by conjunct. -/
theorem realize_atomBody (core : (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l)))
    (ys : Fin (n + (n + 1 + l)) → A ⊕ Fin m) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (atomBody n l ts core) isEmptyElim ys ↔
      ys (zIdx n l) = Sum.inl z ∧
        (∀ i : Fin n, (IsOld (ys (xIdx n l i)) → ys (uIdx n l i) = ys (xIdx n l i)) ∧
            (¬IsOld (ys (xIdx n l i)) → ys (uIdx n l i) = ys (zIdx n l))) ∧
          (∀ j : Fin l, @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m)
              (tgtStruct (jAssign z μ)) _ _ (argCl n l (ts j) j) isEmptyElim ys) ∧
            @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
              core isEmptyElim ys := by
  rw [atomBody]
  simp only [BoundedFormula.realize_inf, realize_finConj, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, realize_zOf, realize_oldOf, realize_eqOf]

/-- **A translated atom is its core, read at the values the body forces**: the
existential block is determined, so nothing is really guessed. -/
theorem realize_flatAtom (core : (tgtLang L B).BoundedFormula Empty (n + (n + 1 + l))) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (flatAtom n l ts core) isEmptyElim w ↔
      @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        core isEmptyElim (canonYs z μ ts w) := by
  letI : (tgtLang L B).Structure (A ⊕ Fin m) := tgtStruct (jAssign z μ)
  rw [flatAtom, realize_exs]
  constructor
  · rintro ⟨ys, hys, hbody⟩
    rw [realize_atomBody] at hbody
    obtain ⟨hz, hc, ha, hcore⟩ := hbody
    have hxs : ∀ i, ys (xIdx n l i) = w i := fun i => hys i
    have hu : ∀ i, ys (uIdx n l i) = Sum.inl (ubar z w i) := by
      intro i
      by_cases hold : IsOld (w i)
      · rw [(hc i).1 (by rw [hxs i]; exact hold), hxs i]
        exact (inl_oldPartAt_of_isOld z hold).symm
      · rw [(hc i).2 (by rw [hxs i]; exact hold), hz]
        exact (inl_oldPartAt_of_not z hold).symm
    have hy : ∀ j, ys (yIdx n l j) =
        @Term.realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _
          (Sum.elim isEmptyElim w) (ts j) :=
      fun j => (realize_argCl_iff z μ w (ts j) j ys hxs hu).mp (ha j)
    have heq : ys = canonYs z μ ts w := by
      funext p
      rcases idx_cases p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
      · rw [hxs i, canonYs_x]
      · rw [hu i, canonYs_u]; rfl
      · rw [hz, canonYs_z]
      · rw [hy j, canonYs_y]
    rwa [heq] at hcore
  · intro hcore
    refine ⟨canonYs z μ ts w, fun i => canonYs_x z μ ts w i, ?_⟩
    rw [realize_atomBody]
    refine ⟨canonYs_z z μ ts w, fun i => ?_, fun j => ?_, hcore⟩
    · rw [canonYs_x, canonYs_u, canonYs_z]
      exact ⟨fun hold => inl_oldPartAt_of_isOld z hold,
        fun hnold => inl_oldPartAt_of_not z hnold⟩
    · exact (realize_argCl_iff z μ w (ts j) j _ (fun i => canonYs_x z μ ts w i)
        (fun i => canonYs_u z μ ts w i)).mpr (canonYs_y z μ ts w j)

/-! ### The translation is correct -/

/-- The core of a translated atom of the instance's vocabulary: the symbol of
the atomic diagram language naming that atom, at the values of the arguments. -/
theorem realize_core_input (r : L.Relations l) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (BoundedFormula.rel (Sum.inl (Sum.inl (Sum.inl ⟨l, r, fun j => Term.var j⟩)))
          fun j => vr (yIdx n l j)) isEmptyElim (canonYs z μ ts w) ↔
      @BoundedFormula.Realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ _
        (BoundedFormula.rel (Sum.inl (Sum.inl r)) ts) isEmptyElim w := by
  refine exists_congr fun y => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => (canonYs_y z μ ts w j).symm.trans (h1 j), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => (canonYs_y z μ ts w j).trans (h1 j), h2⟩

/-- The core of a translated atom of a relation variable: the same variable of
the enlarged block, at the values of the arguments. -/
theorem realize_core_block (b : B.lang.Relations l) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
        (BoundedFormula.rel (Sum.inr ⟨Sum.inl b.1, b.2⟩) fun j => vr (yIdx n l j))
        isEmptyElim (canonYs z μ ts w) ↔
      @BoundedFormula.Realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ _
        (BoundedFormula.rel (Sum.inr b) ts) isEmptyElim w :=
  iff_of_eq (congrArg (μ b.1) (funext fun j => canonYs_y z μ ts w (Fin.cast b.2 j)))

variable {z μ}

/-- **The translated kernel says of the atomic diagram what the kernel says of
the instance**: the two structures share a carrier, and the translation only
replaces each atom by the symbol of the atomic diagram language that names
it. -/
theorem realize_flat :
    ∀ {n : ℕ} (f : (srcLang L B).BoundedFormula Empty n) (w : Fin n → A ⊕ Fin m),
      @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct (jAssign z μ)) _ _
          (flat f) isEmptyElim w ↔
        @BoundedFormula.Realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ _
          f isEmptyElim w
  | _, .falsum, _ => Iff.rfl
  | n, .equal t₁ t₂, w => by
      have h1 := realize_flatAtom (z := z) (μ := μ) (ts := ![t₁, t₂]) (w := w)
        (core := eqOf (yIdx n 2 0) (yIdx n 2 1))
      rw [show flat (BoundedFormula.equal t₁ t₂) =
        flatAtom n 2 ![t₁, t₂] (eqOf (yIdx n 2 0) (yIdx n 2 1)) from rfl, h1, realize_eqOf]
      simp only [canonYs_y, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact Iff.rfl
  | n, .rel (l := l) R ts, w => by
      cases R with
      | inl R' =>
        cases R' with
        | inl r =>
          have h1 := realize_flatAtom (z := z) (μ := μ) (ts := ts) (w := w)
            (core := BoundedFormula.rel
              (Sum.inl (Sum.inl (Sum.inl ⟨l, r, fun j => Term.var j⟩)))
              fun j => vr (yIdx n l j))
          rw [show flat (BoundedFormula.rel (Sum.inl (Sum.inl r)) ts) =
            flatAtom n l ts (BoundedFormula.rel
              (Sum.inl (Sum.inl (Sum.inl ⟨l, r, fun j => Term.var j⟩)))
              fun j => vr (yIdx n l j)) from rfl, h1]
          exact realize_core_input z μ ts w r
        | inr o =>
          cases o
          have h1 := realize_flatAtom (z := z) (μ := μ) (ts := ts) (w := w)
            (core := oldOf (yIdx n 1 0))
          rw [show flat (BoundedFormula.rel (Sum.inl (Sum.inr Language.oldSym)) ts) =
            flatAtom n 1 ts (oldOf (yIdx n 1 0)) from rfl, h1, realize_oldOf]
          simp only [canonYs_y]
          exact Iff.rfl
      | inr b =>
        have h1 := realize_flatAtom (z := z) (μ := μ) (ts := ts) (w := w)
          (core := BoundedFormula.rel (Sum.inr ⟨Sum.inl b.1, b.2⟩) fun j => vr (yIdx n l j))
        rw [show flat (BoundedFormula.rel (Sum.inr b) ts) =
          flatAtom n l ts (BoundedFormula.rel (Sum.inr ⟨Sum.inl b.1, b.2⟩)
            fun j => vr (yIdx n l j)) from rfl, h1]
        exact realize_core_block z μ ts w b
  | _, .imp f₁ f₂, w => by
      rw [show flat (f₁.imp f₂) = (flat f₁).imp (flat f₂) from rfl]
      exact imp_congr (realize_flat f₁ w) (realize_flat f₂ w)
  | _, .all f, w => by
      rw [show flat f.all = (flat f).all from rfl]
      exact forall_congr' fun x => realize_flat f (Fin.snoc w x)

/-! ### The relational problem, and the reduction to it -/

variable (B)

/-- The junk element is a *single* original element: what makes the guesses of
the individual atoms agree. -/
def zSingle : (tgtLang L B).Sentence :=
  (BoundedFormula.ex (zOf (0 : Fin 1) ⊓ oldOf (0 : Fin 1))) ⊓
    BoundedFormula.all (BoundedFormula.all
      (zOf (0 : Fin 2) ⟹ (zOf (1 : Fin 2) ⟹ eqOf (0 : Fin 2) (1 : Fin 2))))

/-- **The translated kernel**: the junk element, and the translation of the
original kernel. -/
def relKernel (φ : (srcLang L B).Sentence) : (tgtLang L B).Sentence := zSingle B ⊓ flat φ

variable {B}

theorem realize_zSingle (μ' : (jBlock B).Assignment (A ⊕ Fin m))
    (xs : Fin 0 → A ⊕ Fin m) :
    @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _
        (zSingle B) isEmptyElim xs ↔
      ∃ z : A, ∀ u : A ⊕ Fin m, μ' (Sum.inr ()) (fun _ => u) ↔ u = Sum.inl z := by
  have e1 : ∀ u : A ⊕ Fin m, (Fin.snoc xs u : Fin 1 → A ⊕ Fin m) 0 = u := fun _ => rfl
  have e2 : ∀ a b : A ⊕ Fin m, (Fin.snoc (Fin.snoc xs a) b : Fin 2 → A ⊕ Fin m) 0 = a :=
    fun _ _ => rfl
  have e3 : ∀ a b : A ⊕ Fin m, (Fin.snoc (Fin.snoc xs a) b : Fin 2 → A ⊕ Fin m) 1 = b :=
    fun _ _ => rfl
  rw [zSingle]
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, realize_zOf', realize_oldOf, realize_eqOf, e1, e2, e3]
  constructor
  · rintro ⟨⟨c, hc, hold⟩, huniq⟩
    obtain ⟨z, rfl⟩ := isOld_iff.mp hold
    exact ⟨z, fun u => ⟨fun hu => huniq u (Sum.inl z) hu hc, fun hu => hu ▸ hc⟩⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨Sum.inl z, (hz (Sum.inl z)).mpr rfl, isOld_inl z⟩,
      fun a b ha hb => ((hz a).mp ha).trans ((hz b).mp hb).symm⟩

/-! ### The relational problem, and the reduction to it -/

omit [Nonempty A] instA in
theorem funs_one {M : Type} (u : Fin ((jBlock B).arity (Sum.inr ())) → M) :
    u = fun _ => u ⟨0, Nat.zero_lt_one⟩ := by
  funext j
  have hj : (j : ℕ) < 1 := j.isLt
  refine congrArg u (Fin.ext ?_)
  change (j : ℕ) = 0
  omega

variable (B)

omit [Nonempty A] in
theorem sorealize_src_iff (φ : (srcLang L B).Sentence) (z : A) (m : ℕ) :
    @SORealize (newLang L) (A ⊕ Fin m) (extStructureAt L A m z) [B] φ true ↔
      ∃ μ : B.Assignment (A ⊕ Fin m),
        @BoundedFormula.Realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ _ φ
          isEmptyElim finZeroElim :=
  exists_congr fun μ => iff_of_eq (congrArg₂
    (fun (v : Empty → A ⊕ Fin m) (xs : Fin 0 → A ⊕ Fin m) =>
      @BoundedFormula.Realize (srcLang L B) (A ⊕ Fin m) (srcStruct z μ) _ _ φ v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem sorealize_tgt_iff (ψ : (tgtLang L B).Sentence) (m : ℕ) :
    @SORealize (newLang (atomLang L)) (A ⊕ Fin m)
        (@extStructure (atomLang L) A (atomStructure L A) _ m) [jBlock B] ψ true ↔
      ∃ μ' : (jBlock B).Assignment (A ⊕ Fin m),
        @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _ ψ
          isEmptyElim finZeroElim :=
  exists_congr fun μ' => iff_of_eq (congrArg₂
    (fun (v : Empty → A ⊕ Fin m) (xs : Fin 0 → A ⊕ Fin m) =>
      @BoundedFormula.Realize (tgtLang L B) (A ⊕ Fin m) (tgtStruct μ') _ _ ψ v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- **The relational reading of an `∃SO[new]` definition**: the same definition
over the atomic diagram language, with the junk element guessed by one more
relation variable. -/
def relHolds (B : SOBlock) (φ : (srcLang L B).Sentence) (A' : Type)
    [(atomLang L).Structure A'] : Prop :=
  ∃ (hne : Nonempty A') (m : ℕ),
    @SORealize (newLang (atomLang L)) (A' ⊕ Fin m)
      (@extStructure (atomLang L) A' _ hne m) [jBlock B] (relKernel B φ) true

/-- It is a decision problem: `∃SO[new]` sentences are isomorphism-invariant. -/
def relProblem (B : SOBlock) (φ : (srcLang L B).Sentence) : DecisionProblem (atomLang L) where
  Holds A' _ := relHolds B φ A'
  iso_invariant {A₁ A₂} _ _ e := by
    classical
    constructor
    · rintro ⟨hne, m, hm⟩
      haveI := hne
      haveI hne₂ : Nonempty A₂ := ⟨e (Classical.arbitrary A₁)⟩
      exact ⟨hne₂, m, (sorealize_new_iso e (jBlock B) (relKernel B φ) m).mp hm⟩
    · rintro ⟨hne, m, hm⟩
      haveI := hne
      haveI hne₁ : Nonempty A₁ := ⟨e.symm (Classical.arbitrary A₂)⟩
      exact ⟨hne₁, m, (sorealize_new_iso e (jBlock B) (relKernel B φ) m).mpr hm⟩

theorem sigmaSONewDefinable_relProblem (φ : (srcLang L B).Sentence) :
    SigmaSONewDefinable (relProblem B φ) :=
  ⟨jBlock B, relKernel B φ, fun _ _ _ _ =>
    ⟨fun h => ⟨h.choose_spec.choose, h.choose_spec.choose_spec⟩,
      fun ⟨m, h⟩ => ⟨inferInstance, m, h⟩⟩⟩

variable {B}

/-- **The relational reading agrees with the original on atomic diagrams.** -/
theorem relProblem_iff {P : DecisionProblem L} (φ : (srcLang L B).Sentence)
    (hφ : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A] (z : A),
      P A ↔ ∃ m : ℕ, @SORealize (newLang L) (A ⊕ Fin m) (extStructureAt L A m z) [B] φ true)
    [Finite A] :
    P A ↔ @DecisionProblem.Holds (atomLang L) (relProblem B φ) A (atomStructure L A) := by
  classical
  constructor
  · intro hP
    obtain ⟨m, hm⟩ := (hφ A (Classical.arbitrary A)).mp hP
    obtain ⟨μ, hμ⟩ := (sorealize_src_iff B φ (Classical.arbitrary A) m).mp hm
    letI : (tgtLang L B).Structure (A ⊕ Fin m) := tgtStruct (jAssign (Classical.arbitrary A) μ)
    refine ⟨inferInstance, m, (sorealize_tgt_iff B (relKernel B φ) m).mpr
      ⟨jAssign (Classical.arbitrary A) μ, ?_⟩⟩
    rw [relKernel, BoundedFormula.realize_inf]
    exact ⟨(realize_zSingle _ _).mpr ⟨Classical.arbitrary A, fun _ => Iff.rfl⟩,
      (realize_flat φ finZeroElim).mpr hμ⟩
  · rintro ⟨hne, m, hm⟩
    obtain ⟨μ', hb⟩ := (sorealize_tgt_iff B (relKernel B φ) m).mp hm
    letI : (tgtLang L B).Structure (A ⊕ Fin m) := tgtStruct μ'
    rw [relKernel, BoundedFormula.realize_inf] at hb
    obtain ⟨hz, hf⟩ := hb
    obtain ⟨z, hzc⟩ := (realize_zSingle μ' _).mp hz
    have hμ' : μ' = jAssign z fun b => μ' (Sum.inl b) := by
      funext i
      cases i with
      | inl b => rfl
      | inr t =>
        cases t
        funext u
        refine propext ?_
        rw [funs_one u]
        exact hzc (u ⟨0, Nat.zero_lt_one⟩)
    rw [hμ'] at hf
    exact (hφ A z).mpr ⟨m, (sorealize_src_iff B φ z m).mpr
      ⟨_, (realize_flat φ finZeroElim).mp hf⟩⟩

end Flatten

/-! ### The theorem -/

/-- **Every `∃SO[new]`-definable problem admits a first-order reduction to an
`∃SO[new]`-definable problem over a relational vocabulary.**

The relational vocabulary is the atomic diagram language
`DescriptiveComplexity.atomLang`, and the reduction is the identity on the
carrier: only the vocabulary changes, an atomic formula of the source becoming a
relation symbol of the target. The kernel of the definition is carried across by
`DescriptiveComplexity.flat`, and what makes that possible is that the junk
element of the extended universe may be *guessed*
(`DescriptiveComplexity.sigmaSONewDefinable_junk`).

Composed with a hardness result proved for relational sources, this gives the
hardness result for all of them, which is what
`DescriptiveComplexity.CofinalHard` asks for. -/
theorem exists_relational_of_sigmaSONewDefinable {L : Language.{0, 0}}
    {P : DecisionProblem L} (h : SigmaSONewDefinable P) :
    ∃ (L' : Language.{0, 0}) (hrel : L'.IsRelational) (Q : DecisionProblem L'),
      SigmaSONewDefinable Q ∧ Nonempty (@FOReduction L L' hrel P Q) := by
  obtain ⟨B, φ, hφ⟩ := sigmaSONewDefinable_junk h
  exact ⟨atomLang L, atomLang_isRelational, relProblem B φ,
    sigmaSONewDefinable_relProblem B φ,
    ⟨atomReduction P (relProblem B φ) fun A _ _ _ => relProblem_iff φ hφ⟩⟩

end DescriptiveComplexity
