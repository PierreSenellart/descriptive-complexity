/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.ArithmeticDefinable

/-!
# Arithmetically definable relations: AC⁰ definability with free variables

`DescriptiveComplexity.AC0Definable` is a statement about *sentences*, and a
sentence is an awkward thing to build by hand: every construction carries its
own variable bookkeeping through `FirstOrder.Language.Formula.iExs` and
`Sum.elim`. This file does that bookkeeping once, and then never again:
`DescriptiveComplexity.ArithDef` says that a *family* of relations on
valuations – one relation for every nonempty finite ordered structure – is
realized by a single formula of the arithmetic expansion, and the lemmas below
close the notion under the Boolean connectives and under quantification.

Everything downstream is then semantic. A construction states what its relation
*means* on ranks, chains the closure lemmas, and reads the sentence off at the
end with `DescriptiveComplexity.ArithDef.ac0Definable`; no formula is ever
inspected again.

## Conventions

Variables are indexed by an arbitrary type `α`, as `Formula α` is, and a
quantifier binds the variables of `Fin 1` in `α ⊕ Fin 1`
(`DescriptiveComplexity.ArithDef.ex`, `DescriptiveComplexity.ArithDef.all`) –
the layout of `FirstOrder.Language.Formula.iExs`, so that no relabelling is
needed at the quantifier step. Moving between variable layouts is
`DescriptiveComplexity.ArithDef.relabel`, and a relation with *no* free
variables (`α = Empty`) is literally a sentence, which is what
`DescriptiveComplexity.ArithDef.ac0Definable` reads.

## The three groups of lemmas

* **Atoms** – the order, the two numeric predicates, equality, and an input
  relation read at a tuple of variables
  (`DescriptiveComplexity.arithDef_le`, `_plus`, `_times`, `_eq`, `_rel`).
* **Connectives** – negation, conjunction, disjunction, implication, and the
  two constants.
* **Quantifiers** – `DescriptiveComplexity.ArithDef.ex` and
  `DescriptiveComplexity.ArithDef.all`, together with the vector forms
  `DescriptiveComplexity.ArithDef.exs` and `DescriptiveComplexity.ArithDef.alls`
  binding a whole `Fin k` of variables at once.

A `DescriptiveComplexity.ArithDef.congr` lemma lets a relation be replaced by a
pointwise-equivalent one, which is how a semantic reformulation – the shape most
proofs actually want – is fed to the closure lemmas.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {α β : Type}

/-! ### Relations on valuations of a finite ordered structure -/

/-- A **family of relations** on `α`-indexed valuations: one relation for every
nonempty finite ordered `L`-structure. The instance arguments are those of
`DescriptiveComplexity.AC0Definable`, since that is what the family is
eventually read as. -/
abbrev ArithRel (L : Language.{0, 0}) (α : Type) : Type 1 :=
  ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], (α → A) → Prop

/-- A family of relations is **arithmetically definable** when one formula of
the arithmetic expansion realizes it in every nonempty finite ordered
structure – first-order logic with `≤`, `+` and `×` on the ranks, with free
variables indexed by `α`. -/
def ArithDef (R : ArithRel L α) : Prop :=
  ∃ φ : (L.sum Language.arith).Formula α,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ φ.Realize v

namespace ArithDef

/-- Definability transfers along a pointwise equivalence of relations: the
formula is unchanged, only the semantic reading of it is. -/
theorem congr {R S : ArithRel L α} (h : ArithDef R)
    (he : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ S A v) : ArithDef S := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun A _ _ _ _ v => (he A v).symm.trans (hφ A v)⟩

/-- **Renaming the free variables**: a definable relation read through a
substitution of variables is definable. -/
theorem relabel {R : ArithRel L α} (h : ArithDef R) (f : α → β) :
    ArithDef (L := L) (α := β) (fun A _ _ _ _ v => R A (v ∘ f)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.relabel f, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_relabel]
  exact hφ A _

/-! ### Connectives -/

/-- The negation of a definable relation is definable. -/
theorem not {R : ArithRel L α} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ¬ R A v) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨∼φ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_not]
  exact not_congr (hφ A v)

/-- The conjunction of two definable relations is definable. -/
theorem and {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v ∧ S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ ⊓ ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_inf]
  exact and_congr (hφ A v) (hψ A v)

/-- The disjunction of two definable relations is definable. -/
theorem or {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v ∨ S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ ⊔ ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_sup]
  exact or_congr (hφ A v) (hψ A v)

/-- An implication between definable relations is definable. -/
theorem imp {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => R A v → S A v) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ.imp ψ, fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_imp]
  exact imp_congr (hφ A v) (hψ A v)

/-- An equivalence between definable relations is definable. -/
theorem iff {R S : ArithRel L α} (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => (R A v ↔ S A v)) :=
  ((h.imp h').and (h'.imp h)).congr fun _A _ _ _ _ _v =>
    ⟨fun hc => ⟨hc.1, hc.2⟩, fun hc => ⟨hc.mp, hc.mpr⟩⟩

/-- The always-true relation is definable. -/
theorem top : ArithDef (L := L) (α := α) (fun _ _ _ _ _ _ => True) :=
  ⟨⊤, fun A _ _ _ _ v => by simp⟩

/-- The always-false relation is definable. -/
theorem bot : ArithDef (L := L) (α := α) (fun _ _ _ _ _ _ => False) :=
  ⟨⊥, fun A _ _ _ _ v => by simp⟩

/-- A case distinction made outside the structure – a condition on the
*machine*, not on the instance – is definable when both branches are. -/
theorem ite {R S : ArithRel L α} (c : Prop) [Decidable c] (h : ArithDef R) (h' : ArithDef S) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => if c then R A v else S A v) := by
  by_cases hc : c
  · simpa [hc] using h
  · simpa [hc] using h'

/-- **A finite conjunction** of definable relations is definable: the index
ranges over a `Fin k` of the *machine*, not of the instance, so the conjunction
is unfolded rather than quantified. -/
theorem forallFin : ∀ {k : ℕ} {R : Fin k → ArithRel L α}, (∀ j, ArithDef (R j)) →
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ j, R j A v) := by
  intro k
  induction k with
  | zero =>
    intro R _
    exact top.congr fun _A _ _ _ _ _v => ⟨fun _ j => j.elim0, fun _ => trivial⟩
  | succ k ih =>
    intro R h
    refine ((h 0).and (ih (R := fun j => R j.succ) fun j => h j.succ)).congr
      fun _A _ _ _ _ _v => ?_
    exact ⟨fun hc j => Fin.cases hc.1 (fun j' => hc.2 j') j, fun hall => ⟨hall 0, fun j => hall _⟩⟩

/-- **A conjunction over a finite index** of the *machine*, not of the instance:
the index type is any finite type, and the conjunction is unfolded rather than
quantified. -/
theorem forallFinite {ι : Type} [Finite ι] {R : ι → ArithRel L α} (h : ∀ j, ArithDef (R j)) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ j, R j A v) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine (forallFin (R := fun j => R (e.symm j)) fun j => h _).congr fun A _ _ _ _ v => ?_
  refine ⟨fun hall j => ?_, fun hall j => hall _⟩
  have := hall (e j)
  rwa [Equiv.symm_apply_apply] at this

/-- **A disjunction over a finite index** of the machine, by De Morgan. -/
theorem existsFinite {ι : Type} [Finite ι] {R : ι → ArithRel L α} (h : ∀ j, ArithDef (R j)) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∃ j, R j A v) :=
  (forallFinite (R := fun j A _ _ _ _ v => ¬ R j A v) fun j => (h j).not).not.congr
    fun _A _ _ _ _ _v => not_forall_not

/-- A truth value fixed outside the structure is definable. -/
theorem prop (c : Prop) : ArithDef (L := L) (α := α) (fun _ _ _ _ _ _ => c) := by
  by_cases hc : c
  · exact top.congr fun A _ _ _ _ v => by simp [hc]
  · exact bot.congr fun A _ _ _ _ v => by simp [hc]

end ArithDef

/-! ### Atoms -/

section Atoms

/-- The order between two variables is definable. -/
theorem arithDef_le (x y : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => v x ≤ v y) :=
  ⟨aLeF (Term.var x) (Term.var y), fun A _ _ _ _ v => by rw [realize_aLeF]; exact Iff.rfl⟩

/-- Equality between two variables is definable. -/
theorem arithDef_eq (x y : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => v x = v y) :=
  ⟨Term.equal (Term.var x) (Term.var y), fun A _ _ _ _ v => by
    rw [Formula.realize_equal]; exact Iff.rfl⟩

/-- Addition of the ranks of three variables is definable. -/
theorem arithDef_plus (x y z : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => orank (v x) + orank (v y) = orank (v z)) :=
  ⟨aPlusF (Term.var x) (Term.var y) (Term.var z), fun A _ _ _ _ v => by
    rw [realize_aPlusF]; exact Iff.rfl⟩

/-- Multiplication of the ranks of three variables is definable. -/
theorem arithDef_times (x y z : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => orank (v x) * orank (v y) = orank (v z)) :=
  ⟨aTimesF (Term.var x) (Term.var y) (Term.var z), fun A _ _ _ _ v => by
    rw [realize_aTimesF]; exact Iff.rfl⟩

/-- An input relation symbol, in the arithmetic expansion of its vocabulary.
Named, as every symbol of a sum vocabulary in this library is, so that `rw`
matches it. -/
abbrev inSym {a : ℕ} (R : L.Relations a) : (L.sum Language.arith).Relations a := Sum.inl R

/-- **Reading the input**: an atom of the input vocabulary, at a tuple of
variables, is definable. This is the only place the instance is looked at – in
the machine reading of this logic it is the query instruction. -/
theorem arithDef_rel {a : ℕ} (R : L.Relations a) (arg : Fin a → α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => RelMap R fun t => v (arg t)) :=
  ⟨Relations.formula (inSym R) fun t => Term.var (arg t), fun A _ _ _ _ v => by
    rw [Formula.realize_rel]
    exact Iff.rfl⟩

end Atoms

/-! ### Quantifiers -/

namespace ArithDef

/-- **Existential quantification** of one variable: the variable of `Fin 1` in
`α ⊕ Fin 1`, which is the layout `FirstOrder.Language.Formula.iExs` binds. -/
theorem ex {R : ArithRel L (α ⊕ Fin 1)} (h : ArithDef R) :
    ArithDef (L := L) (α := α)
      (fun A _ _ _ _ v => ∃ a, R A (Sum.elim v fun _ => a)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iExs (Fin 1), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, (hφ A _).mp ha⟩
  · rintro ⟨w, hw⟩
    refine ⟨w 0, (hφ A _).mpr ?_⟩
    have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
      rw [Subsingleton.elim (0 : Fin 1) i]
    rwa [hw']

/-- **Universal quantification** of one variable, in the same layout. -/
theorem all {R : ArithRel L (α ⊕ Fin 1)} (h : ArithDef R) :
    ArithDef (L := L) (α := α)
      (fun A _ _ _ _ v => ∀ a, R A (Sum.elim v fun _ => a)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iAlls (Fin 1), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iAlls]
  constructor
  · intro ha w
    have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
      rw [Subsingleton.elim (0 : Fin 1) i]
    exact hw' ▸ (hφ A _).mp (ha (w 0))
  · intro hw a
    exact (hφ A _).mpr (hw fun _ => a)

/-- **Existential quantification of a block** of `k` variables at once. -/
theorem exs {k : ℕ} {R : ArithRel L (α ⊕ Fin k)} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∃ w : Fin k → A, R A (Sum.elim v w)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iExs (Fin k), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iExs]
  exact exists_congr fun w => hφ A _

/-- **Universal quantification of a block** of `k` variables at once. -/
theorem alls {k : ℕ} {R : ArithRel L (α ⊕ Fin k)} (h : ArithDef R) :
    ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ w : Fin k → A, R A (Sum.elim v w)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.iAlls (Fin k), fun A _ _ _ _ v => ?_⟩
  rw [Formula.realize_iAlls]
  exact forall_congr' fun w => hφ A _

end ArithDef

/-! ### From a closed relation to a sentence -/

/-- **The bridge to `DescriptiveComplexity.AC0Definable`**: a definable relation
with no free variables *is* an AC⁰ definition of the problem it states – a
formula over `Empty` is a sentence. -/
theorem ArithDef.ac0Definable [L.IsRelational] {P : DecisionProblem L} {R : ArithRel L Empty}
    (h : ArithDef R)
    (hP : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R A Empty.elim) :
    AC0Definable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, ?_⟩
  intro A _ _ _ _
  rw [hP A, Sentence.Realize]
  exact (hφ A _).trans (by rw [Subsingleton.elim (Empty.elim : Empty → A) default])

end DescriptiveComplexity
