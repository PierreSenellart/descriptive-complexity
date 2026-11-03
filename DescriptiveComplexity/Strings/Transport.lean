/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Strings.Vocab
import DescriptiveComplexity.Strings.Lax.FiniteStructures

/-!
# Structures and problems across the two formalisms

A structure of the archive's formalism is a size and Boolean tables, numbered by a
`DescriptiveComplexity.Strings.FinVocab`; it reads as an `L`-structure on `Fin n`
(`DescriptiveComplexity.Strings.ofOrdered`), and a decision problem of the library
reads as a property of such structures (`DescriptiveComplexity.Strings.toProperty`)
and as a Boolean query (`DescriptiveComplexity.Strings.toQuery`).

The library's classes are about nonempty structures, while the archive's
structures may be empty: the empty structure is a no-instance. Malformed words need
no such care, the archive's languages ranging over encodings of structures only.

The other direction, `DescriptiveComplexity.Strings.toOrdered`, numbers a structure
along a bijection with `Fin n`, and the round trip is an isomorphism
(`DescriptiveComplexity.Strings.ofOrderedEquiv`).
-/

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure
open Lax.OrderedStructures

variable {L : Language.{0, 0}}

/-- Read a table of the archive's formalism as a structure of the library. -/
@[instance_reducible]
def ofOrdered [L.IsRelational] (V : FinVocab L) (S : OrderedStructure V.σ) :
    L.Structure (Fin S.size) where
  funMap f := isEmptyElim f
  RelMap {n} R v := S.relation (V.toSym R) (v ∘ Fin.cast
    (show V.σ.get (V.toSym R) = n by rw [← V.arity_sym, FinVocab.toSym, Equiv.apply_symm_apply]))
    = true

/-- The table of a number, read through `ofOrdered`. -/
theorem relMap_ofOrdered_ofSym [L.IsRelational] (V : FinVocab L) (S : OrderedStructure V.σ)
    (r : Fin V.σ.length) (v : Fin (V.σ.get r) → Fin S.size) :
    (ofOrdered V S).RelMap (V.ofSym r) v ↔ S.relation r v = true := by
  have key : ∀ (r' : Fin V.σ.length) (h : r' = r) (h' : V.σ.get r' = V.σ.get r),
      S.relation r' (v ∘ Fin.cast h') = true ↔ S.relation r v = true := by
    rintro _ rfl _; exact Iff.rfl
  exact key _ (V.toSym_ofSym r) _

/-- A decision problem of the library, as a property of the archive's structures. The
empty structure is a no-instance. -/
def toProperty [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L) :
    Lax.FiniteStructures.Property V.σ :=
  fun S => 0 < S.size ∧ @DecisionProblem.Holds L _ P (Fin S.size) (ofOrdered V S)

/-- A decision problem of the library, as a Boolean query on ordered structures. -/
def toQuery [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L) : Query V.σ 0 :=
  fun S => toProperty V P S.structureValue

open Classical in
/-- Number a structure along a bijection with `Fin n`. -/
noncomputable def toOrdered (V : FinVocab L) (A : Type) [L.Structure A] {n : ℕ} (e : A ≃ Fin n) :
    OrderedStructure V.σ where
  size := n
  relation r a := decide (RelMap (V.ofSym r) (e.symm ∘ a))

/-- Transport along a cast of the arity of a symbol. -/
private theorem relMap_cast {A : Type} [L.Structure A] {n m : ℕ} (h : n = m) (R : L.Relations n)
    (v : Fin n → A) :
    RelMap (h ▸ R) (v ∘ Fin.cast h.symm) ↔ RelMap R v := by
  subst h; exact Iff.rfl

open Classical in
/-- A table of `toOrdered` is the relation it numbers. -/
theorem relation_toOrdered (V : FinVocab L) (A : Type) [L.Structure A] {n : ℕ} (e : A ≃ Fin n)
    (r : Fin V.σ.length) (a : Fin (V.σ.get r) → Fin n) :
    (toOrdered V A e).relation r a = true ↔ RelMap (V.ofSym r) (e.symm ∘ a) :=
  decide_eq_true_iff

/-- **The round trip is an isomorphism**: numbering a structure along a bijection and
reading the result back. -/
noncomputable def ofOrderedEquiv [L.IsRelational] (V : FinVocab L) (A : Type) [L.Structure A]
    {n : ℕ} (e : A ≃ Fin n) :
    @Language.Equiv L A (Fin n) _ (ofOrdered V (toOrdered V A e)) :=
  letI : L.Structure (Fin n) := ofOrdered V (toOrdered V A e)
  { toEquiv := e
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {m} R x => by
      refine (relation_toOrdered V A e _ _).trans ?_
      have h₁ : e.symm ∘ (fun i => e (x i)) ∘ Fin.cast (V.arity_toSym R) =
          x ∘ Fin.cast (V.arity_toSym R) := by
        funext i; simp
      have h₂ : (x ∘ Fin.cast (V.arity_toSym R)) ∘ Fin.cast (V.arity_toSym R).symm = x := by
        funext i; simp
      have h₃ := relMap_cast (V.arity_toSym R) (V.ofSym (V.toSym R))
        (x ∘ Fin.cast (V.arity_toSym R))
      rw [V.ofSym_toSym R, h₂] at h₃
      exact (iff_of_eq (congrArg _ h₁)).trans h₃.symm }

/-- **A library problem reads as an isomorphism-invariant property.** -/
theorem toProperty_isoInvariant [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L) :
    Lax.FiniteStructures.IsomorphismInvariant (toProperty V P) := by
  have key : ∀ A B : OrderedStructure V.σ, Lax.FiniteStructures.Isomorphism A B →
      (toProperty V P A → toProperty V P B) := by
    rintro A B e ⟨hA, hP⟩
    have hsize : A.size = B.size := by simpa using Fintype.card_congr e.equivalence
    refine ⟨hsize ▸ hA, ?_⟩
    let := ofOrdered V A
    let := ofOrdered V B
    have iso : Fin A.size ≃[L] Fin B.size :=
      { toEquiv := e.equivalence
        map_fun' := fun f => isEmptyElim f
        map_rel' := fun {m} R x => by
          change B.relation _ _ = true ↔ A.relation _ _ = true
          have := e.preserves (V.toSym R) (x ∘ Fin.cast (V.arity_toSym R))
          rw [← this]
          exact Iff.rfl }
    exact (P.iso_invariant iso).mp hP
  rintro A B ⟨e⟩
  refine ⟨key A B e, key B A ⟨e.equivalence.symm, fun r a => ?_⟩⟩
  rw [← e.preserves r (e.equivalence.symm ∘ a)]
  congr 1
  funext i
  simp

/-- **Numbering preserves the problem**, on nonempty structures. -/
theorem toProperty_toOrdered [L.IsRelational] (V : FinVocab L) (P : DecisionProblem L)
    (A : Type) [L.Structure A] [Nonempty A] {n : ℕ} (e : A ≃ Fin n) :
    toProperty V P (toOrdered V A e) ↔ P A := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨e (Classical.arbitrary A)⟩
  constructor
  · rintro ⟨-, h⟩
    exact (@DecisionProblem.iso_invariant L _ P A (Fin n) _ (ofOrdered V (toOrdered V A e))
      (ofOrderedEquiv V A e)).mpr h
  · intro h
    exact ⟨hn, (@DecisionProblem.iso_invariant L _ P A (Fin n) _ (ofOrdered V (toOrdered V A e))
      (ofOrderedEquiv V A e)).mp h⟩

end DescriptiveComplexity.Strings
