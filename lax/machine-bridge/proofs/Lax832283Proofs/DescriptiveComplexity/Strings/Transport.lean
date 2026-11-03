/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.Interpretation
import Lax832283Proofs.DescriptiveComplexity.Strings.Vocab
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure Query)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures
export Lax988886.FiniteStructures (Isomorphism IsomorphismInvariant Property)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FiniteStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab ofOrdered toProperty toQuery)
end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax832283Proofs.DescriptiveComplexity

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

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder Language Structure

open Lax.OrderedStructures

variable {L : Language.{0, 0}}

/-- The table of a number, read through `ofOrdered`. -/
theorem relMap_ofOrdered_ofSym [L.IsRelational] (V : Lax832283.StringProblems.FinVocab L) (S : Lax751879.OrderedStructures.OrderedStructure V.σ)
    (r : Fin V.σ.length) (v : Fin (V.σ.get r) → Fin S.size) :
    (Lax832283.StringProblems.ofOrdered V S).RelMap (V.ofSym r) v ↔ S.relation r v = true := by
  have key : ∀ (r' : Fin V.σ.length) (h : r' = r) (h' : V.σ.get r' = V.σ.get r),
      S.relation r' (v ∘ Fin.cast h') = true ↔ S.relation r v = true := by
    rintro _ rfl _; exact Iff.rfl
  exact key _ (V.toSym_ofSym r) _

open Classical in
/-- Number a structure along a bijection with `Fin n`. -/
noncomputable def toOrdered (V : Lax832283.StringProblems.FinVocab L) (A : Type) [L.Structure A] {n : ℕ} (e : A ≃ Fin n) :
    Lax751879.OrderedStructures.OrderedStructure V.σ where
  size := n
  relation r a := decide (RelMap (V.ofSym r) (e.symm ∘ a))

/-- Transport along a cast of the arity of a symbol. -/
private theorem relMap_cast {A : Type} [L.Structure A] {n m : ℕ} (h : n = m) (R : L.Relations n)
    (v : Fin n → A) :
    RelMap (h ▸ R) (v ∘ Fin.cast h.symm) ↔ RelMap R v := by
  subst h; exact Iff.rfl

open Classical in
/-- A table of `toOrdered` is the relation it numbers. -/
theorem relation_toOrdered (V : Lax832283.StringProblems.FinVocab L) (A : Type) [L.Structure A] {n : ℕ} (e : A ≃ Fin n)
    (r : Fin V.σ.length) (a : Fin (V.σ.get r) → Fin n) :
    (toOrdered V A e).relation r a = true ↔ RelMap (V.ofSym r) (e.symm ∘ a) :=
  decide_eq_true_iff

/-- **The round trip is an isomorphism**: numbering a structure along a bijection and
reading the result back. -/
noncomputable def ofOrderedEquiv [L.IsRelational] (V : Lax832283.StringProblems.FinVocab L) (A : Type) [L.Structure A]
    {n : ℕ} (e : A ≃ Fin n) :
    @Language.Equiv L A (Fin n) _ (Lax832283.StringProblems.ofOrdered V (toOrdered V A e)) :=
  letI : L.Structure (Fin n) := Lax832283.StringProblems.ofOrdered V (toOrdered V A e)
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
theorem toProperty_isoInvariant [L.IsRelational] (V : Lax832283.StringProblems.FinVocab L) (P : Lax904597.Problems.DecisionProblem L) :
    Lax988886.FiniteStructures.IsomorphismInvariant (Lax832283.StringProblems.toProperty V P) := by
  have key : ∀ A B : Lax751879.OrderedStructures.OrderedStructure V.σ, Lax988886.FiniteStructures.Isomorphism A B →
      (Lax832283.StringProblems.toProperty V P A → Lax832283.StringProblems.toProperty V P B) := by
    rintro A B e ⟨hA, hP⟩
    have hsize : A.size = B.size := by simpa using Fintype.card_congr e.equivalence
    refine ⟨hsize ▸ hA, ?_⟩
    let := Lax832283.StringProblems.ofOrdered V A
    let := Lax832283.StringProblems.ofOrdered V B
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
theorem toProperty_toOrdered [L.IsRelational] (V : Lax832283.StringProblems.FinVocab L) (P : Lax904597.Problems.DecisionProblem L)
    (A : Type) [L.Structure A] [Nonempty A] {n : ℕ} (e : A ≃ Fin n) :
    Lax832283.StringProblems.toProperty V P (toOrdered V A e) ↔ P A := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨e (Classical.arbitrary A)⟩
  constructor
  · rintro ⟨-, h⟩
    exact (@Lax904597.Problems.DecisionProblem.iso_invariant L _ P A (Fin n) _ (Lax832283.StringProblems.ofOrdered V (toOrdered V A e))
      (ofOrderedEquiv V A e)).mpr h
  · intro h
    exact ⟨hn, (@Lax904597.Problems.DecisionProblem.iso_invariant L _ P A (Fin n) _ (Lax832283.StringProblems.ofOrdered V (toOrdered V A e))
      (ofOrderedEquiv V A e)).mp h⟩

end Lax832283Proofs.DescriptiveComplexity.Strings


