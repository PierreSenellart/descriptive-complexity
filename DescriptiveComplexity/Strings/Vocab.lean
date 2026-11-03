/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite vocabularies as lists of arities

The string side of the library's bridge to machine classes numbers the relation
symbols of a structure, so that a structure can be written down as a bit string:
the tables of its relations, one symbol after the other. A
`DescriptiveComplexity.Strings.FinVocab` is such a numbering of the symbols of a
relational language. It is data: the encoding of a structure depends on it, as it
must, while what is proved about the encoded language does not.

`DescriptiveComplexity.Strings.FinVocab.ofEquiv` builds one from an enumeration of
the symbols, and `DescriptiveComplexity.Strings.FinVocab.ofFinite` from the mere
finiteness of the set of symbols.
-/

namespace DescriptiveComplexity.Strings

open FirstOrder

/-- An enumeration of the relation symbols of `L`, listing their arities. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The arities of the symbols, in the order of the enumeration. -/
  σ : List ℕ
  /-- The symbol of a given number, with its arity. -/
  sym : Fin σ.length ≃ Σ n, L.Relations n
  /-- The list records the arity of each symbol. -/
  arity_sym : ∀ i, (sym i).1 = σ.get i

namespace FinVocab

variable {L : Language.{0, 0}}

/-- A numbering from an enumeration of the symbols. -/
def ofEquiv {m : ℕ} (e : Fin m ≃ Σ n, L.Relations n) : FinVocab L where
  σ := List.ofFn fun i => (e i).1
  sym := (finCongr (List.length_ofFn ..)).trans e
  arity_sym i := by simp; rfl

/-- A numbering from the finiteness of the set of symbols. -/
noncomputable def ofFinite (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : FinVocab L :=
  ofEquiv (Finite.equivFin _).symm

/-- A numbering from a complete list of the symbols, in that order. -/
noncomputable def ofList (l : List (Σ n, L.Relations n)) (hn : l.Nodup) (hc : ∀ s, s ∈ l) :
    FinVocab L := by
  classical
  exact ofEquiv (hn.getEquivOfForallMemList l hc)

/-- The list of arities of `FinVocab.ofList` is that of the list of symbols. -/
theorem ofList_σ (l : List (Σ n, L.Relations n)) (hn : l.Nodup) (hc : ∀ s, s ∈ l) :
    (ofList l hn hc).σ = l.map Sigma.fst := by
  classical
  apply List.ext_getElem
  · simp [ofList, ofEquiv]
  · intro i h₁ h₂
    simp [ofList, ofEquiv]

variable (V : FinVocab L)

/-- The number of a given symbol. -/
def toSym {n : ℕ} (R : L.Relations n) : Fin V.σ.length :=
  V.sym.symm ⟨n, R⟩

/-- The number of a symbol has the arity of that symbol. -/
theorem arity_toSym {n : ℕ} (R : L.Relations n) : V.σ.get (V.toSym R) = n := by
  rw [← V.arity_sym, toSym, Equiv.apply_symm_apply]

/-- The symbol of a given number, at the arity the list records. -/
def ofSym (i : Fin V.σ.length) : L.Relations (V.σ.get i) :=
  V.arity_sym i ▸ (V.sym i).2

theorem toSym_ofSym (i : Fin V.σ.length) : V.toSym (V.ofSym i) = i := by
  have key : ∀ (n : ℕ) (h : (V.sym i).1 = n), V.toSym (h ▸ (V.sym i).2) = i := by
    rintro _ rfl
    exact V.sym.symm_apply_apply i
  exact key _ _

/-- The symbol of the number of a symbol is that symbol. -/
theorem ofSym_toSym {n : ℕ} (R : L.Relations n) :
    V.arity_toSym R ▸ V.ofSym (V.toSym R) = R := by
  have key : ∀ (s : Σ n, L.Relations n) (hs : s = ⟨n, R⟩) (m : ℕ) (h₁ : s.1 = m) (h₂ : m = n),
      h₂ ▸ h₁ ▸ s.2 = R := by
    rintro _ rfl _ rfl _; rfl
  exact key _ (V.sym.apply_symm_apply _) _ _ _

end FinVocab

end DescriptiveComplexity.Strings
