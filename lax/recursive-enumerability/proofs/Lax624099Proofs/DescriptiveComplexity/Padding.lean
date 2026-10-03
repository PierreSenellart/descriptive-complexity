/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Ordered
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Canonically padded tuples

Shared machinery for interpretations whose tags need tuples of *different*
lengths. The universe of a `Lax624099Proofs.DescriptiveComplexity.FOInterpretation` is `Tag × A^dim`
for a single dimension `dim`, so an element meant to carry an `m`-tuple with
`m < dim` must fix its remaining coordinates; otherwise the same intended
element would have several representatives, which for the SAT-family
reductions would mean several distinct propositional variables standing for
the same atom.

The convention here is to pad with a *minimum* of the input order: a tuple is
`Lax624099Proofs.DescriptiveComplexity.Canon m` when every coordinate from `m` on is a minimum. This is
the one place where the reductions of the library need their input structure
to be ordered. The file provides

* the semantic side: `Lax624099Proofs.DescriptiveComplexity.Canon`, `Lax624099Proofs.DescriptiveComplexity.Agree`,
  the padding `Lax624099Proofs.DescriptiveComplexity.pad` and prefix `Lax624099Proofs.DescriptiveComplexity.pref` operations,
  and the fact that a canonical tuple is the padding of its prefix
  (`Lax624099Proofs.DescriptiveComplexity.pad_pref_of_canon`, `Lax624099Proofs.DescriptiveComplexity.eq_pad_of_canon_agree`);
* the first-order side: formulas `Lax624099Proofs.DescriptiveComplexity.canonF`,
  `Lax624099Proofs.DescriptiveComplexity.eqTupF`, `Lax624099Proofs.DescriptiveComplexity.agreeF` over the ordered expansion
  `L.sum Language.order` expressing these conditions of the coordinates held
  by selected free variables, with their realization lemmas;
* the special case of a tuple read from a context through an index map
  (`Lax624099Proofs.DescriptiveComplexity.PadTup`, `Lax624099Proofs.DescriptiveComplexity.padTupF`), which is how an element
  encoding a second-order atom `R (x_{f 0}, …)` is pinned down.

Formula builders are parameterized by maps `Fin D → γ` selecting the free
variables holding each tuple, so that they can be instantiated at the variable
types of the defining formulas of an interpretation (`Fin 1 × Fin D`,
`Fin 2 × Fin D`).

Clients: the Tseitin encoding of `Lax624099Proofs.DescriptiveComplexity.Problems.Sat.Tseitin` and the
Horn discharge of `Lax624099Proofs.DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Finite conjunctions and disjunctions of formulas -/

section ListConnectives

variable {L' : Language.{0, 0}} {γ A : Type} [L'.Structure A] {v : γ → A}

/-- Finite conjunction of a list of formulas. -/
def listInf : List (L'.Formula γ) → L'.Formula γ
  | [] => ⊤
  | φ :: l => φ ⊓ listInf l

/-- Finite disjunction of a list of formulas. -/
def listSup : List (L'.Formula γ) → L'.Formula γ
  | [] => ⊥
  | φ :: l => φ ⊔ listSup l

theorem realize_listInf (l : List (L'.Formula γ)) :
    (listInf l).Realize v ↔ ∀ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [listInf, Formula.realize_top]
  | cons φ l ih => simp [listInf, Formula.realize_inf, ih]

theorem realize_listSup (l : List (L'.Formula γ)) :
    (listSup l).Realize v ↔ ∃ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [listSup, Formula.realize_bot]
  | cons φ l ih => simp [listSup, Formula.realize_sup, ih]

end ListConnectives

/-! ### Padded tuples -/

section Padding

variable {A : Type} {D : ℕ}

/-- A `D`-tuple is canonical at context length `m`: every coordinate from `m`
on is a minimum of the order. -/
def Canon [LE A] (m : ℕ) (u : Fin D → A) : Prop :=
  ∀ j : Fin D, m ≤ (j : ℕ) → IsBot (u j)

/-- Two `D`-tuples agree below `m`. -/
def Agree (m : ℕ) (u x : Fin D → A) : Prop :=
  ∀ j : Fin D, (j : ℕ) < m → x j = u j

/-- Pad a context tuple to a `D`-tuple with a (minimal) element. -/
def pad (a₀ : A) {m : ℕ} (w : Fin m → A) : Fin D → A :=
  fun j => if hj : (j : ℕ) < m then w ⟨j, hj⟩ else a₀

/-- The prefix of a `D`-tuple. -/
def pref {m : ℕ} (h : m ≤ D) (u : Fin D → A) : Fin m → A :=
  fun j => u (Fin.castLE h j)

theorem canon_pad [LE A] {a₀ : A} (h₀ : IsBot a₀) (m : ℕ) (w : Fin m → A) :
    Canon m (pad (D := D) a₀ w) := by
  intro j hj
  rw [pad, dif_neg (not_lt.mpr hj)]
  exact h₀

/-- A canonical tuple is the padding of its prefix. -/
theorem pad_pref_of_canon [PartialOrder A] {a₀ : A} (h₀ : IsBot a₀) {m : ℕ} (h : m ≤ D)
    {u : Fin D → A} (hc : Canon m u) : pad a₀ (pref h u) = u := by
  funext j
  rw [pad]
  split_ifs with hj
  · rw [pref]
    exact congrArg u (Fin.ext rfl)
  · exact (h₀ (u j)).antisymm (hc j (not_lt.mp hj) a₀)

/-! #### Tuples read through an index map

An interpretation encoding second-order atoms as elements needs one element per
atom `R (x_{f 0}, …, x_{f (m-1)})`, whose coordinates are read from a context
tuple `u` through an index map `f`. Canonical padding makes that element
unique. -/

end Padding

section Builders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

/-- `x` is a minimum of the order, as a formula. -/
noncomputable def botF (x : γ) : (L.sum Language.order).Formula γ :=
  Formula.iAlls (Fin 1)
    (Relations.formula₂ leSymb (Term.var (Sum.inl x)) (Term.var (Sum.inr 0)))

/-- The coordinates of `c` from `m` on are minima, as a formula: `c` holds a
canonically padded context tuple of length `m`. -/
noncomputable def canonF (m : ℕ) (c : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    if m ≤ (j : ℕ) then botF (c j) else ⊤)

/-- The tuples held by `u` and `x` are equal, as a formula. -/
def eqTupF (u x : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    Term.equal (Term.var (x j)) (Term.var (u j)))

/-- The tuples held by `u` and `x` agree below `m`, as a formula. -/
def agreeF (m : ℕ) (u x : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    if (j : ℕ) < m then Term.equal (Term.var (x j)) (Term.var (u j)) else ⊤)

end Builders

/-! ### Realization of the builders -/

section RealizeBuilders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_botF {x : γ} : (botF (L := L) x).Realize v ↔ IsBot (v x) := by
  rw [botF]
  simp only [Formula.realize_iAlls, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, relMap_leSymb]
  exact ⟨fun h b => h fun _ => b, fun h i => h (i 0)⟩

@[simp]
theorem realize_canonF {m : ℕ} {c : Fin D → γ} :
    (canonF (L := L) m c).Realize v ↔ Canon m fun j => v (c j) := by
  rw [canonF, realize_listInf]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [if_pos hj] at this
    exact realize_botF.mp this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · exact realize_botF.mpr (h j hj)
    · exact Formula.realize_top.mpr trivial

@[simp]
theorem realize_eqTupF {u x : Fin D → γ} :
    (eqTupF (L := L) u x).Realize v ↔ (fun j => v (x j)) = fun j => v (u j) := by
  rw [eqTupF, realize_listInf, funext_iff]
  constructor
  · intro h j
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact h j

@[simp]
theorem realize_agreeF {m : ℕ} {u x : Fin D → γ} :
    (agreeF (L := L) m u x).Realize v ↔
      Agree m (fun j => v (u j)) fun j => v (x j) := by
  rw [agreeF, realize_listInf]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [if_pos hj] at this
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact h j hj
    · exact Formula.realize_top.mpr trivial

end RealizeBuilders

end Lax624099Proofs.DescriptiveComplexity


