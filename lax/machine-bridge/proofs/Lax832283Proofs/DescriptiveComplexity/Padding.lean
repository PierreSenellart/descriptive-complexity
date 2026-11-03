/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.Ordered
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

/-!
# Canonically padded tuples

Shared machinery for interpretations whose tags need tuples of *different*
lengths. The universe of a `DescriptiveComplexity.FOInterpretation` is `Tag × A^dim`
for a single dimension `dim`, so an element meant to carry an `m`-tuple with
`m < dim` must fix its remaining coordinates; otherwise the same intended
element would have several representatives, which for the SAT-family
reductions would mean several distinct propositional variables standing for
the same atom.

The convention here is to pad with a *minimum* of the input order: a tuple is
`DescriptiveComplexity.Canon m` when every coordinate from `m` on is a minimum. This is
the one place where the reductions of the library need their input structure
to be ordered. The file provides

* the semantic side: `DescriptiveComplexity.Canon`, `DescriptiveComplexity.Agree`,
  the padding `DescriptiveComplexity.pad` and prefix `DescriptiveComplexity.pref` operations,
  and the fact that a canonical tuple is the padding of its prefix
  (`DescriptiveComplexity.pad_pref_of_canon`, `DescriptiveComplexity.eq_pad_of_canon_agree`);
* the first-order side: formulas `DescriptiveComplexity.canonF`,
  `DescriptiveComplexity.eqTupF`, `DescriptiveComplexity.agreeF` over the ordered expansion
  `L.sum Language.order` expressing these conditions of the coordinates held
  by selected free variables, with their realization lemmas;
* the special case of a tuple read from a context through an index map
  (`DescriptiveComplexity.PadTup`, `DescriptiveComplexity.padTupF`), which is how an element
  encoding a second-order atom `R (x_{f 0}, …)` is pinned down.

Formula builders are parameterized by maps `Fin D → γ` selecting the free
variables holding each tuple, so that they can be instantiated at the variable
types of the defining formulas of an interpretation (`Fin 1 × Fin D`,
`Fin 2 × Fin D`).

Clients: the Tseitin encoding of `DescriptiveComplexity.Problems.Sat.Tseitin` and the
Horn discharge of `DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax832283Proofs.DescriptiveComplexity

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

/-! #### Tuples read through an index map

An interpretation encoding second-order atoms as elements needs one element per
atom `R (x_{f 0}, …, x_{f (m-1)})`, whose coordinates are read from a context
tuple `u` through an index map `f`. Canonical padding makes that element
unique. -/

end Padding

section Builders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

/-- The tuples held by `u` and `x` are equal, as a formula. -/
def eqTupF (u x : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun (j : Fin D) =>
    Term.equal (Term.var (x j)) (Term.var (u j)))

end Builders

/-! ### Realization of the builders -/

section RealizeBuilders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

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

end RealizeBuilders

end Lax832283Proofs.DescriptiveComplexity


