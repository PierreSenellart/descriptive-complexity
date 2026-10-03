/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
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
lengths. The universe of a `Lax799700Proofs.DescriptiveComplexity.FOInterpretation` is `Tag × A^dim`
for a single dimension `dim`, so an element meant to carry an `m`-tuple with
`m < dim` must fix its remaining coordinates; otherwise the same intended
element would have several representatives, which for the SAT-family
reductions would mean several distinct propositional variables standing for
the same atom.

The convention here is to pad with a *minimum* of the input order: a tuple is
`Lax799700Proofs.DescriptiveComplexity.Canon m` when every coordinate from `m` on is a minimum. This is
the one place where the reductions of the library need their input structure
to be ordered. The file provides

* the semantic side: `Lax799700Proofs.DescriptiveComplexity.Canon`, `Lax799700Proofs.DescriptiveComplexity.Agree`,
  the padding `Lax799700Proofs.DescriptiveComplexity.pad` and prefix `Lax799700Proofs.DescriptiveComplexity.pref` operations,
  and the fact that a canonical tuple is the padding of its prefix
  (`Lax799700Proofs.DescriptiveComplexity.pad_pref_of_canon`, `Lax799700Proofs.DescriptiveComplexity.eq_pad_of_canon_agree`);
* the first-order side: formulas `Lax799700Proofs.DescriptiveComplexity.canonF`,
  `Lax799700Proofs.DescriptiveComplexity.eqTupF`, `Lax799700Proofs.DescriptiveComplexity.agreeF` over the ordered expansion
  `L.sum Language.order` expressing these conditions of the coordinates held
  by selected free variables, with their realization lemmas;
* the special case of a tuple read from a context through an index map
  (`Lax799700Proofs.DescriptiveComplexity.PadTup`, `Lax799700Proofs.DescriptiveComplexity.padTupF`), which is how an element
  encoding a second-order atom `R (x_{f 0}, …)` is pinned down.

Formula builders are parameterized by maps `Fin D → γ` selecting the free
variables holding each tuple, so that they can be instantiated at the variable
types of the defining formulas of an interpretation (`Fin 1 × Fin D`,
`Fin 2 × Fin D`).

Clients: the Tseitin encoding of `Lax799700Proofs.DescriptiveComplexity.Problems.Sat.Tseitin` and the
Horn discharge of `Lax799700Proofs.DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Finite conjunctions and disjunctions of formulas -/

section ListConnectives

variable {L' : Language.{0, 0}} {γ A : Type} [L'.Structure A] {v : γ → A}

end ListConnectives

/-! ### Padded tuples -/

section Padding

variable {A : Type} {D : ℕ}

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

end RealizeBuilders

end Lax799700Proofs.DescriptiveComplexity


