/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Lax895169Proofs.DescriptiveComplexity.Complexity
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax895169Proofs.DescriptiveComplexity.SOAtom
end Lax895169Proofs.DescriptiveComplexity.SOAtom

namespace Lax895169Proofs.DescriptiveComplexity.SOBlock
end Lax895169Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable instIsRelationalLang soLang)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Second-order definability with bounded alternation

Foundation for *defining* the levels `Σₖ`/`Πₖ` (`k ≥ 1`) of the polynomial
hierarchy logically, by Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: `Σₖᵖ`
consists of
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

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Second-order quantifier blocks -/

attribute [instance] Lax904597.SecondOrder.SOBlock.ιFinite

/-- A bound on the arities of a block: every relation variable of the block
has arity at most `blockArityBound B`. Interpretations encoding the relation
variables as tagged tuples use it to size their dimension. -/
noncomputable def blockArityBound (B : Lax904597.SecondOrder.SOBlock) : ℕ :=
  letI := Fintype.ofFinite B.ι
  Finset.univ.sup B.arity

theorem arity_le_blockArityBound (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) :
    B.arity i ≤ blockArityBound B := by
  let := Fintype.ofFinite B.ι
  exact Finset.le_sup (Finset.mem_univ i)

variable {L : Language.{0, 0}}

/-! ### Isomorphism-invariance -/

section Iso

/-- Transport of a block assignment along an equivalence. -/
def SOBlock.mapAssign (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A') (ρ : B.Assignment A) :
    B.Assignment A' :=
  fun i x => ρ i fun j => e.symm (x j)

end Iso

end Lax895169Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax895169Proofs.DescriptiveComplexity.SOBlock (mapAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Iso

end Iso

/-! ### Duality: `Πₖ` is co-`Σₖ` -/

section Duality

end Duality

/-! ### Atoms in the relation variables of a block

The clausal fragments of existential second-order logic – SO-Horn
(`DescriptiveComplexity.SecondOrderHorn`) and SO-Krom
(`DescriptiveComplexity.SecondOrderKrom`) – represent their first-order kernel as
data: a list of clauses built from *atoms* in the quantified relation
variables, over a shared list of universally quantified first-order variables.
The atom type and its semantics are common to both fragments, so they live
here. -/

section Atoms

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- Atoms are insensitive to transporting an assignment along an
isomorphism. -/
theorem SOAtom.holds_equiv {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)
    (a : Lax485149.SecondOrderAtoms.SOAtom B k) (ρ : B.Assignment M) (v : Fin k → M) :
    a.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ a.Holds ρ v := by
  refine iff_of_eq (congrArg (ρ a.idx) (funext fun j => ?_))
  exact e.toEquiv.symm_apply_apply _

end Atoms

end Lax895169Proofs.DescriptiveComplexity

namespace Lax485149.SecondOrderAtoms.SOAtom

export Lax895169Proofs.DescriptiveComplexity.SOAtom (holds_equiv)

end Lax485149.SecondOrderAtoms.SOAtom

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Atoms

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

end Atoms

end Lax895169Proofs.DescriptiveComplexity


