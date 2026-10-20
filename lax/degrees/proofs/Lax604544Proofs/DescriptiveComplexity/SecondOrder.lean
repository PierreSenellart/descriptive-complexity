/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Lax604544Proofs.DescriptiveComplexity.Complexity
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax604544Proofs.DescriptiveComplexity.SOAtom
end Lax604544Proofs.DescriptiveComplexity.SOAtom

namespace Lax604544Proofs.DescriptiveComplexity.SOBlock
end Lax604544Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable instIsRelationalLang soLang)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax604544Proofs.DescriptiveComplexity

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

namespace Lax604544Proofs.DescriptiveComplexity

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

end Lax604544Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax604544Proofs.DescriptiveComplexity.SOBlock (mapAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Iso

/-- An `L`-isomorphism extends to the vocabulary expanded by a block, when
the block is interpreted by an assignment on one side and its transport on
the other. -/
def SOBlock.extendEquiv (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} [L.Structure A] [L.Structure A']
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

end Iso

end Lax604544Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax604544Proofs.DescriptiveComplexity.SOBlock (extendEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Iso

private theorem sorealize_iso_aux :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A A' : Type) (instA : L.Structure A)
      (instA' : L.Structure A'), @Language.Equiv L A A' instA instA' →
      ∀ (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A instA Bs φ pol → @Lax904597.SecondOrder.SORealize L A' instA' Bs φ pol := by
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
    (Bs : List Lax904597.SecondOrder.SOBlock) (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool) :
    Lax904597.SecondOrder.SORealize L A Bs φ pol ↔ Lax904597.SecondOrder.SORealize L A' Bs φ pol :=
  ⟨sorealize_iso_aux Bs L A A' _ _ e φ pol,
    sorealize_iso_aux Bs L A' A _ _ e.symm φ pol⟩

end Iso

/-! ### Duality: `Πₖ` is co-`Σₖ` -/

section Duality

private theorem sorealize_not :
    ∀ (Bs : List Lax904597.SecondOrder.SOBlock) (L : Language.{0, 0}) (A : Type) (inst : L.Structure A)
      (φ : (Lax904597.SecondOrder.soLang L Bs).Sentence) (pol : Bool),
      @Lax904597.SecondOrder.SORealize L A inst Bs (∼φ) pol ↔ ¬@Lax904597.SecondOrder.SORealize L A inst Bs φ (!pol) := by
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
            ¬@Lax904597.SecondOrder.SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
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
theorem piSODefinable_iff_compl [L.IsRelational] (k : ℕ) (P : Lax904597.Problems.DecisionProblem L) :
    Lax904597.SecondOrder.PiSODefinable k P ↔ Lax904597.SecondOrder.SigmaSODefinable k Pᶜ := by
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

end Lax604544Proofs.DescriptiveComplexity

namespace Lax485149.SecondOrderAtoms.SOAtom

export Lax604544Proofs.DescriptiveComplexity.SOAtom (holds_equiv)

end Lax485149.SecondOrderAtoms.SOAtom

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Atoms

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

end Atoms

end Lax604544Proofs.DescriptiveComplexity


