/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax859101Proofs.DescriptiveComplexity.DecisionProblem
end Lax859101Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax859101Proofs.DescriptiveComplexity.FOInterpretation
end Lax859101Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation FOReduction)
end Lax859101Proofs.DescriptiveComplexity

/-!
# First-order interpretations and FO reductions

Complexity theory is essentially absent from Mathlib because formalizing a
machine model of computation (and resource bounds on it) is hard. However, many
classical NP-hardness reductions do not need the full power of polynomial-time
computation: the reduction is *first-order expressible* – the output structure
can be described by fixed first-order formulas evaluated in the input
structure. Such FO reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so
exhibiting an FO reduction is (much) stronger than exhibiting a Karp
reduction ([Karp 1972][karp1972reducibility]), while being completely
machine-model-free and therefore easy to
formalize on top of Mathlib's `ModelTheory` library.

This file defines:

* `DescriptiveComplexity.DecisionProblem L`: a “problem” over the vocabulary `L`, i.e., a
  property of `L`-structures;
* `DescriptiveComplexity.FOInterpretation L L' Tag dim`: a tagged, `dim`-dimensional
  first-order interpretation of a relational language `L'` in a language `L`,
  mapping every `L`-structure `A` to an `L'`-structure `I.Map A` with universe
  `Tag × (Fin dim → A)`;
* `DescriptiveComplexity.FOInterpretation.IsQuantifierFree`: interpretations all of whose
  defining formulas are quantifier-free (an even weaker reduction notion);
* `DescriptiveComplexity.FOReduction P Q`: an FO reduction from problem `P` to problem
  `Q`, i.e., an interpretation mapping yes-instances of `P` exactly to
  yes-instances of `Q`.

## Design notes

The textbook notion of FO reduction maps a structure `A` to a structure with
universe a definable subset of `A^k`, using a linear order on `A` to encode
constantly many “sorts” of elements. To stay order-free and subset-free we
instead tag tuples with elements of a finite type `Tag`, and use the full
universe `Tag × A^dim`: junk elements are harmless in practice because the
defining formulas can exclude them from all relations. Every tagged
interpretation can be converted into a textbook `k`-ary FO reduction on
ordered structures (using the order to encode constantly many tags), so the
notion formalized here is a genuine form of FO reducibility.

The universe of `I.Map A` is `Tag × (Fin dim → A)`, which is finite whenever
`A` and `Tag` are (`FOInterpretation.map_finite`): FO reductions map finite
structures to finite structures, as required for reductions between decision
problems on finite structures.

Following the usual convention of finite model theory, reductions are only
required to be correct on *nonempty* structures (and their tag types are
required to be nonempty, so that nonempty structures map to nonempty
structures). Empty structures are degenerate: no fixed-dimension
interpretation can produce a nonempty structure from an empty one, so e.g., no
problem that is false on an empty structure could reduce to SAT (whose empty
instance is trivially satisfiable), and hardness results would fail for
spurious reasons.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace DecisionProblem

variable {L} [L.IsRelational]

@[ext]
theorem ext {P Q : Lax904597.Problems.DecisionProblem L} (h : ∀ (A : Type) [L.Structure A], P A ↔ Q A) :
    P = Q := by
  obtain ⟨p, hp⟩ := P
  obtain ⟨q, hq⟩ := Q
  have : p = q := funext fun A => funext fun inst => propext (h A)
  subst this
  rfl

end DecisionProblem

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax859101Proofs.DescriptiveComplexity.DecisionProblem (ext)

end Lax904597.Problems.DecisionProblem

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace DecisionProblem

variable {L} [L.IsRelational]

end DecisionProblem

/-! ### Transport of relations along isomorphisms

Proving the `iso_invariant` field of a `DecisionProblem` always starts the
same way: the semantic property is phrased in terms of `RelMap r ![a]` /
`RelMap r ![a, b]`, and one must know that these transport along an
`L`-isomorphism. The two lemmas below package this step once and for all
(`Mathlib`'s `StrongHomClass.map_rel` states it with `e ∘ ![a, b]`, which
must first be normalized to `![e a, e b]`). -/

section RelMapTransport

variable {L} {A B : Type} [L.Structure A] [L.Structure B]

/-- A unary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₁ (e : A ≃[L] B) (r : L.Relations 1) (a : A) :
    RelMap r ![a] ↔ RelMap r ![e a] := by
  have h := StrongHomClass.map_rel e r ![a]
  have hv : e ∘ ![a] = ![e a] := by
    funext j
    fin_cases j
    simp
  rw [hv] at h
  exact h.symm

/-- A binary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₂ (e : A ≃[L] B) (r : L.Relations 2) (a b : A) :
    RelMap r ![a, b] ↔ RelMap r ![e a, e b] := by
  have h := StrongHomClass.map_rel e r ![a, b]
  have hv : e ∘ ![a, b] = ![e a, e b] := by
    funext j
    fin_cases j <;> simp
  rw [hv] at h
  exact h.symm

end RelMapTransport

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

theorem relMap_map [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.Map A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2 :=
  Iff.rfl

end FOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (relMap_map)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

omit [L.Structure A] in
/-- FO interpretations map finite structures to finite structures. -/
theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  inferInstanceAs (Finite (Tag × (Fin dim → A)))

end FOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (map_finite)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

omit [L.Structure A] in
/-- FO interpretations with nonempty tags map nonempty structures to nonempty
structures. -/
theorem map_nonempty [Nonempty Tag] [Nonempty A] : Nonempty (I.Map A) :=
  inferInstanceAs (Nonempty (Tag × (Fin dim → A)))

end FOInterpretation

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (map_nonempty)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end FOInterpretation

variable {L L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ " Q:51 => Lax904597.Interpretations.FOReduction P Q

/-- For a one-dimensional interpretation with a single tag, the interpreted
universe is equivalent, as a plain type, to the original universe. -/
def FOInterpretation.mapEquivSelf (I : Lax904597.Interpretations.FOInterpretation L L' Unit 1) (A : Type) :
    I.Map A ≃ A where
  toFun x := x.2 0
  invFun a := ((), fun _ => a)
  left_inv x :=
    Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
  right_inv _ := rfl

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (mapEquivSelf)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

variable {L L' : Language.{0, 0}}

/-- Interpretations are functorial on isomorphisms: an `L`-isomorphism of the
base structures induces an `L'`-isomorphism of the interpreted structures. -/
def FOInterpretation.mapLEquiv [L'.IsRelational] {Tag : Type} {dim : ℕ}
    (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : I.Map M ≃[L'] I.Map N where
  toFun p := (p.1, fun j => e (p.2 j))
  invFun p := (p.1, fun j => e.symm (p.2 j))
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun j => e.symm_apply_apply (p.2 j)⟩
  right_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun j => e.apply_symm_apply (p.2 j)⟩
  map_fun' f := isEmptyElim f
  map_rel' R x := by
    rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    exact StrongHomClass.realize_formula e _

end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax859101Proofs.DescriptiveComplexity.FOInterpretation (mapLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

variable {L L' : Language.{0, 0}}

end Lax859101Proofs.DescriptiveComplexity


