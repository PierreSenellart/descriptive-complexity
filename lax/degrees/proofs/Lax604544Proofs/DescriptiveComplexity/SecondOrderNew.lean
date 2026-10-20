/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.SecondOrderLift
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

namespace Lax604544Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax604544Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax604544Proofs.Foreign.FirstOrder.Language
end Lax604544Proofs.Foreign.FirstOrder.Language

namespace Lax624099.ValueInvention
end Lax624099.ValueInvention

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize SigmaSODefinable soLang)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax624099.ValueInvention (IsOld SigmaSONewDefinable extBase extStructure newLang oldMarkStructure)
end Lax604544Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax624099.ValueInvention (oldMark oldRel)
end FirstOrder.Language

/-!
# Existential second-order logic with value invention

The logic `∃SO[new]` defining the class RE of recursively enumerable problems:
existential second-order logic whose relation variables range over a universe
*extended by finitely many invented values*, in the style of the
object-creating query languages of ([Abiteboul–Hull–Vianu 1995]
[abiteboul1995foundations], ch. 18).

Bounding the certificate by the instance is what keeps a second-order class
inside NP: a `Σ₁` sentence guesses relations over `A` itself, so the search
space is exponential in `|A|`. Value invention
removes exactly that bound and nothing else: the certificate is a finite
extension `A ⊕ Fin m` of the universe – with `m` *unbounded* – together with
relations over it, checked by a fixed first-order kernel. The witness is still
a finite object and the kernel is still decidable on a finite structure, so
the yes-instances are those found by an unbounded search over finite
witnesses: this is a logical definition of *recursive enumerability*, with no
machine model. (The converse inclusion, RE ⊆ `∃SO[new]`, is the
Trakhtenbrot-style encoding of an accepting run into invented values; it lives
with the machine bridge, not here.)

## The extended structure

An instance `A` and a number `m` of invented values determine an extended
structure over the vocabulary `DescriptiveComplexity.newLang L`, the base
vocabulary `L` together with one unary predicate `old`:

* its universe is `A ⊕ Fin m`;
* the symbols of `L` hold exactly where they hold in `A`, on original
  elements only – invented values are related to nothing
  (`DescriptiveComplexity.extBase`);
* `old` marks the original elements (`DescriptiveComplexity.IsOld`).

The vocabulary is relational, as every vocabulary of a
`DescriptiveComplexity.DecisionProblem` is, so invented values carry no
structure at all until the certificate's relations put some on them.

## Main definitions and results

* `DescriptiveComplexity.SigmaSONewDefinable`: definability by an `∃SO[new]`
  sentence – one existential second-order block over the extended universe and
  a first-order kernel, reusing the alternation machinery of
  `DescriptiveComplexity.SecondOrder` at a one-block list;
* `DescriptiveComplexity.extEquiv`: extended structures are functorial in the
  base isomorphism, so `∃SO[new]` expresses isomorphism-invariant properties;
* `DescriptiveComplexity.sigmaSONewDefinable_congr`: definability depends only
  on the finite instances of a problem;
* `DescriptiveComplexity.SigmaSODefinable.toNew`: `Σ₁ ⊆ ∃SO[new]`, by
  inventing nothing – the kernel is guarded by
  `DescriptiveComplexity.noNewSentence`, “every element is original”, which
  pins the number of invented values to zero. As a statement about classes this
  is `DescriptiveComplexity.NP_subset_RE`.

No alternation hierarchy is built on top of `∃SO[new]`, deliberately:
alternating second-order blocks over a *finite* extended universe are still
checked by an unbounded search over finite witnesses, so the levels would
collapse into RE rather than stack. (That collapse is a semantic remark, not a
theorem here: proving it inside the logic needs the same encoding as the
inclusion RE ⊆ `∃SO[new]`.)
-/

namespace FirstOrder

namespace Language

open Lax604544Proofs.Foreign.FirstOrder.Language in
/-- The symbol marking the original elements. -/
abbrev _root_.Lax604544Proofs.Foreign.FirstOrder.Language.oldSym : Lax624099.ValueInvention.oldMark.Relations 1 := .old

export Lax604544Proofs.Foreign.FirstOrder.Language (oldSym)

end Language

end FirstOrder

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The extended universe -/

section Extended

variable {L : Language.{0, 0}} {A A' : Type} {m m' : ℕ}

@[simp]
theorem isOld_inl (a : A) : Lax624099.ValueInvention.IsOld (Sum.inl a : A ⊕ Fin m) := trivial

@[simp]
theorem not_isOld_inr (i : Fin m) : ¬Lax624099.ValueInvention.IsOld (Sum.inr i : A ⊕ Fin m) := id

theorem isOld_iff {x : A ⊕ Fin m} : Lax624099.ValueInvention.IsOld x ↔ ∃ a : A, x = Sum.inl a := by
  cases x <;> simp

theorem relMap_ext_iff [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (x : Fin k → A ⊕ Fin m) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (Sum.inl r) x ↔ ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y :=
  Iff.rfl

/-- On original elements, the extended structure is the original one. -/
@[simp]
theorem relMap_ext_inl [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (y : Fin k → A) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (M := A ⊕ Fin m) (Sum.inl r) (fun i => Sum.inl (y i)) ↔
      RelMap r y := by
  rw [relMap_ext_iff]
  refine ⟨fun h => ?_, fun h => ⟨y, fun _ => rfl, h⟩⟩
  obtain ⟨y', hy', h⟩ := h
  have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
  exact hyy ▸ h

@[simp]
theorem relMap_ext_old [L.IsRelational] [L.Structure A] (x : Fin 1 → A ⊕ Fin m) :
    RelMap (L := Lax624099.ValueInvention.newLang L) (Sum.inr Lax604544Proofs.Foreign.FirstOrder.Language.oldSym) x ↔ Lax624099.ValueInvention.IsOld (x 0) :=
  Iff.rfl

/-! ### Functoriality in the base structure -/

end Extended

/-! ### Definability

`SORealize` is reused at the one-block list `[B]`, so that an `∃SO[new]`
sentence is literally an `∃SO` sentence – over the extended vocabulary, read
in the extended structure. -/

section Definability

variable {L : Language.{0, 0}}

/-- `∃SO[new]`-definability only depends on the finite instances of a
problem. -/
theorem sigmaSONewDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax624099.ValueInvention.SigmaSONewDefinable P ↔ Lax624099.ValueInvention.SigmaSONewDefinable Q := by
  constructor <;> rintro ⟨B, φ, hφ⟩ <;> refine ⟨B, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

end Definability

/-! ### Inventing nothing

The `Σ₁` sentences are the `∃SO[new]` sentences that invent nothing: the
kernel is guarded by `DescriptiveComplexity.noNewSentence`, which forces the
extended universe to be the original one. -/

section NoNew

variable (L : Language.{0, 0})

/-- The mark of the original elements on the original universe itself: every
element is original. -/
@[instance_reducible]
def allOldMarkStructure (A : Type) : Lax624099.ValueInvention.oldMark.Structure A where
  RelMap | .old => fun _ => True

/-- The instance itself, over the extended vocabulary: nothing is invented, so
every element is marked as original. -/
@[instance_reducible]
def allOldStructure (A : Type) [L.Structure A] : (Lax624099.ValueInvention.newLang L).Structure A :=
  @sumStructure L Lax624099.ValueInvention.oldMark A _ (allOldMarkStructure A)

end NoNew

/-! ### `Σ₁ ⊆ ∃SO[new]` -/

end Lax604544Proofs.DescriptiveComplexity


