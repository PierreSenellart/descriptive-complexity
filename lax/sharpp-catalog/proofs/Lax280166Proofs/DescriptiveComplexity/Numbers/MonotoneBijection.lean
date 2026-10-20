/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Cardinal.Finite
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

/-!
# The monotone bijection between two sets of the same size

A threshold in the unary representation of `DescriptiveComplexity.Numbers.Unary` is
the size of a marked set, and “this set has exactly that size” is certified by
a bijection with the marked set. A *count* of certificates needs the certificate
to be unique, and a bijection is not: two sets of size `k` have `k!` of them.
On a linearly ordered finite universe exactly one of them is monotone, and that
is the one a counting kernel guesses.

* `DescriptiveComplexity.MonoBij K S F`: the binary relation `F` is the graph of a
  monotone bijection from `K` onto `S`, as four first-order conditions;
* `DescriptiveComplexity.MonoBij.ncard_eq`: such a graph makes the two sets the same
  size;
* `DescriptiveComplexity.exists_monoBij`, `DescriptiveComplexity.MonoBij.ext`: on a finite
  linear order, two sets of the same size have one, and only one.
-/

namespace Lax280166Proofs.DescriptiveComplexity

variable {A : Type}

/-- The relation `F` is the graph of a monotone bijection from `K` onto `S`: it
relates members of `K` to members of `S`, it is total on `K` and onto `S`, and
it preserves and reflects the order. The last condition makes it functional
and injective as well. -/
def MonoBij [LE A] (K S : A → Prop) (F : A → A → Prop) : Prop :=
  (∀ x y, F x y → K x ∧ S y) ∧ (∀ x, K x → ∃ y, F x y) ∧ (∀ y, S y → ∃ x, F x y) ∧
    ∀ x x' y y', F x y → F x' y' → (x ≤ x' ↔ y ≤ y')

/-- The graph of an order isomorphism between two sets is a monotone
bijection. -/
theorem monoBij_of_orderIso [LE A] {K S : A → Prop} (e : {x // K x} ≃o {y // S y}) :
    MonoBij K S fun x y => ∃ hx : K x, (e ⟨x, hx⟩).1 = y := by
  refine ⟨?_, fun x hx => ⟨_, hx, rfl⟩, fun y hy => ?_, ?_⟩
  · rintro x y ⟨hx, rfl⟩
    exact ⟨hx, (e ⟨x, hx⟩).2⟩
  · refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [Subtype.coe_eta, e.apply_symm_apply]
  · rintro x x' y y' ⟨hx, rfl⟩ ⟨hx', rfl⟩
    exact (e.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩)).symm

section Linear

variable [LinearOrder A] {K S : A → Prop} {F G : A → A → Prop}

/-- A monotone bijection is functional. -/
theorem MonoBij.functional (h : MonoBij K S F) {x y y' : A} (hy : F x y) (hy' : F x y') :
    y = y' :=
  le_antisymm ((h.2.2.2 x x y y' hy hy').mp le_rfl) ((h.2.2.2 x x y' y hy' hy).mp le_rfl)

/-- A monotone bijection is injective. -/
theorem MonoBij.injective (h : MonoBij K S F) {x x' y : A} (hx : F x y) (hx' : F x' y) :
    x = x' :=
  le_antisymm ((h.2.2.2 x x' y y hx hx').mpr le_rfl) ((h.2.2.2 x' x y y hx' hx).mpr le_rfl)

/-- The order isomorphism a monotone bijection is the graph of. -/
noncomputable def MonoBij.orderIso (h : MonoBij K S F) : {x // K x} ≃o {y // S y} where
  toFun x := ⟨(h.2.1 x.1 x.2).choose, (h.1 _ _ (h.2.1 x.1 x.2).choose_spec).2⟩
  invFun y := ⟨(h.2.2.1 y.1 y.2).choose, (h.1 _ _ (h.2.2.1 y.1 y.2).choose_spec).1⟩
  left_inv x := Subtype.ext
    (h.injective (h.2.2.1 _ (h.1 _ _ (h.2.1 x.1 x.2).choose_spec).2).choose_spec
      (h.2.1 x.1 x.2).choose_spec)
  right_inv y := Subtype.ext
    (h.functional (h.2.1 _ (h.1 _ _ (h.2.2.1 y.1 y.2).choose_spec).1).choose_spec
      (h.2.2.1 y.1 y.2).choose_spec)
  map_rel_iff' {x x'} :=
    (h.2.2.2 _ _ _ _ (h.2.1 x.1 x.2).choose_spec (h.2.1 x'.1 x'.2).choose_spec).symm

theorem MonoBij.rel_orderIso (h : MonoBij K S F) (x : {x // K x}) :
    F x.1 (h.orderIso x).1 :=
  (h.2.1 x.1 x.2).choose_spec

/-- A monotone bijection is the graph of its order isomorphism. -/
theorem MonoBij.iff_orderIso (h : MonoBij K S F) (x y : A) :
    F x y ↔ ∃ hx : K x, (h.orderIso ⟨x, hx⟩).1 = y := by
  constructor
  · intro hxy
    exact ⟨(h.1 x y hxy).1, h.functional (h.rel_orderIso ⟨x, (h.1 x y hxy).1⟩) hxy⟩
  · rintro ⟨hx, rfl⟩
    exact h.rel_orderIso ⟨x, hx⟩

/-- Two sets related by a monotone bijection have the same size. -/
theorem MonoBij.ncard_eq (h : MonoBij K S F) : {y | S y}.ncard = {x | K x}.ncard :=
  (Nat.card_coe_set_eq {y | S y}).symm.trans
    ((Nat.card_congr h.orderIso.toEquiv.symm).trans (Nat.card_coe_set_eq {x | K x}))

variable [Finite A]

/-- **A monotone bijection between two sets is unique.** -/
theorem MonoBij.ext (h : MonoBij K S F) (h' : MonoBij K S G) : F = G := by
  funext x y
  rw [h.iff_orderIso, h'.iff_orderIso, Subsingleton.elim h.orderIso h'.orderIso]

/-- **Two sets of the same size have a monotone bijection.** -/
theorem exists_monoBij (hcard : {y | S y}.ncard = {x | K x}.ncard) :
    ∃ F : A → A → Prop, MonoBij K S F := by
  classical
  have := Fintype.ofFinite {x // K x}
  have := Fintype.ofFinite {y // S y}
  have hc : Fintype.card {y // S y} = Fintype.card {x // K x} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq {y | S y}).trans
      (hcard.trans (Nat.card_coe_set_eq {x | K x}).symm)
  exact ⟨_, monoBij_of_orderIso
    ((monoEquivOfFin {x // K x} rfl).symm.trans (monoEquivOfFin {y // S y} hc))⟩

end Linear

end Lax280166Proofs.DescriptiveComplexity


