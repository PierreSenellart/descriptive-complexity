/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Defs
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.Defs
import Lax280166Proofs.DescriptiveComplexity.Padding
import Mathlib.Data.Fintype.Lattice
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax799700.ZeroOneIP
end Lax799700.ZeroOneIP

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Knapsack (BWBit BWItem BWLe BWPosn BWTarget BWTgt BWWeight HasSubsetSum)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.ZeroOneIP (HasZeroOneSolution IPCoef IPCoefVal IPCol IPLe IPPosn IPRhs IPRhsVal IPRow)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Knapsack (binWeights bwBit bwItem bwLe bwPosn bwTgt)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.ZeroOneIP (zeroOneIP)
end FirstOrder.Language

/-!
# 0-1 integer programming is NP-hard

A single equation with `0-1` variables *is* a subset-sum instance, so the
reduction from Knapsack is the identity in everything but the vocabulary: the
items become the columns, the target becomes the right-hand side, and the
whole instance becomes **one** equation.

The only thing to build is that single row. The interpretation has one tag and
dimension one, so its universe is a copy of the input
(`DescriptiveComplexity.IPRed.ipPt`); the row is the *minimum* of the input order,
which is the one element a first-order formula can name. Everything else –
columns, positions, bits, and the order carrying the place values, which stays
the input's own `le` – is read off unchanged, so no arithmetic appears
anywhere and the correctness proof is a transport of `binNum` along that copy.

Naming the minimum is the only use of the order, so this is an
`DescriptiveComplexity.OrderedFOReduction`; conveniently, being one also supplies the
finiteness and nonemptiness that make the minimum exist.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace IPRed

open Language Structure

/-! ### Formula builders over the ordered expansion of binary-weighted instances -/

/-- The ordered expansion of the language of binary-weighted instances. -/
abbrev bwOrd : Language := Lax799700.Knapsack.binWeights.sum Language.order

/-- The item symbol in the ordered expansion. -/
abbrev itemSym : bwOrd.Relations 1 := Sum.inl Lax799700.Knapsack.bwItem

/-- The position symbol in the ordered expansion. -/
abbrev posnSym : bwOrd.Relations 1 := Sum.inl Lax799700.Knapsack.bwPosn

/-- The bit symbol in the ordered expansion. -/
abbrev bitSym : bwOrd.Relations 2 := Sum.inl Lax799700.Knapsack.bwBit

/-- The target symbol in the ordered expansion. -/
abbrev tgtSym : bwOrd.Relations 1 := Sum.inl Lax799700.Knapsack.bwTgt

/-- The place-value order symbol in the ordered expansion. -/
abbrev leBwSym : bwOrd.Relations 2 := Sum.inl Lax799700.Knapsack.bwLe

section Builders

variable {α : Type}

/-- `x` is an item, as a formula. -/
def itemF (x : α) : bwOrd.Formula α := Relations.formula₁ itemSym (Term.var x)

/-- `x` is a bit position, as a formula. -/
def posnF (x : α) : bwOrd.Formula α := Relations.formula₁ posnSym (Term.var x)

/-- The weight of `i` has bit 1 at `p`, as a formula. -/
def bitF (i p : α) : bwOrd.Formula α :=
  Relations.formula₂ bitSym (Term.var i) (Term.var p)

/-- The target has bit 1 at `p`, as a formula. -/
def tgtF (p : α) : bwOrd.Formula α := Relations.formula₁ tgtSym (Term.var p)

/-- `x` is below `y` in the place-value order, as a formula. -/
def leBwF (x y : α) : bwOrd.Formula α :=
  Relations.formula₂ leBwSym (Term.var x) (Term.var y)

/-- `x` is a minimum of the *input* order, as a formula. -/
noncomputable def minF (x : α) : bwOrd.Formula α := botF (L := Lax799700.Knapsack.binWeights) x

end Builders

section RealizeBuilders

variable {α A : Type} [Lax799700.Knapsack.binWeights.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_itemF {x : α} : (itemF x).Realize v ↔ Lax799700.Knapsack.BWItem (v x) := by
  rw [itemF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posnF {x : α} : (posnF x).Realize v ↔ Lax799700.Knapsack.BWPosn (v x) := by
  rw [posnF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_bitF {i p : α} : (bitF i p).Realize v ↔ Lax799700.Knapsack.BWBit (v i) (v p) := by
  rw [bitF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_tgtF {p : α} : (tgtF p).Realize v ↔ Lax799700.Knapsack.BWTgt (v p) := by
  rw [tgtF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_leBwF {x y : α} : (leBwF x y).Realize v ↔ Lax799700.Knapsack.BWLe (v x) (v y) := by
  rw [leBwF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_minF {x : α} : (minF x).Realize v ↔ IsBot (v x) := realize_botF

end RealizeBuilders

/-! ### The interpretation -/

/-- The interpretation of a 0-1 integer program in a binary-weighted
instance: one column per item, one bit position per bit position, and a single
row – the minimum of the input order – whose entries are the weights and whose
right-hand side is the target. -/
noncomputable def ipInterp : Lax904597.Interpretations.FOInterpretation bwOrd Lax799700.ZeroOneIP.zeroOneIP Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .col => fun _ => itemF (0, 0)
    | _, .row => fun _ => minF (0, 0)
    | _, .posn => fun _ => posnF (0, 0)
    | _, .coef => fun _ => minF (0, 0) ⊓ itemF (1, 0) ⊓ posnF (2, 0) ⊓ bitF (1, 0) (2, 0)
    | _, .rhs => fun _ => minF (0, 0) ⊓ posnF (1, 0) ⊓ tgtF (1, 0)
    | _, .le => fun _ => leBwF (0, 0) (1, 0)

/-! ### The interpreted structure is a copy of the input -/

section Points

variable {A : Type}

/-- The point of the interpreted structure carrying `a`. -/
def ipPt (a : A) : ipInterp.Map A := ((), fun _ => a)

@[simp]
theorem ipPt_snd (a : A) (j : Fin 1) : (ipPt a).2 j = a := rfl

theorem ipPt_surj (q : ipInterp.Map A) : q = ipPt (q.2 0) := by
  obtain ⟨u, w⟩ := q
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext j
  exact congrArg w (Subsingleton.elim j 0)

theorem ipPt_injective : Function.Injective (ipPt (A := A)) := fun _ _ h =>
  congrArg (fun q : ipInterp.Map A => q.2 0) h

/-- The interpreted universe is a copy of the input, which is what makes the
whole correctness proof a transport. -/
def ipEquiv : A ≃ ipInterp.Map A where
  toFun := ipPt
  invFun := fun q => q.2 0
  left_inv := fun _ => rfl
  right_inv := fun q => (ipPt_surj q).symm

@[simp]
theorem ipEquiv_apply (a : A) : ipEquiv a = ipPt a := rfl

end Points

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Lax799700.Knapsack.binWeights.Structure A] [LinearOrder A]

@[simp]
theorem ipCol_iff (a : A) : Lax799700.ZeroOneIP.IPCol (ipPt a) ↔ Lax799700.Knapsack.BWItem a := by
  rw [Lax799700.ZeroOneIP.IPCol, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipRow_iff (a : A) : Lax799700.ZeroOneIP.IPRow (ipPt a) ↔ IsBot a := by
  rw [Lax799700.ZeroOneIP.IPRow, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipPosn_iff (a : A) : Lax799700.ZeroOneIP.IPPosn (ipPt a) ↔ Lax799700.Knapsack.BWPosn a := by
  rw [Lax799700.ZeroOneIP.IPPosn, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipCoef_iff (r j p : A) :
    Lax799700.ZeroOneIP.IPCoef (ipPt r) (ipPt j) (ipPt p) ↔ IsBot r ∧ Lax799700.Knapsack.BWItem j ∧ Lax799700.Knapsack.BWPosn p ∧ Lax799700.Knapsack.BWBit j p := by
  rw [Lax799700.ZeroOneIP.IPCoef, ipPt, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]

@[simp]
theorem ipRhs_iff (r p : A) :
    Lax799700.ZeroOneIP.IPRhs (ipPt r) (ipPt p) ↔ IsBot r ∧ Lax799700.Knapsack.BWPosn p ∧ Lax799700.Knapsack.BWTgt p := by
  rw [Lax799700.ZeroOneIP.IPRhs, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]

@[simp]
theorem ipLe_iff (a b : A) : Lax799700.ZeroOneIP.IPLe (ipPt a) (ipPt b) ↔ Lax799700.Knapsack.BWLe a b := by
  rw [Lax799700.ZeroOneIP.IPLe, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

/-- The interpreted order is the input's own place-value order, read on the
copy. -/
theorem isLinOrd_ipLe (h : Lax904597.Machines.IsLinOrd (Lax799700.Knapsack.BWLe (A := A))) :
    Lax904597.Machines.IsLinOrd (Lax799700.ZeroOneIP.IPLe (A := ipInterp.Map A)) :=
  IsLinOrd.of_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm) h

end Characterizations

/-! ### The numbers, transported -/

section Numbers

variable {A : Type} [Lax799700.Knapsack.binWeights.Structure A] [LinearOrder A]

/-- Transport of a decoded number along the copy: only bits at positions
matter, which is what lets the interpreted bits carry their guards. -/
private theorem binNum_ipPt (b : A → Prop) (b' : ipInterp.Map A → Prop)
    (hb : ∀ a : A, Lax799700.Knapsack.BWPosn a → (b a ↔ b' (ipPt a))) :
    Lax799700.Common.binNum (Lax799700.Knapsack.BWLe (A := A)) Lax799700.Knapsack.BWPosn b = Lax799700.Common.binNum (Lax799700.ZeroOneIP.IPLe (A := ipInterp.Map A)) Lax799700.ZeroOneIP.IPPosn b' := by
  have h1 : Lax799700.Common.binNum (Lax799700.ZeroOneIP.IPLe (A := ipInterp.Map A)) Lax799700.ZeroOneIP.IPPosn b' =
      Lax799700.Common.binNum (Lax799700.ZeroOneIP.IPLe (A := ipInterp.Map A)) Lax799700.ZeroOneIP.IPPosn fun q => b (q.2 0) := by
    refine binNum_congr_on fun q hq => ?_
    obtain ⟨a, rfl⟩ : ∃ a, q = ipPt a := ⟨q.2 0, ipPt_surj q⟩
    exact (hb a ((ipPosn_iff a).mp hq)).symm
  rw [h1]
  exact binNum_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm)
    (fun a => (ipPosn_iff a).symm) fun _ => Iff.rfl

/-- The entry of the single row in the column of an item is the weight of that
item. -/
theorem ipCoefVal_eq {r j : A} (hr : IsBot r) (hj : Lax799700.Knapsack.BWItem j) :
    Lax799700.ZeroOneIP.IPCoefVal (ipPt r) (ipPt j) = Lax799700.Knapsack.BWWeight j :=
  (binNum_ipPt (Lax799700.Knapsack.BWBit j) _ fun p hp => by
    rw [ipCoef_iff]
    exact ⟨fun h => ⟨hr, hj, hp, h⟩, fun h => h.2.2.2⟩).symm

/-- The right-hand side of the single row is the target. -/
theorem ipRhsVal_eq {r : A} (hr : IsBot r) : Lax799700.ZeroOneIP.IPRhsVal (ipPt r) = Lax799700.Knapsack.BWTarget A :=
  (binNum_ipPt Lax799700.Knapsack.BWTgt _ fun p hp => by
    rw [ipRhs_iff]
    exact ⟨fun h => ⟨hr, hp, h⟩, fun h => h.2.2⟩).symm

end Numbers

/-! ### Correctness

Stated for an explicit set of items and an explicit `0-1` vector, so that the
same lemmas give the equivalence of the two decision problems and the
bijection between their solutions
(`DescriptiveComplexity.Problems.ZeroOneIP.CountingHardness`). -/

section Correctness

variable {A : Type} [Lax799700.Knapsack.binWeights.Structure A] [LinearOrder A] [Finite A]

/-- The columns of a set of items. -/
def colsOf (S : A → Prop) (q : ipInterp.Map A) : Prop := S (q.2 0)

/-- The items of a set of columns. -/
def itemsOfCols (x : ipInterp.Map A → Prop) (a : A) : Prop := x (ipPt a)

omit [Finite A] in
/-- The order of the interpreted program is linear exactly when the input's
is. -/
theorem isLinOrd_bwLe_of_ipLe (hlin : Lax904597.Machines.IsLinOrd (Lax799700.ZeroOneIP.IPLe (A := ipInterp.Map A))) :
    Lax904597.Machines.IsLinOrd (Lax799700.Knapsack.BWLe (A := A)) :=
  IsLinOrd.of_equiv ipEquiv.symm (fun q q' => by
    rw [ipPt_surj q, ipPt_surj q', ipLe_iff]
    exact Iff.rfl) hlin

omit [Finite A] in
/-- **A set of items summing to the target solves the one-equation program.** -/
theorem zeroOneSol_colsOf {S : A → Prop} (hSi : ∀ i, S i → Lax799700.Knapsack.BWItem i)
    (hsum : (∑ᶠ i ∈ {i | S i}, Lax799700.Knapsack.BWWeight i) = Lax799700.Knapsack.BWTarget A) :
    (∀ q, colsOf S q → Lax799700.ZeroOneIP.IPCol q) ∧
      ∀ r : ipInterp.Map A, Lax799700.ZeroOneIP.IPRow r → (∑ᶠ j ∈ {j | colsOf S j}, Lax799700.ZeroOneIP.IPCoefVal r j) = Lax799700.ZeroOneIP.IPRhsVal r := by
  refine ⟨fun q hq => ?_, fun r hr => ?_⟩
  · rw [ipPt_surj q, ipCol_iff]
    exact hSi _ hq
  · obtain ⟨a, rfl⟩ : ∃ a, r = ipPt a := ⟨r.2 0, ipPt_surj r⟩
    have ha : IsBot a := (ipRow_iff a).mp hr
    have hbij : Set.BijOn ipPt {i : A | S i} {q : ipInterp.Map A | colsOf S q} :=
      ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, hq, (ipPt_surj q).symm⟩⟩
    rw [← finsum_mem_eq_of_bijOn ipPt hbij fun i hi => (ipCoefVal_eq ha (hSi i hi)).symm,
      hsum, ipRhsVal_eq ha]

omit [Finite A] in
/-- **A solution of the one-equation program is a set of items summing to the
target.** -/
theorem subsetSum_itemsOfCols {a₀ : A} (ha₀ : IsBot a₀) {x : ipInterp.Map A → Prop}
    (hxc : ∀ j, x j → Lax799700.ZeroOneIP.IPCol j)
    (heq : ∀ r : ipInterp.Map A, Lax799700.ZeroOneIP.IPRow r → (∑ᶠ j ∈ {j | x j}, Lax799700.ZeroOneIP.IPCoefVal r j) = Lax799700.ZeroOneIP.IPRhsVal r) :
    (∀ a, itemsOfCols x a → Lax799700.Knapsack.BWItem a) ∧
      (∑ᶠ i ∈ {i | itemsOfCols x i}, Lax799700.Knapsack.BWWeight i) = Lax799700.Knapsack.BWTarget A := by
  refine ⟨fun a ha => (ipCol_iff a).mp (hxc _ ha), ?_⟩
  have hrow : Lax799700.ZeroOneIP.IPRow (ipPt a₀) := (ipRow_iff a₀).mpr ha₀
  have hbij : Set.BijOn ipPt {i : A | itemsOfCols x i} {q : ipInterp.Map A | x q} := by
    refine ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, ?_, (ipPt_surj q).symm⟩⟩
    change x (ipPt (q.2 0))
    rw [← ipPt_surj q]
    exact hq
  have hstep : ∀ i : A, itemsOfCols x i → Lax799700.Knapsack.BWWeight i = Lax799700.ZeroOneIP.IPCoefVal (ipPt a₀) (ipPt i) :=
    fun i hi => (ipCoefVal_eq ha₀ ((ipCol_iff i).mp (hxc _ hi))).symm
  rw [finsum_mem_eq_of_bijOn ipPt hbij fun i hi => hstep i hi, heq _ hrow, ipRhsVal_eq ha₀]

end Correctness

end IPRed

end Lax280166Proofs.DescriptiveComplexity


