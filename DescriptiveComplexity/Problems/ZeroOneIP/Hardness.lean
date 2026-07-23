/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ZeroOneIP.Defs
import DescriptiveComplexity.Problems.Knapsack.Defs
import DescriptiveComplexity.Padding
import Mathlib.Data.Fintype.Lattice

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

namespace DescriptiveComplexity

open FirstOrder

namespace IPRed

open Language Structure

/-! ### Formula builders over the ordered expansion of binary-weighted instances -/

/-- The ordered expansion of the language of binary-weighted instances. -/
abbrev bwOrd : Language := Language.binWeights.sum Language.order

/-- The item symbol in the ordered expansion. -/
abbrev itemSym : bwOrd.Relations 1 := Sum.inl bwItem

/-- The position symbol in the ordered expansion. -/
abbrev posnSym : bwOrd.Relations 1 := Sum.inl bwPosn

/-- The bit symbol in the ordered expansion. -/
abbrev bitSym : bwOrd.Relations 2 := Sum.inl bwBit

/-- The target symbol in the ordered expansion. -/
abbrev tgtSym : bwOrd.Relations 1 := Sum.inl bwTgt

/-- The place-value order symbol in the ordered expansion. -/
abbrev leBwSym : bwOrd.Relations 2 := Sum.inl bwLe

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
noncomputable def minF (x : α) : bwOrd.Formula α := botF (L := Language.binWeights) x

end Builders

section RealizeBuilders

variable {α A : Type} [Language.binWeights.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_itemF {x : α} : (itemF x).Realize v ↔ BWItem (v x) := by
  rw [itemF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_posnF {x : α} : (posnF x).Realize v ↔ BWPosn (v x) := by
  rw [posnF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_bitF {i p : α} : (bitF i p).Realize v ↔ BWBit (v i) (v p) := by
  rw [bitF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_tgtF {p : α} : (tgtF p).Realize v ↔ BWTgt (v p) := by
  rw [tgtF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_leBwF {x y : α} : (leBwF x y).Realize v ↔ BWLe (v x) (v y) := by
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
noncomputable def ipInterp : FOInterpretation bwOrd Language.zeroOneIP Unit 1 where
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

variable {A : Type} [Language.binWeights.Structure A] [LinearOrder A]

@[simp]
theorem ipCol_iff (a : A) : IPCol (ipPt a) ↔ BWItem a := by
  rw [IPCol, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipRow_iff (a : A) : IPRow (ipPt a) ↔ IsBot a := by
  rw [IPRow, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipPosn_iff (a : A) : IPPosn (ipPt a) ↔ BWPosn a := by
  rw [IPPosn, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

@[simp]
theorem ipCoef_iff (r j p : A) :
    IPCoef (ipPt r) (ipPt j) (ipPt p) ↔ IsBot r ∧ BWItem j ∧ BWPosn p ∧ BWBit j p := by
  rw [IPCoef, ipPt, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]

@[simp]
theorem ipRhs_iff (r p : A) :
    IPRhs (ipPt r) (ipPt p) ↔ IsBot r ∧ BWPosn p ∧ BWTgt p := by
  rw [IPRhs, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]

@[simp]
theorem ipLe_iff (a b : A) : IPLe (ipPt a) (ipPt b) ↔ BWLe a b := by
  rw [IPLe, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]

/-- The interpreted order is the input's own place-value order, read on the
copy. -/
theorem isLinOrd_ipLe (h : IsLinOrd (BWLe (A := A))) :
    IsLinOrd (IPLe (A := ipInterp.Map A)) :=
  IsLinOrd.of_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm) h

end Characterizations

/-! ### The numbers, transported -/

section Numbers

variable {A : Type} [Language.binWeights.Structure A] [LinearOrder A]

/-- Transport of a decoded number along the copy: only bits at positions
matter, which is what lets the interpreted bits carry their guards. -/
private theorem binNum_ipPt (b : A → Prop) (b' : ipInterp.Map A → Prop)
    (hb : ∀ a : A, BWPosn a → (b a ↔ b' (ipPt a))) :
    binNum (BWLe (A := A)) BWPosn b = binNum (IPLe (A := ipInterp.Map A)) IPPosn b' := by
  have h1 : binNum (IPLe (A := ipInterp.Map A)) IPPosn b' =
      binNum (IPLe (A := ipInterp.Map A)) IPPosn fun q => b (q.2 0) := by
    refine binNum_congr_on fun q hq => ?_
    obtain ⟨a, rfl⟩ : ∃ a, q = ipPt a := ⟨q.2 0, ipPt_surj q⟩
    exact (hb a ((ipPosn_iff a).mp hq)).symm
  rw [h1]
  exact binNum_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm)
    (fun a => (ipPosn_iff a).symm) fun _ => Iff.rfl

/-- The entry of the single row in the column of an item is the weight of that
item. -/
theorem ipCoefVal_eq {r j : A} (hr : IsBot r) (hj : BWItem j) :
    IPCoefVal (ipPt r) (ipPt j) = BWWeight j :=
  (binNum_ipPt (BWBit j) _ fun p hp => by
    rw [ipCoef_iff]
    exact ⟨fun h => ⟨hr, hj, hp, h⟩, fun h => h.2.2.2⟩).symm

/-- The right-hand side of the single row is the target. -/
theorem ipRhsVal_eq {r : A} (hr : IsBot r) : IPRhsVal (ipPt r) = BWTarget A :=
  (binNum_ipPt BWTgt _ fun p hp => by
    rw [ipRhs_iff]
    exact ⟨fun h => ⟨hr, hp, h⟩, fun h => h.2.2⟩).symm

end Numbers

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.binWeights.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **Correctness of the reduction**: a binary-weighted instance has a set of
items summing to the target iff the one-equation program interpreted in it has
a `0-1` solution. -/
theorem hasSubsetSum_iff_hasZeroOneSolution :
    HasSubsetSum A ↔ HasZeroOneSolution (ipInterp.Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  haveI : Finite (ipInterp.Map A) := ipInterp.map_finite A
  constructor
  · rintro ⟨-, hlin, S, hSi, hsum⟩
    refine ⟨inferInstance, isLinOrd_ipLe hlin, fun q => S (q.2 0), fun q hq => ?_, ?_⟩
    · rw [ipPt_surj q, ipCol_iff]
      exact hSi _ hq
    · intro r hr
      obtain ⟨a, rfl⟩ : ∃ a, r = ipPt a := ⟨r.2 0, ipPt_surj r⟩
      have ha : IsBot a := (ipRow_iff a).mp hr
      have hbij : Set.BijOn ipPt {i : A | S i} {q : ipInterp.Map A | S (q.2 0)} :=
        ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, hq, (ipPt_surj q).symm⟩⟩
      rw [← finsum_mem_eq_of_bijOn ipPt hbij fun i hi => (ipCoefVal_eq ha (hSi i hi)).symm,
        hsum, ipRhsVal_eq ha]
  · rintro ⟨-, hlin, x, hxc, heq⟩
    have hlin' : IsLinOrd (BWLe (A := A)) :=
      IsLinOrd.of_equiv ipEquiv.symm (fun q q' => by
        rw [ipPt_surj q, ipPt_surj q', ipLe_iff]
        exact Iff.rfl) hlin
    refine ⟨inferInstance, hlin', fun a => x (ipPt a), fun a ha => ?_, ?_⟩
    · exact (ipCol_iff a).mp (hxc _ ha)
    · have hrow : IPRow (ipPt a₀) := (ipRow_iff a₀).mpr ha₀
      have hbij : Set.BijOn ipPt {i : A | x (ipPt i)} {q : ipInterp.Map A | x q} := by
        refine ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, ?_, (ipPt_surj q).symm⟩⟩
        change x (ipPt (q.2 0))
        rw [← ipPt_surj q]
        exact hq
      have hstep : ∀ i : A, x (ipPt i) → BWWeight i = IPCoefVal (ipPt a₀) (ipPt i) :=
        fun i hi => (ipCoefVal_eq ha₀ ((ipCol_iff i).mp (hxc _ hi))).symm
      rw [finsum_mem_eq_of_bijOn ipPt hbij fun i hi => hstep i hi, heq _ hrow,
        ipRhsVal_eq ha₀]

end Correctness

end IPRed

open IPRed in
/-- **Knapsack FO-reduces to 0-1 integer programming**, over any linear order
on the input: the items become the columns, the target the right-hand side,
and the whole instance a single equation, carried by the minimum of the
order. -/
noncomputable def knapsack_ordered_fo_reduction_zeroOneIP : Knapsack ≤ᶠᵒ[≤] ZeroOneIP where
  Tag := Unit
  dim := 1
  toInterpretation := ipInterp
  correct A _ _ _ _ := hasSubsetSum_iff_hasZeroOneSolution A

end DescriptiveComplexity
