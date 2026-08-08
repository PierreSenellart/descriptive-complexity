/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Even
import DescriptiveComplexity.DetLogSpace
import DescriptiveComplexity.TransitiveClosurePull

/-!
# PARITY: the parity of a marked subset

The problem the switching lemma is about, and the one
`DescriptiveComplexity.EVEN` must not be confused with. The vocabulary is a
single unary predicate, so an instance is a finite set with a marked subset, and
the question is whether **the marked subset** has an even number of elements.

## Why it is here, given that EVEN is already here

`DescriptiveComplexity.EVEN` asks the parity of the *universe* – of the input's
length – and that is AC⁰: an AC⁰ circuit family is indexed by the length, and in
the logic the numeric predicates read the top rank
(`DescriptiveComplexity.even_ac0Definable`). PARITY asks the parity of *part of
the input*, and is the classical example of a problem **outside** AC⁰ (Ajtai;
Furst–Saxe–Sipser; Håstad). Keeping both in the catalog is what makes the
distinction concrete rather than a warning in a docstring.

What is proved here is the *easy* side of that separation, and it is worth
having on its own:

* **PARITY is in LOGSPACE** (`DescriptiveComplexity.parity_mem_LOGSPACE`), by one
  deterministic walk along the order: carry a bit, flip it at each marked
  element. The walk is `DescriptiveComplexity.parSpec`, its mode is the parity of
  the marked elements seen so far, and it is *functional* on the nose
  (`DescriptiveComplexity.functional_parSpec`), so determinizing changes nothing
  (`DescriptiveComplexity.TCSpec.det_accepts_iff`).
* **PARITY is not first-order definable**, even order-invariantly
  (`DescriptiveComplexity.parity_not_foDefinable`): EVEN is the special case where
  everything is marked, an FO reduction of one line
  (`DescriptiveComplexity.evenParityInterp`), and first-order definability travels
  backward along reductions.

## What would finish the story, and is not here

`AC⁰ ⊊ LOGSPACE` is now **one theorem away**: PARITY ∉ AC⁰. That theorem is the
switching lemma, a major formalization on its own, and nothing in this library
proves any AC⁰ lower bound. The gap is deliberate and documented; what is
recorded here is that the *other* three sides of the square – PARITY in LOGSPACE,
PARITY not in FO(≤), EVEN in AC⁰, AC⁰ inside PTIME – are theorems.
-/

/- The vocabulary of a marked subset lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.order` and the vocabularies of the rest of the
catalog. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the vocabulary of a marked subset: one unary
predicate. -/
inductive markedSetRel : ℕ → Type
  /-- `mark x`: the element `x` belongs to the marked subset. -/
  | mark : markedSetRel 1
  deriving DecidableEq

/-- The relational vocabulary of a *marked subset*: a finite set with a
distinguished subset of it. -/
protected def markedSet : Language :=
  ⟨fun _ => Empty, markedSetRel⟩
  deriving IsRelational

/-- The symbol for “is marked”. -/
abbrev markedSetMark : Language.markedSet.Relations 1 := .mark

/-- The marking symbol, in the ordered expansion. Sum-language symbols are
referenced through an abbreviation with a declared type, never as a raw
`Sum.inl`, or `rw` fails to match at implicit transparency. -/
abbrev markedSetMarkO : (Language.markedSet.sum Language.order).Relations 1 :=
  Sum.inl markedSetMark

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Problem

variable (A : Type) [Language.markedSet.Structure A]

/-- The marked subset of a structure. -/
def Marked : Set A :=
  {x : A | RelMap Language.markedSetMark ![x]}

variable {A}

@[simp]
theorem mem_marked_iff (x : A) : x ∈ Marked A ↔ RelMap Language.markedSetMark ![x] :=
  Iff.rfl

end Problem

/-- **PARITY**: the marked subset has an even number of elements. Contrast
`DescriptiveComplexity.EVEN`, which asks this of the *universe*: that one is AC⁰,
this one is the classical AC⁰ lower bound. -/
def PARITY : DecisionProblem Language.markedSet where
  Holds := fun A _ => Even (Marked A).ncard
  iso_invariant := fun {A B} _ _ e => by
    have hcard : (Marked A).ncard = (Marked B).ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun a => relMap_equiv₁ e _ a)
    rw [hcard]

/-- The value of PARITY, unfolded. -/
theorem parity_holds_iff (A : Type) [Language.markedSet.Structure A] :
    PARITY A ↔ Even (Marked A).ncard :=
  Iff.rfl

/-! ### PARITY is a deterministic walk

One bit, one element, one pass along the order: the mode is the parity of the
marked elements *up to and including* the current one, so it flips exactly at a
marked element. Both the successor and the new mode are determined by the current
node, which is why the walk is functional and the determinization is free. -/

section Membership

variable {A : Type} [Language.markedSet.Structure A] [LinearOrder A]

/-- `x` is marked, as a formula over the ordered expansion. -/
noncomputable def markF {α : Type} (x : α) :
    (Language.markedSet.sum Language.order).Formula α :=
  Relations.formula₁ Language.markedSetMarkO (Term.var x)

@[simp]
theorem realize_markF {α : Type} (x : α) (v : α → A) :
    (markF x).Realize v ↔ v x ∈ Marked A := by
  rw [markF, Formula.realize_rel₁]
  exact Iff.rfl

/-- The number of marked elements up to and including `x`. -/
noncomputable def parCount [Finite A] (x : A) : ℕ :=
  {y : A | y ≤ x ∧ y ∈ Marked A}.ncard

/-- The mode carried at `x`: whether an even number of marked elements has been
seen so far. -/
noncomputable def parMode [Finite A] (x : A) : Bool :=
  decide (Even (parCount x))

/-- The transition of the parity walk: step to the immediate successor, and flip
the mode exactly when the element stepped onto is marked. -/
noncomputable def parStep (m m' : Bool) :
    (Language.markedSet.sum Language.order).Formula (Fin 1 ⊕ Fin 1) :=
  succF (Sum.inl 0) (Sum.inr 0) ⊓
    (if m' = !m then markF (Sum.inr 0) else ∼(markF (Sum.inr 0)))

/-- The walk starts at the minimum, in the mode that element prescribes: even
unless the minimum is itself marked. -/
noncomputable def parSrc (m : Bool) :
    (Language.markedSet.sum Language.order).Formula (Fin 1) :=
  minF 0 ⊓ (if m then ∼(markF 0) else markF 0)

/-- The walk accepts at the maximum, in the even mode. -/
noncomputable def parTgt (m : Bool) :
    (Language.markedSet.sum Language.order).Formula (Fin 1) :=
  if m then maxF 0 else ⊥

/-- **PARITY as a single walk**: one element, one bit, flipped at the marked
elements. -/
noncomputable def parSpec : TCSpec Language.markedSet where
  Mode := Bool
  k := 1
  step := parStep
  src := parSrc
  tgt := parTgt

theorem realize_parStep (m m' : Bool) (x y : Fin 1 → A) :
    (parStep m m').Realize (Sum.elim x y) ↔
      x 0 ⋖ y 0 ∧ ((m' = !m ∧ y 0 ∈ Marked A) ∨ (m' = m ∧ y 0 ∉ Marked A)) := by
  rw [parStep, Formula.realize_inf, realize_succF]
  simp only [Sum.elim_inl, Sum.elim_inr]
  refine and_congr ⟨fun h => ⟨h.1, fun _ h₁ h₂ => h.2 _ ⟨h₁, h₂⟩⟩,
    fun h => ⟨h.1, fun _ ha => h.2 ha.1 ha.2⟩⟩ ?_
  split_ifs with h
  · rw [realize_markF]
    simp only [Sum.elim_inr]
    exact ⟨fun hy => Or.inl ⟨h, hy⟩, fun hy => by
      rcases hy with ⟨-, hy⟩ | ⟨hm, -⟩
      · exact hy
      · exact absurd (hm.symm.trans h) (by cases m <;> simp)⟩
  · rw [Formula.realize_not, realize_markF]
    simp only [Sum.elim_inr]
    refine ⟨fun hy => Or.inr ⟨?_, hy⟩, fun hy => ?_⟩
    · revert h
      cases m <;> cases m' <;> simp
    · rcases hy with ⟨hm, -⟩ | ⟨-, hy⟩
      · exact absurd hm h
      · exact hy

theorem step_parSpec_iff (m m' : Bool) (x y : Fin 1 → A) :
    parSpec.Step (m, x) (m', y) ↔
      x 0 ⋖ y 0 ∧ ((m' = !m ∧ y 0 ∈ Marked A) ∨ (m' = m ∧ y 0 ∉ Marked A)) :=
  realize_parStep m m' x y

theorem isSrc_parSpec_iff (m : Bool) (x : Fin 1 → A) :
    parSpec.IsSrc (m, x) ↔
      (∀ a : A, x 0 ≤ a) ∧
        ((m = true ∧ x 0 ∉ Marked A) ∨ (m = false ∧ x 0 ∈ Marked A)) := by
  change (parSrc m).Realize x ↔ _
  cases m <;> simp [parSrc]

theorem isTgt_parSpec_iff (m : Bool) (x : Fin 1 → A) :
    parSpec.IsTgt (m, x) ↔ m = true ∧ ∀ a : A, a ≤ x 0 := by
  change (parTgt m).Realize x ↔ _
  cases m <;> simp [parTgt]

variable [Finite A]

/-- A Boolean is not its own negation: what makes the “not marked” branch of the
step formula pin the mode. -/
private theorem bool_ne_not_self (b : Bool) : ¬(b = !b) := by cases b <;> simp

/-- The prefix of a minimum is the minimum itself, when it is marked. -/
theorem parCount_isMin_marked {z : A} (hz : ∀ a : A, z ≤ a) (hm : z ∈ Marked A) :
    parCount z = 1 := by
  have hset : {y : A | y ≤ z ∧ y ∈ Marked A} = {z} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.1 (hz y), fun h => ⟨h.le, by rw [h]; exact hm⟩⟩
  rw [parCount, hset, Set.ncard_singleton]

/-- The prefix of an unmarked minimum is empty. -/
theorem parCount_isMin_not_marked {z : A} (hz : ∀ a : A, z ≤ a) (hm : z ∉ Marked A) :
    parCount z = 0 := by
  have hset : {y : A | y ≤ z ∧ y ∈ Marked A} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hy
    rw [le_antisymm hy (hz y)]
    exact hm
  rw [parCount, hset, Set.ncard_empty]

/-- The prefix grows by one along a cover onto a marked element. -/
theorem parCount_covBy_marked {w z : A} (h : w ⋖ z) (hm : z ∈ Marked A) :
    parCount z = parCount w + 1 := by
  have hnot : z ∉ {y : A | y ≤ w ∧ y ∈ Marked A} := by
    simp only [Set.mem_setOf_eq, not_and]
    exact fun hzw => absurd hzw (not_le_of_gt h.lt)
  have hset : {y : A | y ≤ z ∧ y ∈ Marked A} = insert z {y : A | y ≤ w ∧ y ∈ Marked A} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hle, hy⟩
      rcases covBy_le_cases h hle with hw | he
      · exact Or.inr ⟨hw, hy⟩
      · exact Or.inl he
    · rintro (hy | ⟨hw, hy⟩)
      · rw [hy]
        exact ⟨le_refl z, hm⟩
      · exact ⟨hw.trans h.le, hy⟩
  rw [parCount, parCount, hset, Set.ncard_insert_of_notMem hnot]

/-- The prefix is unchanged along a cover onto an unmarked element. -/
theorem parCount_covBy_not_marked {w z : A} (h : w ⋖ z) (hm : z ∉ Marked A) :
    parCount z = parCount w := by
  have hset : {y : A | y ≤ z ∧ y ∈ Marked A} = {y : A | y ≤ w ∧ y ∈ Marked A} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hle, hy⟩
      rcases covBy_le_cases h hle with hw | he
      · exact ⟨hw, hy⟩
      · rw [he] at hy
        exact absurd hy hm
    · exact fun hy => ⟨hy.1.trans h.le, hy.2⟩
  rw [parCount, parCount, hset]

/-- The mode of a marked minimum is odd. -/
theorem parMode_isMin_marked {z : A} (hz : ∀ a : A, z ≤ a) (hm : z ∈ Marked A) :
    parMode z = false := by
  rw [parMode, parCount_isMin_marked hz hm]
  simp

/-- The mode of an unmarked minimum is even. -/
theorem parMode_isMin_not_marked {z : A} (hz : ∀ a : A, z ≤ a) (hm : z ∉ Marked A) :
    parMode z = true := by
  rw [parMode, parCount_isMin_not_marked hz hm]
  simp

/-- The mode flips along a cover onto a marked element. -/
theorem parMode_covBy_marked {w z : A} (h : w ⋖ z) (hm : z ∈ Marked A) :
    parMode z = !parMode w := by
  rw [parMode, parMode, parCount_covBy_marked h hm]
  cases Nat.even_or_odd (parCount w) with
  | inl he => simp [he, Nat.even_add_one]
  | inr ho => simp [Nat.even_add_one, Nat.not_even_iff_odd.mpr ho]

/-- The mode is unchanged along a cover onto an unmarked element. -/
theorem parMode_covBy_not_marked {w z : A} (h : w ⋖ z) (hm : z ∉ Marked A) :
    parMode z = parMode w := by
  rw [parMode, parMode, parCount_covBy_not_marked h hm]

/-- **The walk reaches every element**, in the mode its prefix prescribes. -/
theorem reach_parSpec {x₀ : A} (h₀ : ∀ a : A, x₀ ≤ a) (x : A) :
    parSpec.Reach (parMode x₀, fun _ => x₀) (parMode x, fun _ => x) := by
  induction x using order_induction with
  | hmin z hz =>
    have hzx : z = x₀ := le_antisymm (hz x₀) (h₀ z)
    subst hzx
    exact .refl
  | hstep w z hwz hnb ih =>
    have hcov : w ⋖ z := ⟨hwz, fun _ h₁ h₂ => hnb _ ⟨h₁, h₂⟩⟩
    refine ih.tail ((step_parSpec_iff _ _ _ _).mpr ⟨hcov, ?_⟩)
    by_cases hm : z ∈ Marked A
    · exact Or.inl ⟨parMode_covBy_marked hcov hm, hm⟩
    · exact Or.inr ⟨parMode_covBy_not_marked hcov hm, hm⟩

/-- **The mode of a reachable node is the parity of its prefix**: the invariant
that reads the walk backwards. -/
theorem parMode_of_reach {x₀ : A} :
    ∀ p : parSpec.Node A, parSpec.Reach (parMode x₀, fun _ => x₀) p →
      p.1 = parMode (p.2 (0 : Fin 1)) := by
  intro p h
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    obtain ⟨hcov, hmk⟩ := (step_parSpec_iff b.1 c.1 b.2 c.2).mp (by
      rw [Prod.mk.eta, Prod.mk.eta]; exact hbc)
    rcases hmk with ⟨hm, hmark⟩ | ⟨hm, hmark⟩
    · rw [hm, ih]
      exact (parMode_covBy_marked hcov hmark).symm
    · rw [hm, ih]
      exact (parMode_covBy_not_marked hcov hmark).symm

variable [Nonempty A]

/-- **The walk accepts exactly the structures whose marked subset is even**: it
visits every element once, from the minimum to the maximum, so the mode it ends
in is the parity of the whole marked subset. -/
theorem accepts_parSpec_iff : parSpec.Accepts A ↔ Even (Marked A).ncard := by
  obtain ⟨x₀, -, h₀'⟩ := Set.exists_min_image (Set.univ : Set A) id (Set.toFinite _)
    ⟨Classical.arbitrary A, trivial⟩
  obtain ⟨x₁, -, h₁'⟩ := Set.exists_max_image (Set.univ : Set A) id (Set.toFinite _)
    ⟨Classical.arbitrary A, trivial⟩
  have h₀ : ∀ a : A, x₀ ≤ a := fun a => h₀' a trivial
  have h₁ : ∀ a : A, a ≤ x₁ := fun a => h₁' a trivial
  have htotal : parCount x₁ = (Marked A).ncard := by
    rw [parCount]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, and_iff_right_iff_imp]
    exact fun _ => h₁ y
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨hu₁, hu₂⟩ := (isSrc_parSpec_iff u.1 u.2).mp hu
    obtain ⟨hv₁, hv₂⟩ := (isTgt_parSpec_iff v.1 v.2).mp hv
    have hmin : u.2 (0 : Fin 1) = x₀ := le_antisymm (hu₁ x₀) (h₀ _)
    have humode : u.1 = parMode (u.2 (0 : Fin 1)) := by
      rcases hu₂ with ⟨hm, hmark⟩ | ⟨hm, hmark⟩
      · rw [hm, parMode_isMin_not_marked hu₁ hmark]
      · rw [hm, parMode_isMin_marked hu₁ hmark]
    have hueq : u = (parMode (u.2 (0 : Fin 1)), fun _ => u.2 (0 : Fin 1)) := by
      refine Prod.ext humode (funext fun i => ?_)
      rw [show i = (0 : Fin 1) from Subsingleton.elim (α := Fin 1) i 0]
    rw [hueq, hmin] at huv
    have hend := parMode_of_reach (x₀ := x₀) _ huv
    rw [hv₁, parMode] at hend
    have hmax : v.2 (0 : Fin 1) = x₁ := le_antisymm (h₁ _) (hv₂ x₁)
    rw [hmax, htotal] at hend
    exact of_decide_eq_true hend.symm
  · intro hev
    refine ⟨(parMode x₀, fun _ => x₀), (parMode x₁, fun _ => x₁), ?_, ?_,
      reach_parSpec h₀ x₁⟩
    · refine (isSrc_parSpec_iff _ _).mpr ⟨h₀, ?_⟩
      by_cases hm : x₀ ∈ Marked A
      · exact Or.inr ⟨parMode_isMin_marked h₀ hm, hm⟩
      · exact Or.inl ⟨parMode_isMin_not_marked h₀ hm, hm⟩
    · refine (isTgt_parSpec_iff _ _).mpr ⟨?_, h₁⟩
      rw [parMode, htotal]
      exact decide_eq_true hev

omit [Nonempty A] in
/-- **The walk is functional**: the successor of an element is unique in a finite
linear order, and the new mode is determined by its markedness. -/
theorem functional_parSpec : parSpec.Functional A := by
  intro a b c hab hac
  obtain ⟨hcovb, hmb⟩ := (step_parSpec_iff a.1 b.1 a.2 b.2).mp (by
    rw [Prod.mk.eta, Prod.mk.eta]; exact hab)
  obtain ⟨hcovc, hmc⟩ := (step_parSpec_iff a.1 c.1 a.2 c.2).mp (by
    rw [Prod.mk.eta, Prod.mk.eta]; exact hac)
  have htup : b.2 (0 : Fin 1) = c.2 (0 : Fin 1) :=
    orank_inj (by rw [orank_covBy hcovb, orank_covBy hcovc])
  have hmode : b.1 = c.1 := by
    rcases hmb with ⟨hmb', hkb⟩ | ⟨hmb', hkb⟩ <;>
      rcases hmc with ⟨hmc', hkc⟩ | ⟨hmc', hkc⟩
    · rw [hmb', hmc']
    · rw [htup] at hkb
      exact absurd hkb hkc
    · rw [htup] at hkb
      exact absurd hkc hkb
    · rw [hmb', hmc']
  refine Prod.ext hmode (funext fun i => ?_)
  rw [show i = (0 : Fin 1) from Subsingleton.elim (α := Fin 1) i 0]
  exact htup

end Membership

/-- **PARITY is FO(DTC) definable**, by the deterministic parity walk: the
determinization changes nothing, the walk being functional. -/
theorem parity_dtcDefinable : DTCDefinable PARITY :=
  ⟨parSpec, fun A _ _ _ _ =>
    (parity_holds_iff A).trans
      ((accepts_parSpec_iff (A := A)).symm.trans
        (TCSpec.det_accepts_iff parSpec functional_parSpec).symm)⟩

/-- **PARITY is in LOGSPACE.** With `DescriptiveComplexity.parity_not_foDefinable`
below, and the AC⁰ layer, this is three of the four sides of `AC⁰ ⊊ LOGSPACE`;
the fourth is PARITY ∉ AC⁰, which this library does not prove. -/
theorem parity_mem_LOGSPACE : PARITY ∈ LOGSPACE :=
  (mem_LOGSPACE_iff PARITY).mpr parity_dtcDefinable

/-! ### EVEN is the special case where everything is marked -/

/-- The interpretation marking every element: EVEN read as an instance of
PARITY, one dimension and one tag. -/
noncomputable def evenParityInterp :
    FOInterpretation Language.empty Language.markedSet Unit 1 where
  relFormula {_} _ _ := ⊤

/-- Every point of the interpreted structure is marked. -/
theorem marked_evenParityInterp (A : Type) [Language.empty.Structure A] :
    Marked (evenParityInterp.Map A) = Set.univ := by
  ext p
  rw [mem_marked_iff]
  simp only [Set.mem_univ, iff_true]
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_top.mpr trivial

/-- **EVEN reduces to PARITY**: mark everything. -/
noncomputable def even_fo_reduction_parity : EVEN ≤ᶠᵒ PARITY where
  Tag := Unit
  dim := 1
  toInterpretation := evenParityInterp
  correct := fun A _ _ _ => by
    rw [parity_holds_iff, marked_evenParityInterp, Set.ncard_univ, even_holds_iff]
    refine Iff.of_eq (congrArg Even ?_)
    exact Nat.card_congr
      (((Equiv.punitProd (Fin 1 → A)).trans (Equiv.funUnique (Fin 1) A)).symm)

/-- **PARITY is not first-order definable**, even order-invariantly: EVEN is not
(`DescriptiveComplexity.even_not_foDefinable`), and it reduces to PARITY. -/
theorem parity_not_foDefinable : ¬FODefinable PARITY := fun h =>
  even_not_foDefinable (h.of_foReduction even_fo_reduction_parity)

end DescriptiveComplexity
