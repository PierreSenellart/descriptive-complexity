/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Lax945089Proofs.DescriptiveComplexity.Ordered
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax945089Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax945089Proofs.DescriptiveComplexity

/-!
# Walking a finite linear order, first-order

Shared machinery for constructions that traverse a finite linear order – or the
lexicographic order on tuples – one step at a time, with each step described by
a first-order guard over the ordered expansion `L.sum Language.order`.

Two clients, one technique. The SO-Horn definition of HORN-SAT
(`DescriptiveComplexity.Problems.HornSat.Definability`) assembles the unbounded body of
an input clause by walking the order of its elements; the translation of
FO(LFP) into SO-Horn (`DescriptiveComplexity.FixedPointHorn`) walks the lexicographic
order of *stage* and *valuation* tuples to derive the complement of a fixed
point. Both need the same three ingredients, provided here:

* **guards**: formulas `DescriptiveComplexity.minF`, `DescriptiveComplexity.maxF`,
  `DescriptiveComplexity.succF` – being minimal, maximal, the immediate successor – and
  their tuple analogues `DescriptiveComplexity.minTupF`, `DescriptiveComplexity.maxTupF`,
  `DescriptiveComplexity.succTupF` for the lexicographic order, with realization lemmas
  phrased purely in terms of the order of the structure;
* **induction**: `DescriptiveComplexity.order_induction`, walking any finite linear order
  from its minimum along immediate successors – applied not only to the
  universe of a structure but to lexicographic tuple orders over it;
* **the bridge to `Lex`**: the coordinatewise conditions realized by the tuple
  guards characterize bottom, top and covering
  (`DescriptiveComplexity.tupSucc_iff_covBy`…) in `Lex (Fin D → A)`, and
  `DescriptiveComplexity.prodLex_covBy_iff`/`DescriptiveComplexity.finCovBy_iff` do the same for
  the lexicographic product heading a static index; so a walk described by
  guards is a walk along covers of a bona fide finite linear order.

Finally `DescriptiveComplexity.orank` – the rank of an element of a finite linear order,
the number of its strict predecessors – converts that walk into arithmetic:
rank `0` at the bottom (`DescriptiveComplexity.orank_eq_zero`), `+1` along a cover
(`DescriptiveComplexity.orank_covBy`), `Nat.card - 1` at the top
(`DescriptiveComplexity.orank_isTop`). This is how a fixed-point stage indexed by a
tuple is matched with the `ℕ`-indexed stages of
`DescriptiveComplexity.derivesIn`.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Order guards -/

section Guards

variable {L : Language.{0, 0}} {α : Type}

/-- `x ≤ y`, as a formula over the ordered expansion. -/
noncomputable def leF (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x < y`, as a formula over the ordered expansion. -/
noncomputable def ltF (x y : α) : (L.sum Language.order).Formula α :=
  leF x y ⊓ ∼(leF y x)

/-- The variable `x` holds a minimum. -/
noncomputable def minF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Sum.inl x) (Sum.inr 0)).iAlls (Fin 1)

/-- The variable `x` holds a maximum. -/
noncomputable def maxF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Sum.inr 0) (Sum.inl x)).iAlls (Fin 1)

/-- `w` holds the immediate predecessor of `z`. -/
noncomputable def succF (w z : α) : (L.sum Language.order).Formula α :=
  ltF w z ⊓
    (show (L.sum Language.order).Formula (α ⊕ Fin 1) from
      ∼(ltF (Sum.inl w) (Sum.inr 0) ⊓ ltF (Sum.inr 0) (Sum.inl z))).iAlls (Fin 1)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_leF (x y : α) : (leF (L := L) x y).Realize v ↔ v x ≤ v y := by
  rw [leF, Formula.realize_rel₂, relMap_leSymb]
  exact Iff.rfl

@[simp]
theorem realize_ltF (x y : α) : (ltF (L := L) x y).Realize v ↔ v x < v y := by
  rw [ltF, Formula.realize_inf, Formula.realize_not, realize_leF, realize_leF]
  exact lt_iff_le_not_ge.symm

@[simp]
theorem realize_minF (x : α) : (minF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

@[simp]
theorem realize_maxF (x : α) : (maxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [maxF]
  simp only [Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

@[simp]
theorem realize_succF (w z : α) :
    (succF (L := L) w z).Realize v ↔ v w < v z ∧ ∀ a : A, ¬(v w < a ∧ a < v z) := by
  rw [succF]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_not, realize_ltF,
    Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

end Guards

/-! ### Immediate predecessors, and induction along a finite linear order -/

section Pred

variable {A : Type} [LinearOrder A] [Finite A]

/-- In a finite linear order, an element that is not a minimum has an
immediate predecessor. -/
theorem exists_succ_of_not_min {z : A} (hz : ¬∀ a : A, z ≤ a) :
    ∃ w : A, w < z ∧ ∀ a : A, ¬(w < a ∧ a < z) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => a < z).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => a < z).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => a < z).max'_mem hne)).2
  · rintro a ⟨hwa, haz⟩
    exact absurd ((Finset.univ.filter fun a : A => a < z).le_max'
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, haz⟩)) (not_le.mpr hwa)

/-- Induction along a finite linear order: from the minimum, one immediate
successor at a time. -/
theorem order_induction {P : A → Prop} (hmin : ∀ z : A, (∀ a : A, z ≤ a) → P z)
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) → P w → P z) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedLT (α := A)).wf.induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, z ≤ a
    · exact hmin z hz
    · obtain ⟨w, hwz, hnb⟩ := exists_succ_of_not_min hz
      exact hstep w z hwz hnb (ih w hwz)

end Pred

/-! ### The lexicographic successor of a tuple, coordinatewise -/

section TupSucc

end TupSucc

/-! ### Tuple guards, for the lexicographic order -/

section TupGuards

end TupGuards

/-! ### The bridge to `Lex`: bottom, top and covering, coordinatewise

The tuple guards above speak coordinatewise; the walk they describe is along
the finite linear order `Lex (Fin D → A)`. These lemmas identify the two
languages. (`Lex` is a type synonym, so `Finite` and `Nonempty` instances are
provided for it here.) -/

section LexBridge

instance {α : Type*} [Finite α] : Finite (Lex α) := Finite.of_equiv α toLex

instance {α : Type*} [Nonempty α] : Nonempty (Lex α) := Nonempty.map toLex ‹_›

/-! #### The lexicographic product with a static head -/

end LexBridge

/-! ### Deciding the lexicographic order of two tuples

`DescriptiveComplexity.succTupF` *walks* the lexicographic order; the two
guards below *decide* it, which is what a reduction defining the order of its
image has to do. They are stated at arbitrary selectors `sel`, `sel'` into a
shared variable type, rather than at the fixed layout `Fin 2 × Fin D` of
`DescriptiveComplexity.lexTupleLeF`, because their consumers compare tuples
sitting at arbitrary positions among the free variables. -/

section LexDecide

end LexDecide

/-! ### Reaching an element from below a cover -/

section CovByCases

variable {α : Type*} [LinearOrder α]

/-- Whatever is below a cover is below its base, or is the cover itself. -/
theorem covBy_le_cases {a b c : α} (h : a ⋖ b) (hc : c ≤ b) : c ≤ a ∨ c = b := by
  rcases lt_or_eq_of_le hc with hlt | he
  · exact Or.inl ((covBy_iff_lt_iff_le_left.mp h).mp hlt)
  · exact Or.inr he

end CovByCases

/-! ### The rank of an element of a finite linear order -/

section Rank

variable {A : Type} [LinearOrder A]

/-- A minimum has rank `0`. -/
theorem orank_eq_zero {z : A} (hz : ∀ a : A, z ≤ a) : Lax895169.BitPredicate.orank z = 0 := by
  rw [Lax895169.BitPredicate.orank]
  have : {y : A | y < z} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hz y
  simp [this]

variable [Finite A]

/-- Rank increases by one along a cover. -/
theorem orank_covBy {w z : A} (h : w ⋖ z) : Lax895169.BitPredicate.orank z = Lax895169.BitPredicate.orank w + 1 := by
  rw [Lax895169.BitPredicate.orank, Lax895169.BitPredicate.orank]
  have hset : {y : A | y < z} = insert w {y : A | y < w} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    rw [covBy_iff_lt_iff_le_left.mp h]
    exact le_iff_eq_or_lt
  rw [hset, Set.ncard_insert_of_notMem (by simp)]

/-- Rank is monotone. -/
theorem orank_le_orank {x y : A} (h : x ≤ y) : Lax895169.BitPredicate.orank x ≤ Lax895169.BitPredicate.orank y :=
  Set.ncard_le_ncard (fun _ hz => lt_of_lt_of_le hz h) (Set.toFinite _)

/-- Rank is strictly monotone. -/
theorem orank_lt_orank {x y : A} (h : x < y) : Lax895169.BitPredicate.orank x < Lax895169.BitPredicate.orank y :=
  Set.ncard_lt_ncard ⟨fun _ hz => lt_trans hz h, fun hsup => lt_irrefl x (hsup h)⟩
    (Set.toFinite _)

/-- **Rank reflects the order**: it is an order isomorphism onto an initial
segment of `ℕ`, which is what lets a walk along the order be replayed as
arithmetic. -/
theorem orank_le_iff {x y : A} : Lax895169.BitPredicate.orank x ≤ Lax895169.BitPredicate.orank y ↔ x ≤ y := by
  refine ⟨fun h => ?_, orank_le_orank⟩
  by_contra hxy
  exact absurd (orank_lt_orank (lt_of_not_ge hxy)) (by omega)

/-- Rank tells elements apart. -/
theorem orank_inj_iff {x y : A} : Lax895169.BitPredicate.orank x = Lax895169.BitPredicate.orank y ↔ x = y :=
  ⟨fun h => le_antisymm (orank_le_iff.mp h.le) (orank_le_iff.mp h.ge), fun h => h ▸ rfl⟩

/-- The rank determines the element. -/
theorem orank_inj {x y : A} (h : Lax895169.BitPredicate.orank x = Lax895169.BitPredicate.orank y) : x = y :=
  orank_inj_iff.mp h

/-- Rank is below the cardinality. -/
theorem orank_lt_card (x : A) : Lax895169.BitPredicate.orank x < Nat.card A := by
  have hsub : {y : A | y < x} ⊆ {x}ᶜ := fun _ hy => ne_of_lt hy
  have hle : Lax895169.BitPredicate.orank x ≤ Nat.card A - 1 := by
    rw [Lax895169.BitPredicate.orank]
    calc {y : A | y < x}.ncard ≤ ({x}ᶜ : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card A - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
  have hpos : 0 < Nat.card A := Nat.card_pos_iff.mpr ⟨⟨x⟩, ‹Finite A›⟩
  omega

/-- **Every position below the cardinality is a rank**: the ranks exhaust the
initial segment, by injectivity between two finite types of the same size. -/
theorem exists_orank_eq {m : ℕ} (h : m < Nat.card A) : ∃ x : A, Lax895169.BitPredicate.orank x = m := by
  classical
  let := Fintype.ofFinite A
  have hcard : Fintype.card A = Fintype.card (Fin (Nat.card A)) := by
    rw [Fintype.card_fin, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective
      (fun x : A => (⟨Lax895169.BitPredicate.orank x, orank_lt_card x⟩ : Fin (Nat.card A))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy => orank_inj_iff.mp (congrArg Fin.val hxy), hcard⟩
  obtain ⟨x, hx⟩ := hbij.2 ⟨m, h⟩
  exact ⟨x, congrArg Fin.val hx⟩

/-- A maximum has rank `Nat.card A - 1`. -/
theorem orank_isTop {z : A} (hz : ∀ a : A, a ≤ z) : Lax895169.BitPredicate.orank z = Nat.card A - 1 := by
  rw [Lax895169.BitPredicate.orank]
  have hset : {y : A | y < z} = {z}ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨ne_of_lt, fun h => lt_of_le_of_ne (hz y) h⟩
  rw [hset, Set.ncard_compl, Set.ncard_singleton]

end Rank

end Lax945089Proofs.DescriptiveComplexity


