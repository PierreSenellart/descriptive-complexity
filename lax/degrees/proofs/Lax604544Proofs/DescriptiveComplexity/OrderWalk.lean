/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Lax604544Proofs.DescriptiveComplexity.Padding
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

namespace Lax604544Proofs.DescriptiveComplexity

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

/-- In a finite linear order, an element that is not a maximum has an
immediate successor. -/
theorem exists_gt_of_not_max {z : A} (hz : ¬∀ a : A, a ≤ z) :
    ∃ w : A, z < w ∧ ∀ a : A, ¬(z < a ∧ a < w) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => z < a).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => z < a).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => z < a).min'_mem hne)).2
  · rintro a ⟨hza, haw⟩
    exact absurd ((Finset.univ.filter fun a : A => z < a).min'_le
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hza⟩)) (not_le.mpr haw)

/-- Induction along a finite linear order, downwards: from the maximum, one
immediate predecessor at a time. This is the direction a *scan* is proved
correct in – a walk that stops at the greatest element knows about the elements
above the one it stands on. -/
theorem order_induction_down {P : A → Prop} (hmax : ∀ z : A, (∀ a : A, a ≤ z) → P z)
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) → P z → P w) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedGT (α := A)).wf.induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, a ≤ z
    · exact hmax z hz
    · obtain ⟨w, hzw, hnb⟩ := exists_gt_of_not_max hz
      exact hstep z w hzw hnb (ih w hzw)

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

variable {D : ℕ} {A : Type} [LinearOrder A]

theorem lex_lt_iff {t t' : Fin D → A} :
    toLex t < toLex t' ↔ ∃ p, (∀ j, j < p → t j = t' j) ∧ t p < t' p :=
  Iff.rfl

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

variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}

/-- The tuple held by `sel` is lexicographically strictly below the one held by
`sel'`: the two agree before some coordinate, at which the first is strictly
smaller. -/
noncomputable def lexSelLtF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listSup ((List.finRange D).map fun p =>
    listInf (((List.finRange D).filter fun j => j < p).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j))) ⊓
    ltF (sel p) (sel' p))

/-- The tuple held by `sel` is lexicographically below or equal to the one held
by `sel'`. -/
noncomputable def lexSelLeF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  lexSelLtF sel sel' ⊔
    listInf ((List.finRange D).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j)))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_lexSelLtF (sel sel' : Fin D → γ) :
    (lexSelLtF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) < toLex (v ∘ sel') := by
  rw [lexSelLtF, realize_listSup, lex_lt_iff]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, realize_listInf, realize_ltF] at hr
    refine ⟨p, fun j hj => ?_, hr.2⟩
    have := hr.1 _ (List.mem_map.mpr
      ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · rintro ⟨p, hag, hp⟩
    refine ⟨_, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf, realize_ltF]
    refine ⟨fun φ hφ => ?_, hp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact hag j (by simpa using (List.mem_filter.mp hj).2)

@[simp]
theorem realize_lexSelLeF (sel sel' : Fin D → γ) :
    (lexSelLeF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) ≤ toLex (v ∘ sel') := by
  rw [lexSelLeF, Formula.realize_sup, realize_lexSelLtF, realize_listInf, le_iff_lt_or_eq]
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    refine funext fun j => ?_
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h φ hφ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun h j

end LexDecide

/-! ### Reaching an element from below a cover -/

section CovByCases

end CovByCases

/-! ### The rank of an element of a finite linear order -/

section Rank

end Rank

end Lax604544Proofs.DescriptiveComplexity


