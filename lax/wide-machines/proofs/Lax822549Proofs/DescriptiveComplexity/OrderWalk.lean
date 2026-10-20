/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Lax822549Proofs.DescriptiveComplexity.Padding
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
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

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Order guards -/

section Guards

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

end Pred

/-! ### The lexicographic successor of a tuple, coordinatewise -/

section TupSucc

variable {D : ℕ} {A : Type} [LinearOrder A]

/-- The tuple `t'` is the immediate successor of `t` in the lexicographic
order (most significant coordinate first), stated coordinatewise: the two
tuples agree before some position `p`, at `p` the second covers the first, and
after `p` the first is all maxima and the second all minima. This is the
condition the guard `DescriptiveComplexity.succTupF` realizes;
`DescriptiveComplexity.tupSucc_iff_covBy` identifies it with covering in
`Lex (Fin D → A)`. -/
def TupSucc (t t' : Fin D → A) : Prop :=
  ∃ p : Fin D, (∀ j, j < p → t j = t' j) ∧
    (t p < t' p ∧ ∀ a : A, ¬(t p < a ∧ a < t' p)) ∧
    ∀ j, p < j → (∀ a : A, a ≤ t j) ∧ (∀ a : A, t' j ≤ a)

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

/-- A tuple is a lexicographic bottom iff each coordinate is minimal. -/
theorem tup_isBot_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), toLex t ≤ u) ↔ ∀ (p : Fin D) (a : A), t p ≤ a := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    -- the update is strictly below `t`, so equality is impossible too
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := ofLex u) (t' := t)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))

/-- A tuple is a lexicographic top iff each coordinate is maximal. -/
theorem tup_isTop_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), u ≤ toLex t) ↔ ∀ (p : Fin D) (a : A), a ≤ t p := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))

/-- **Coordinatewise successors are lexicographic covers**: the condition of
the guard `DescriptiveComplexity.succTupF` says exactly that the second tuple covers
the first in `Lex (Fin D → A)`. -/
theorem tupSucc_iff_covBy {t t' : Fin D → A} :
    TupSucc t t' ↔ toLex t ⋖ toLex t' := by
  classical
  constructor
  · rintro ⟨p, hbefore, ⟨hplt, hpnb⟩, hafter⟩
    refine ⟨lex_lt_iff.mpr ⟨p, hbefore, hplt⟩, ?_⟩
    rintro u htu hut
    obtain ⟨i₁, h₁e, h₁l⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp htu
    obtain ⟨i₂, h₂e, h₂l⟩ := (lex_lt_iff (t := ofLex u) (t' := t')).mp hut
    rcases lt_trichotomy i₁ p with hip | hip | hip
    · rcases lt_trichotomy i₂ i₁ with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ (hii.trans hip)] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii, ← hbefore _ hip] at h₂l
        exact absurd (h₁l.trans h₂l) (lt_irrefl _)
      · rw [h₂e _ hii, ← hbefore _ hip] at h₁l
        exact absurd h₁l (lt_irrefl _)
    · rw [hip] at h₁e h₁l
      rcases lt_trichotomy i₂ p with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ hii] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii] at h₂l
        exact hpnb _ ⟨h₁l, h₂l⟩
      · exact absurd h₂l (not_lt.mpr ((hafter _ hii).2 _))
    · exact absurd h₁l (not_lt.mpr ((hafter _ hip).1 _))
  · rintro ⟨hlt, hnb⟩
    obtain ⟨p, hbefore, hpl⟩ := lex_lt_iff.mp hlt
    refine ⟨p, hbefore, ⟨hpl, fun b hb => ?_⟩, fun j hj => ⟨fun a => ?_, fun a => ?_⟩⟩
    · have h1 : toLex t < toLex (Function.update t p b) :=
        lex_lt_iff.mpr ⟨p, fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)],
          by rw [Function.update_self]; exact hb.1⟩
      have h2 : toLex (Function.update t p b) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact hbefore j hj,
          by rw [Function.update_self]; exact hb.2⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t j a) :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      have h2 : toLex (Function.update t j a) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t' j a) :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      have h2 : toLex (Function.update t' j a) < toLex t' :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      exact hnb h1 h2

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

end CovByCases

/-! ### The rank of an element of a finite linear order -/

section Rank

variable {A : Type} [LinearOrder A]

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. This converts a walk along covers into arithmetic, matching
tuple-indexed fixed-point stages with the `ℕ`-indexed
`DescriptiveComplexity.derivesIn`. -/
noncomputable def orank (z : A) : ℕ :=
  {y : A | y < z}.ncard

/-- A minimum has rank `0`. -/
theorem orank_eq_zero {z : A} (hz : ∀ a : A, z ≤ a) : orank z = 0 := by
  rw [orank]
  have : {y : A | y < z} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hz y
  simp [this]

variable [Finite A]

/-- Rank increases by one along a cover. -/
theorem orank_covBy {w z : A} (h : w ⋖ z) : orank z = orank w + 1 := by
  rw [orank, orank]
  have hset : {y : A | y < z} = insert w {y : A | y < w} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    rw [covBy_iff_lt_iff_le_left.mp h]
    exact le_iff_eq_or_lt
  rw [hset, Set.ncard_insert_of_notMem (by simp)]

/-- Rank is monotone. -/
theorem orank_le_orank {x y : A} (h : x ≤ y) : orank x ≤ orank y :=
  Set.ncard_le_ncard (fun _ hz => lt_of_lt_of_le hz h) (Set.toFinite _)

/-- Rank is strictly monotone. -/
theorem orank_lt_orank {x y : A} (h : x < y) : orank x < orank y :=
  Set.ncard_lt_ncard ⟨fun _ hz => lt_trans hz h, fun hsup => lt_irrefl x (hsup h)⟩
    (Set.toFinite _)

/-- **Rank reflects the order**: it is an order isomorphism onto an initial
segment of `ℕ`, which is what lets a walk along the order be replayed as
arithmetic. -/
theorem orank_le_iff {x y : A} : orank x ≤ orank y ↔ x ≤ y := by
  refine ⟨fun h => ?_, orank_le_orank⟩
  by_contra hxy
  exact absurd (orank_lt_orank (lt_of_not_ge hxy)) (by omega)

/-- Rank tells elements apart. -/
theorem orank_inj_iff {x y : A} : orank x = orank y ↔ x = y :=
  ⟨fun h => le_antisymm (orank_le_iff.mp h.le) (orank_le_iff.mp h.ge), fun h => h ▸ rfl⟩

/-- The rank determines the element. -/
theorem orank_inj {x y : A} (h : orank x = orank y) : x = y :=
  orank_inj_iff.mp h

/-- Rank is below the cardinality. -/
theorem orank_lt_card (x : A) : orank x < Nat.card A := by
  have hsub : {y : A | y < x} ⊆ {x}ᶜ := fun _ hy => ne_of_lt hy
  have hle : orank x ≤ Nat.card A - 1 := by
    rw [orank]
    calc {y : A | y < x}.ncard ≤ ({x}ᶜ : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card A - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
  have hpos : 0 < Nat.card A := Nat.card_pos_iff.mpr ⟨⟨x⟩, ‹Finite A›⟩
  omega

end Rank

end Lax822549Proofs.DescriptiveComplexity


