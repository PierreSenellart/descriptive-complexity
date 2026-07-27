/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.NatCard
import DescriptiveComplexity.Counting.Machine

/-!
# Registers as counters and as loop positions

The registers of `DescriptiveComplexity.Counting.Cfg` hold values in `WithBot V`, read in
two ways: as a *count*, through `DescriptiveComplexity.orank` (so `⊥` is `0` and each
cover adds one), and as a *loop position*, through
`DescriptiveComplexity.Counting.predSet` (the set of nodes already scanned). This file
collects the arithmetic of the two readings: how a cover moves a loop past one
more node, how the count of a set restricted to the scanned part grows, and
when a counter still has room to be incremented.
-/

namespace DescriptiveComplexity

namespace Counting

instance instFiniteWithBot {V : Type} [Finite V] : Finite (WithBot V) :=
  inferInstanceAs (Finite (Option V))

/-! ### Covers in a finite linear order -/

section Covers

variable {A : Type} [LinearOrder A] [Finite A]

/-- In a finite linear order, an element that is not a maximum is covered by
some element. -/
theorem exists_covBy_of_not_max {z : A} (hz : ¬∀ a : A, a ≤ z) : ∃ w : A, z ⋖ w := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => z < a).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => z < a).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => z < a).min'_mem hne)).2
  · intro c hzc hcw
    exact absurd ((Finset.univ.filter fun a : A => z < a).min'_le
      c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hzc⟩)) (not_le.mpr hcw)

end Covers

/-! ### Counts -/

section Counts

variable {A : Type} [LinearOrder A] [Finite A] {V : Type} [LinearOrder V] [Finite V]

omit [Finite V] in
@[simp] theorem orank_bot : orank (⊥ : WithBot V) = 0 := orank_eq_zero (fun _ => bot_le)

/-- The rank is strictly monotone. -/
theorem orank_lt_orank {a b : A} (h : a < b) : orank a < orank b := by
  refine Set.ncard_lt_ncard ⟨fun y hy => lt_trans hy h, ?_⟩ (Set.toFinite _)
  intro hsub
  exact absurd (hsub h) (lt_irrefl a)

/-- The rank determines the element. -/
theorem orank_inj {a b : A} (h : orank a = orank b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (orank_lt_orank hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (orank_lt_orank hgt))

/-- A counter whose value is still below the number of nodes can be
incremented. -/
theorem exists_covBy_of_orank_lt {r : WithBot V} (h : orank r < Nat.card V) :
    ∃ r' : WithBot V, r ⋖ r' := by
  by_cases hmax : ∀ a : WithBot V, a ≤ r
  · have : orank r = Nat.card (WithBot V) - 1 := orank_isTop hmax
    rw [show Nat.card (WithBot V) = Nat.card (Option V) from rfl, Finite.card_option] at this
    omega
  · exact exists_covBy_of_not_max hmax

end Counts

/-! ### Loop positions -/

section Positions

variable {V : Type} [LinearOrder V]

/-- The set of nodes strictly below the value of a register: the nodes a loop
holding that value has already scanned. -/
def predSet (r : WithBot V) : Set V := {y : V | (↑y : WithBot V) < r}

@[simp] theorem predSet_bot : predSet (⊥ : WithBot V) = ∅ := by
  ext y; simp [predSet]

theorem predSet_coe (x : V) : predSet (↑x : WithBot V) = {y : V | y < x} := by
  ext y; simp [predSet]

theorem mem_predSet_coe {x y : V} : y ∈ predSet (↑x : WithBot V) ↔ y < x := by
  simp [predSet]

theorem notMem_predSet_self (x : V) : x ∉ predSet (↑x : WithBot V) := by
  simp [predSet]

/-- At the least node, nothing has been scanned. -/
theorem predSet_of_isMin {x : V} (h : ∀ z : V, x ≤ z) : predSet (↑x : WithBot V) = ∅ := by
  ext y
  simp only [predSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  exact_mod_cast h y

/-- Past the greatest node, everything has been scanned. -/
theorem insert_predSet_of_isMax {x : V} (h : ∀ z : V, z ≤ x) :
    insert x (predSet (↑x : WithBot V)) = Set.univ := by
  ext y
  simp only [Set.mem_insert_iff, mem_predSet_coe, Set.mem_univ, iff_true]
  rcases lt_or_eq_of_le (h y) with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-- A cover of a register value holding a node advances the scan past exactly
that node. -/
theorem predSet_of_covBy {x : V} {r : WithBot V} (h : (↑x : WithBot V) ⋖ r) :
    predSet r = insert x (predSet (↑x : WithBot V)) := by
  obtain ⟨x', rfl⟩ : ∃ x' : V, r = ↑x' := by
    cases r with
    | bot => exact absurd h.lt (by simp)
    | coe x' => exact ⟨x', rfl⟩
  have hcov : x ⋖ x' := WithBot.coe_covBy_coe.mp h
  ext y
  simp only [mem_predSet_coe, Set.mem_insert_iff]
  rw [covBy_iff_lt_iff_le_left.mp hcov]
  exact le_iff_eq_or_lt

/-- A cover of a register value holding a node holds a node again. -/
theorem exists_coe_of_covBy {x : V} {r : WithBot V} (h : (↑x : WithBot V) ⋖ r) :
    ∃ x' : V, r = ↑x' ∧ x ⋖ x' := by
  cases r with
  | bot => exact absurd h.lt (by simp)
  | coe x' => exact ⟨x', rfl, WithBot.coe_covBy_coe.mp h⟩

/-- The value covering `⊥` is the least node. -/
theorem isMin_of_bot_covBy {r : WithBot V} (h : (⊥ : WithBot V) ⋖ r) :
    ∃ x : V, r = ↑x ∧ ∀ z : V, x ≤ z := by
  cases r with
  | bot => exact absurd h.lt (lt_irrefl _)
  | coe x =>
    refine ⟨x, rfl, fun z => ?_⟩
    have : IsMin x := WithBot.bot_covBy_coe.mp h
    exact (le_total z x).elim (fun hz => this hz) id

end Positions

/-! ### Counting the scanned part of a set -/

section Counting

variable {V : Type} [LinearOrder V] [Finite V] {P : Set V}

theorem ncard_inter_predSet_le (r : WithBot V) : (P ∩ predSet r).ncard ≤ P.ncard :=
  Set.ncard_le_ncard Set.inter_subset_left P.toFinite

omit [LinearOrder V] in
theorem ncard_le_card (P : Set V) : P.ncard ≤ Nat.card V := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ P) Set.finite_univ

omit [LinearOrder V] in
/-- Scanning one more node, of the set: its scanned count goes up by one. -/
theorem ncard_inter_insert_of_mem {Q P : Set V} {uu : V} (huP : uu ∉ P) (h : uu ∈ Q) :
    (Q ∩ insert uu P).ncard = (Q ∩ P).ncard + 1 := by
  rw [Set.inter_insert_of_mem h,
    Set.ncard_insert_of_notMem (fun hm => huP hm.2) (Set.toFinite _)]

omit [LinearOrder V] [Finite V] in
/-- Scanning one more node, outside the set: its scanned count is unchanged. -/
theorem ncard_inter_insert_of_notMem {Q P : Set V} {uu : V} (h : uu ∉ Q) :
    (Q ∩ insert uu P).ncard = (Q ∩ P).ncard := by
  rw [Set.inter_insert_of_notMem h]

omit [LinearOrder V] in
/-- Scanning one more node can only grow the scanned part of a set. -/
theorem ncard_inter_insert_le {Q P : Set V} {uu : V} :
    (Q ∩ P).ncard ≤ (Q ∩ insert uu P).ncard :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.subset_insert _ _)) (Set.toFinite _)

/-- Scanning past a node of the set increases its scanned count by one. -/
theorem ncard_inter_predSet_covBy_of_mem {x : V} {r : WithBot V} (h : (↑x : WithBot V) ⋖ r)
    (hx : x ∈ P) : (P ∩ predSet r).ncard = (P ∩ predSet (↑x : WithBot V)).ncard + 1 := by
  rw [predSet_of_covBy h, Set.inter_insert_of_mem hx,
    Set.ncard_insert_of_notMem (fun hmem => notMem_predSet_self x hmem.2) (Set.toFinite _)]

omit [Finite V] in
/-- Scanning past a node outside the set leaves its scanned count alone. -/
theorem ncard_inter_predSet_covBy_of_notMem {x : V} {r : WithBot V} (h : (↑x : WithBot V) ⋖ r)
    (hx : x ∉ P) : (P ∩ predSet r).ncard = (P ∩ predSet (↑x : WithBot V)).ncard := by
  rw [predSet_of_covBy h, Set.inter_insert_of_notMem hx]

/-- At the greatest node, the scanned count of the set is one short of its
total, if the node belongs to it. -/
theorem ncard_inter_predSet_isMax_of_mem {x : V} (h : ∀ z : V, z ≤ x) (hx : x ∈ P) :
    (P ∩ predSet (↑x : WithBot V)).ncard + 1 = P.ncard := by
  have hP : P = insert x (P ∩ predSet (↑x : WithBot V)) := by
    conv_lhs => rw [← Set.inter_univ P, ← insert_predSet_of_isMax h]
    rw [Set.inter_insert_of_mem hx]
  conv_rhs => rw [hP]
  rw [Set.ncard_insert_of_notMem (fun hmem => notMem_predSet_self x hmem.2) (Set.toFinite _)]

omit [Finite V] in
/-- At the greatest node, the scanned count of the set is its total, if the
node lies outside it. -/
theorem ncard_inter_predSet_isMax_of_notMem {x : V} (h : ∀ z : V, z ≤ x) (hx : x ∉ P) :
    (P ∩ predSet (↑x : WithBot V)).ncard = P.ncard := by
  conv_rhs => rw [← Set.inter_univ P, ← insert_predSet_of_isMax h,
    Set.inter_insert_of_notMem hx]

end Counting

end Counting

end DescriptiveComplexity
