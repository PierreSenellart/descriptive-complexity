/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Numbers.Unary
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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

namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax794877Proofs.DescriptiveComplexity.IsLinOrd
end Lax794877Proofs.DescriptiveComplexity.IsLinOrd

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum bitRank)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (MaxPos)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Binary numbers carried by a relation

The layer between `DescriptiveComplexity.Numbers.Binary`, which decodes a set of bits
sitting on a genuine `LinearOrder`, and the problems carrying binary numbers,
whose order is a *relation symbol* of the vocabulary and therefore an
arbitrary binary relation until the yes-instances say otherwise.

* `DescriptiveComplexity.IsLinOrd` – being a linear order, as a property of a relation,
  first-order and foldable into the yes-instances;
* `DescriptiveComplexity.bitRank` – the rank of a position, the number of positions
  strictly below it, defined for an arbitrary relation;
* `DescriptiveComplexity.binNum` – the decoding `∑ 2 ^ rank`, over a *set* of positions
  via `finsum`, so that it is total and needs no finiteness to be stated.

Everything transports along equivalences commuting with the relations, which
is what the `DecisionProblem.iso_invariant` proofs of the group need.

The arithmetic the `Σ₁` definitions need – that a bitwise ripple-carry chain
computes an addition – is built on `DescriptiveComplexity.binNum_peel_min`, which
peels the lowest position off a decoded number: `binNum = bit at the bottom +
2 * (the rest)`, the recursion binary numbers actually satisfy. The same
recursion gives the two facts a kernel needs about *whole* numbers rather than
their bits: `DescriptiveComplexity.binNum_inj_on`, two numbers are equal exactly when
their bits agree, and `DescriptiveComplexity.binNum_lt_iff`, one is smaller exactly
when they differ and the higher bit is the second's – both bitwise, hence
first-order, which is why a kernel can compare numbers it has guessed.
-/

namespace Lax794877Proofs.DescriptiveComplexity

/-! ### Linear orders, as a property of a relation -/

section LinOrd

variable {A : Type}

/-! ### Building linear orders

Reductions into a problem carrying binary numbers have to *construct* the
order of the instance they produce, and a `Σ₁` certificate sometimes has to
exhibit one. Both do it the same way: read the elements through a key into a
lexicographic product of orders already at hand. -/

section Build

end Build

end LinOrd

/-! ### Decoding a set of positions -/

section Decode

variable {A : Type}

/-- Only the bits at positions matter. -/
theorem binNum_congr_on {Le : A → A → Prop} {Posn b b' : A → Prop}
    (h : ∀ p, Posn p → (b p ↔ b' p)) : Lax799700.Common.binNum Le Posn b = Lax799700.Common.binNum Le Posn b' := by
  have hset : {p | Posn p ∧ b p} = {p | Posn p ∧ b' p} := by
    ext p
    exact and_congr_right fun hp => h p hp
  rw [Lax799700.Common.binNum, Lax799700.Common.binNum, hset]

/-- The value of the empty set of positions is zero. -/
@[simp]
theorem binNum_bot (Le : A → A → Prop) (Posn : A → Prop) :
    Lax799700.Common.binNum Le Posn (fun _ => False) = 0 := by
  have : {p | Posn p ∧ False} = (∅ : Set A) := by
    ext p
    simp
  rw [Lax799700.Common.binNum, this, finsum_mem_empty]

/-! On a finite universe both are finite sums over `Finset`s, which is what a
decoder computes. The `Decidable` arguments are what makes those `Finset`s
constructible; nothing here needs the relations to be well-behaved. -/

section Finite

end Finite

end Decode

/-! ### Peeling the lowest position -/

section Peel

variable {A : Type} [Finite A]

/-- Removing the lowest position lowers every other rank by one. -/
theorem bitRank_erase_min {Le : A → A → Prop} {Posn : A → Prop} {p₀ : A}
    (h₀ : Posn p₀) (hmin : ∀ q, Posn q → Le p₀ q) {p : A} (hp : Posn p) (hne : p ≠ p₀) :
    Lax799700.Common.bitRank Le Posn p = Lax799700.Common.bitRank Le (fun q => Posn q ∧ q ≠ p₀) p + 1 := by
  have hsplit : {q : A | Posn q ∧ Le q p ∧ q ≠ p} =
      insert p₀ {q : A | (Posn q ∧ q ≠ p₀) ∧ Le q p ∧ q ≠ p} := by
    ext q
    constructor
    · rintro ⟨hq, hle, hqp⟩
      rcases eq_or_ne q p₀ with rfl | hq₀
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨⟨hq, hq₀⟩, hle, hqp⟩
    · rintro (rfl | ⟨⟨hq, -⟩, hle, hqp⟩)
      · exact ⟨h₀, hmin p hp, Ne.symm hne⟩
      · exact ⟨hq, hle, hqp⟩
  have hnot : p₀ ∉ {q : A | (Posn q ∧ q ≠ p₀) ∧ Le q p ∧ q ≠ p} := by
    rintro ⟨⟨-, hcon⟩, -, -⟩
    exact hcon rfl
  rw [Lax799700.Common.bitRank, Lax799700.Common.bitRank, hsplit, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]

open Classical in
/-- **The recursion binary numbers satisfy**: the value is the lowest bit plus
twice the value of the rest. -/
theorem binNum_peel_min {Le : A → A → Prop} {Posn b : A → Prop} {p₀ : A}
    (hlin : Lax904597.Machines.IsLinOrd Le) (h₀ : Posn p₀) (hmin : ∀ q, Posn q → Le p₀ q) :
    Lax799700.Common.binNum Le Posn b =
      (if b p₀ then 1 else 0) + 2 * Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b := by
  classical
  have hrank₀ : Lax799700.Common.bitRank Le Posn p₀ = 0 := by
    have : {q : A | Posn q ∧ Le q p₀ ∧ q ≠ p₀} = (∅ : Set A) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hq, hle, hne⟩
      exact hne (hlin.2.2.1 q p₀ hle (hmin q hq))
    rw [Lax799700.Common.bitRank, this, Set.ncard_empty]
  -- split the sum at the lowest position
  have hsplit : {p : A | Posn p ∧ b p} =
      {p : A | (Posn p ∧ p ≠ p₀) ∧ b p} ∪ {p : A | p = p₀ ∧ b p} := by
    ext p
    constructor
    · rintro ⟨hp, hb⟩
      rcases eq_or_ne p p₀ with rfl | hne
      · exact Or.inr ⟨rfl, hb⟩
      · exact Or.inl ⟨⟨hp, hne⟩, hb⟩
    · rintro (⟨⟨hp, -⟩, hb⟩ | ⟨rfl, hb⟩)
      · exact ⟨hp, hb⟩
      · exact ⟨h₀, hb⟩
  have hdisj : Disjoint {p : A | (Posn p ∧ p ≠ p₀) ∧ b p} {p : A | p = p₀ ∧ b p} := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨-, hne⟩, -⟩ ⟨rfl, -⟩
    exact hne rfl
  rw [Lax799700.Common.binNum, hsplit, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  have hsecond : (∑ᶠ p ∈ {p : A | p = p₀ ∧ b p}, 2 ^ Lax799700.Common.bitRank Le Posn p)
      = if b p₀ then 1 else 0 := by
    by_cases hb : b p₀
    · have : {p : A | p = p₀ ∧ b p} = {p₀} := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hb⟩⟩
      rw [this, finsum_mem_singleton, hrank₀, if_pos hb, pow_zero]
    · have : {p : A | p = p₀ ∧ b p} = (∅ : Set A) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hcon⟩
        exact hb hcon
      rw [this, finsum_mem_empty, if_neg hb]
  have hfirst : (∑ᶠ p ∈ {p : A | (Posn p ∧ p ≠ p₀) ∧ b p}, 2 ^ Lax799700.Common.bitRank Le Posn p)
      = 2 * Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b := by
    rw [Lax799700.Common.binNum, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (Posn p ∧ p ≠ p₀) ∧ b p := by simpa using hp
    rw [bitRank_erase_min h₀ hmin hp'.1.1 hp'.1.2, pow_succ]
    ring
  rw [hfirst, hsecond, Nat.add_comm]

end Peel

/-! ### The full adder -/

section Adder

end Adder

/-! ### Ripple-carry addition -/

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- A nonempty set of positions has a lowest one: minimize the rank. -/
theorem exists_minPos (hlin : Lax904597.Machines.IsLinOrd Le) (hne : ∃ p, Posn p) :
    ∃ p, Lax904597.Machines.MinPos Le Posn p := by
  classical
  obtain ⟨p₀, hp₀, hmin⟩ :=
    Set.exists_min_image {p : A | Posn p} (Lax799700.Common.bitRank Le Posn) (Set.toFinite _) hne
  refine ⟨p₀, hp₀, fun q hq => ?_⟩
  by_contra hle
  have hql : Le q p₀ := (hlin.2.2.2 p₀ q).resolve_left hle
  have hne' : q ≠ p₀ := fun h => hle (h ▸ hlin.1 q)
  have hsub : {r : A | Posn r ∧ Le r q ∧ r ≠ q} ⊆ {r : A | Posn r ∧ Le r p₀ ∧ r ≠ p₀} := by
    rintro r ⟨hr, hrq, hrne⟩
    refine ⟨hr, hlin.2.1 r q p₀ hrq hql, fun hcon => ?_⟩
    exact hrne (hlin.2.2.1 r q hrq (hcon ▸ hql))
  have hmem : q ∈ {r : A | Posn r ∧ Le r p₀ ∧ r ≠ p₀} := ⟨hq, hql, hne'⟩
  have hnot : q ∉ {r : A | Posn r ∧ Le r q ∧ r ≠ q} := fun h => h.2.2 rfl
  have hlt : Lax799700.Common.bitRank Le Posn q < Lax799700.Common.bitRank Le Posn p₀ :=
    Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (Set.toFinite _)
  exact absurd (hmin q hq) (by omega)

/-- A decoded number is smaller than `2` to the number of positions. -/
theorem binNum_lt_two_pow (hlin : Lax904597.Machines.IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b : A → Prop, Lax799700.Common.binNum Le Posn b < 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b
    classical
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext p
        simp
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      have hIH := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b
      rw [binNum_peel_min hlin hp₀ hminp, ← hcard, pow_succ]
      have : (if b p₀ then 1 else 0) ≤ 1 := by
        split <;> omega
      omega
    · have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : Lax799700.Common.binNum Le Posn b = 0 := by
        have hset : {p : A | Posn p ∧ b p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [Lax799700.Common.binNum, hset, finsum_mem_empty]
      rw [hzero]
      exact Nat.two_pow_pos n

open Classical in
/-- **The decoding is injective on the positions**: two sets of bits with the
same value agree wherever it matters. -/
theorem binNum_inj_on (hlin : Lax904597.Machines.IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b b' : A → Prop, Lax799700.Common.binNum Le Posn b = Lax799700.Common.binNum Le Posn b' →
        ∀ p, Posn p → (b p ↔ b' p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b b' heq p hp
    obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin ⟨p, hp⟩
    have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
      ext r
      simp
    have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨p, hp⟩
    have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
      rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
        ← hn]
      omega
    rw [binNum_peel_min hlin hp₀ hminp (b := b),
      binNum_peel_min hlin hp₀ hminp (b := b')] at heq
    -- the lowest bits agree, since they are the parities
    have hbit : (if b p₀ then 1 else 0) = (if b' p₀ then (1 : ℕ) else 0) := by
      by_cases h : b p₀ <;> by_cases h' : b' p₀ <;> simp [h, h'] at heq ⊢ <;> omega
    have hrest : Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b =
        Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b' := by omega
    rcases eq_or_ne p p₀ with hpp₀ | hpne
    · rw [hpp₀]
      by_cases h : b p₀ <;> by_cases h' : b' p₀
      · exact iff_of_true h h'
      · simp [h, h'] at hbit
      · simp [h, h'] at hbit
      · exact iff_of_false h h'
    · exact IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b b' hrest p ⟨hp, hpne⟩

open Classical in
/-- **Comparison by the highest differing position**: one decoded number is
smaller than another exactly when there is a position carrying `0` in the
first and `1` in the second above which the two agree. Unlike the value
itself, this is a *first-order* reading of `<`, which is what a kernel
comparing two guessed numbers writes. -/
theorem binNum_lt_iff (hlin : Lax904597.Machines.IsLinOrd Le) :
    ∀ (n : ℕ) (Posn : A → Prop), ({p : A | Posn p} : Set A).ncard = n →
      ∀ b b' : A → Prop, (Lax799700.Common.binNum Le Posn b < Lax799700.Common.binNum Le Posn b' ↔
        ∃ p, Posn p ∧ ¬b p ∧ b' p ∧ ∀ q, Posn q → Le p q → q ≠ p → (b q ↔ b' q)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Posn hn b b'
    classical
    by_cases hne : ∃ p, Posn p
    · obtain ⟨p₀, hp₀, hminp⟩ := exists_minPos hlin hne
      have hpos : 0 < ({p : A | Posn p} : Set A).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact hne
      have hset' : {p : A | Posn p ∧ p ≠ p₀} = {p : A | Posn p} \ {p₀} := by
        ext r
        simp
      have hcard : ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard + 1 = n := by
        rw [hset', Set.ncard_sdiff_singleton_of_mem (show p₀ ∈ {p : A | Posn p} from hp₀),
          ← hn]
        omega
      have hIH := IH ({p : A | Posn p ∧ p ≠ p₀} : Set A).ncard (by omega)
        (fun q => Posn q ∧ q ≠ p₀) rfl b b'
      -- above the lowest position, equality of the two values is agreement
      have heq : (Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b =
          Lax799700.Common.binNum Le (fun q => Posn q ∧ q ≠ p₀) b') ↔
            ∀ q, Posn q → q ≠ p₀ → (b q ↔ b' q) :=
        ⟨fun h q hq hq₀ => binNum_inj_on hlin _ _ rfl b b' h q ⟨hq, hq₀⟩,
          fun h => binNum_congr_on fun q hq => h q hq.1 hq.2⟩
      -- a witness is either the lowest position or one above it, and nothing
      -- lies above `p₀` that is not a position of its own
      have hsplit : (∃ p, Posn p ∧ ¬b p ∧ b' p ∧
            ∀ q, Posn q → Le p q → q ≠ p → (b q ↔ b' q)) ↔
          (∃ p, (Posn p ∧ p ≠ p₀) ∧ ¬b p ∧ b' p ∧
            ∀ q, (Posn q ∧ q ≠ p₀) → Le p q → q ≠ p → (b q ↔ b' q)) ∨
          ((∀ q, Posn q → q ≠ p₀ → (b q ↔ b' q)) ∧ ¬b p₀ ∧ b' p₀) := by
        constructor
        · rintro ⟨p, hp, hbp, hb'p, habove⟩
          rcases eq_or_ne p p₀ with rfl | hpne
          · exact Or.inr ⟨fun q hq hq₀ => habove q hq (hminp q hq) hq₀, hbp, hb'p⟩
          · exact Or.inl ⟨p, ⟨hp, hpne⟩, hbp, hb'p,
              fun q hq hle hqp => habove q hq.1 hle hqp⟩
        · rintro (⟨p, ⟨hp, hpne⟩, hbp, hb'p, habove⟩ | ⟨hag, hbp, hb'p⟩)
          · refine ⟨p, hp, hbp, hb'p, fun q hq hle hqp => ?_⟩
            rcases eq_or_ne q p₀ with rfl | hq₀
            · exact absurd (hlin.2.2.1 p q hle (hminp p hp)) hpne
            · exact habove q ⟨hq, hq₀⟩ hle hqp
          · exact ⟨p₀, hp₀, hbp, hb'p, fun q hq _ hq₀ => hag q hq hq₀⟩
      rw [binNum_peel_min hlin hp₀ hminp (b := b),
        binNum_peel_min hlin hp₀ hminp (b := b'), hsplit, ← hIH, ← heq]
      by_cases h : b p₀ <;> by_cases h' : b' p₀ <;> simp [h, h'] <;> omega
    · have hempty : ∀ p, ¬Posn p := fun p hp => hne ⟨p, hp⟩
      have hzero : ∀ c : A → Prop, Lax799700.Common.binNum Le Posn c = 0 := by
        intro c
        have hset : {p : A | Posn p ∧ c p} = (∅ : Set A) := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hempty p h.1
        rw [Lax799700.Common.binNum, hset, finsum_mem_empty]
      rw [hzero b, hzero b']
      simp only [lt_self_iff_false, false_iff, not_exists]
      exact fun p hcon => hempty p hcon.1

end Ripple

end Lax794877Proofs.DescriptiveComplexity


