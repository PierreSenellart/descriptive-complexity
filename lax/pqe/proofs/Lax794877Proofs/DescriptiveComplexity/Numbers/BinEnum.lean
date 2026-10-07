/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Numbers.Binary
import Lax794877Proofs.DescriptiveComplexity.Numbers.BinRel
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum bitRank)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Binary numbers on enumerated positions

What an *encoder* of binary numbers needs, once and for all. An encoded
universe lays its bit positions out as the image of an enumeration
`e : Fin N → A` that is injective, hits exactly the positions, and reflects
the order (`DescriptiveComplexity.BinEnum`). Then

* the rank of a position is its index (`DescriptiveComplexity.BinEnum.bitRank_eq`);
* the decoded number is the plain sum of place values
  (`DescriptiveComplexity.BinEnum.binNum_eq_sum`);
* a set of positions carrying the `Nat.testBit` digits of a number that fits
  decodes to that number (`DescriptiveComplexity.BinEnum.binNum_eq_of_testBit`).

The last statement is the one an encoding's faithfulness proof uses: the
encoder writes `w.testBit p` at the position of index `p`, and the abstract
semantics reads `w` back. Whatever else the universe holds – items, vertices,
facts – plays no part.
-/

namespace Lax794877Proofs.DescriptiveComplexity

variable {A : Type} {N : ℕ}

/-- The positions of a universe, enumerated in increasing order: the
enumeration is injective, its range is the set of positions, and it reflects
the order. -/
structure BinEnum (Le : A → A → Prop) (Posn : A → Prop) (e : Fin N → A) : Prop where
  /-- Distinct indices are distinct positions. -/
  injective : Function.Injective e
  /-- The positions are exactly the enumerated elements. -/
  posn_iff : ∀ q, Posn q ↔ ∃ p, q = e p
  /-- The order of the positions is the order of their indices. -/
  le_iff : ∀ p p', Le (e p) (e p') ↔ p ≤ p'

namespace BinEnum

variable {Le : A → A → Prop} {Posn : A → Prop} {e : Fin N → A}

/-- The rank of a position is its index. -/
theorem bitRank_eq (h : BinEnum Le Posn e) (p : Fin N) : Lax799700.Common.bitRank Le Posn (e p) = (p : ℕ) := by
  classical
  have hset : {q : A | Posn q ∧ Le q (e p) ∧ q ≠ e p} = e '' ↑(Finset.Iio p) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_Iio, Set.mem_Iio]
    constructor
    · rintro ⟨hq, hle, hne⟩
      obtain ⟨p', rfl⟩ := (h.posn_iff q).mp hq
      exact ⟨p', lt_of_le_of_ne ((h.le_iff _ _).mp hle) fun hp => hne (hp ▸ rfl), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(h.posn_iff _).mpr ⟨x, rfl⟩, (h.le_iff _ _).mpr (le_of_lt hx),
        fun hp => ne_of_lt hx (h.injective hp)⟩
  unfold Lax799700.Common.bitRank
  rw [hset, Set.ncard_image_of_injective _ h.injective, Set.ncard_coe_finset, Fin.card_Iio]

open Classical in
/-- The decoded number is the sum of the place values of its bits. -/
theorem binNum_eq_sum (h : BinEnum Le Posn e) (b : A → Prop) :
    Lax799700.Common.binNum Le Posn b = ∑ p : Fin N, if b (e p) then 2 ^ (p : ℕ) else 0 := by
  have hset : {q : A | Posn q ∧ b q} = e '' ↑(Finset.univ.filter fun p : Fin N => b (e p)) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hq, hb⟩
      obtain ⟨p, rfl⟩ := (h.posn_iff q).mp hq
      exact ⟨p, hb, rfl⟩
    · rintro ⟨p, hb, rfl⟩
      exact ⟨(h.posn_iff _).mpr ⟨p, rfl⟩, hb⟩
  unfold Lax799700.Common.binNum
  rw [hset, finsum_mem_image h.injective.injOn,
    finsum_mem_congr rfl fun p _ => by rw [h.bitRank_eq p], finsum_mem_coe_finset,
    Finset.sum_filter]

/-- **The decoding.** A set of positions carrying the binary digits of a number
that fits in `N` positions decodes to that number. -/
theorem binNum_eq_of_testBit (h : BinEnum Le Posn e) (w : ℕ) (hw : w < 2 ^ N) (b : A → Prop)
    (hb : ∀ p : Fin N, b (e p) ↔ w.testBit (p : ℕ)) : Lax799700.Common.binNum Le Posn b = w := by
  classical
  have hval : binValue (Fin N) (binEncode (Fin N) w) = w :=
    binValue_binEncode (by simpa using hw)
  rw [h.binNum_eq_sum, ← hval, binValue]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : w.testBit (p : ℕ) <;> simp [binEncode, hb p, hp]

/-- The universe `Fin N`, every element a position, in its own order. -/
theorem fin {Le : Fin N → Fin N → Prop} (hle : ∀ a b, Le a b ↔ a ≤ b) :
    BinEnum Le (fun _ => True) (id : Fin N → Fin N) where
  injective := Function.injective_id
  posn_iff q := ⟨fun _ => ⟨q, rfl⟩, fun _ => trivial⟩
  le_iff := hle

end BinEnum

/-- On the universe `Fin N`, ordered as usual and with every element a
position, the `Nat.testBit` digits of a number below `2 ^ N` decode to it. -/
theorem binNum_fin_of_testBit {N : ℕ} {Le : Fin N → Fin N → Prop}
    (hle : ∀ a b, Le a b ↔ a ≤ b) (w : ℕ) (hw : w < 2 ^ N) (b : Fin N → Prop)
    (hb : ∀ p : Fin N, b p ↔ w.testBit (p : ℕ)) : Lax799700.Common.binNum Le (fun _ => True) b = w :=
  (BinEnum.fin hle).binNum_eq_of_testBit w hw b hb

end Lax794877Proofs.DescriptiveComplexity


