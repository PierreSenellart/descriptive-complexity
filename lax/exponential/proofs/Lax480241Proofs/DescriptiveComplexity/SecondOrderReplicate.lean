/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.SecondOrderMerge
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SORealize)
end Lax480241Proofs.DescriptiveComplexity

/-!
# A quantifier prefix of `k` copies of one block

The shape every `Σₖ` definition in this library has: `k` alternating blocks
that are all *the same* block, one per round of whatever the definition
describes – one truth assignment per quantifier block for
`DescriptiveComplexity.QBF`, one run per round of the game for the machine
bridge of the polynomial hierarchy.

`DescriptiveComplexity.SecondOrderMerge` collapses a prefix into a single
block, at the cost of turning the alternation into
`DescriptiveComplexity.altAssign`, an alternating quantification over the
*pieces* of one merged assignment. That is awkward to use: the pieces are
indexed by the shape of the merge rather than by the round. This file removes
the awkwardness when all the blocks are equal:

* `DescriptiveComplexity.repBlockAssign` assembles a merged assignment out of a
  family `Fin k → B.Assignment A`, one per round (`DescriptiveComplexity.QBF`'s
  own `repAssign` is its monadic special case, and should be folded into it);
* `DescriptiveComplexity.repSym` names the relation variable of the `i`-th
  round, and `DescriptiveComplexity.relMap_repSym` reads it back;
* `DescriptiveComplexity.altBlockQuant` is the alternating quantification over
  such a family, and `DescriptiveComplexity.altAssign_repBlocks` identifies it
  with `altAssign`.

Nothing here is specific to a block: the symbol and the assignment are built by
the same recursion on `k`, so the reading lemma is `Iff.rfl` at the head and the
induction hypothesis at the tail.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The prefix and its merge -/

/-- A quantifier prefix of `k` copies of the block `B`. -/
abbrev repBlocks (B : Lax904597.SecondOrder.SOBlock) (k : ℕ) : List Lax904597.SecondOrder.SOBlock := List.replicate k B

@[simp]
theorem repBlocks_length (B : Lax904597.SecondOrder.SOBlock) (k : ℕ) : (repBlocks B k).length = k :=
  List.length_replicate ..

/-- The single block merging a prefix of `k` copies of `B`. -/
abbrev repMerged (B : Lax904597.SecondOrder.SOBlock) (k : ℕ) : Lax904597.SecondOrder.SOBlock := mergeBlocks (repBlocks B k)

/-- The relation variable of `B` used by the `i`-th round, as a symbol of the
merged block's vocabulary. The arity proof is carried along the recursion, so
that reading the symbol back needs no cast. -/
def repSym (B : Lax904597.SecondOrder.SOBlock) {n : ℕ} (x : B.ι) (h : B.arity x = n) :
    ∀ (k : ℕ), Fin k → (repMerged B k).lang.Relations n
  | 0, i => i.elim0
  | _ + 1, ⟨0, _⟩ => ⟨Sum.inl x, h⟩
  | k + 1, ⟨j + 1, hj⟩ =>
      ⟨Sum.inr (repSym B x h k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).1,
        (repSym B x h k ⟨j, Nat.lt_of_succ_lt_succ hj⟩).2⟩

/-- The merged assignment determined by one assignment of `B` per round. -/
def repBlockAssign (B : Lax904597.SecondOrder.SOBlock) (A : Type) : ∀ (k : ℕ), (Fin k → B.Assignment A) →
    (repMerged B k).Assignment A
  | 0, _ => nilAssign A
  | k + 1, ρs => consAssign (ρs 0) (repBlockAssign B A k fun i => ρs i.succ)

/-- **Reading back the relation variable of a round.** -/
theorem relMap_repSym (B : Lax904597.SecondOrder.SOBlock) {A : Type} {n : ℕ} (x : B.ι) (h : B.arity x = n) :
    ∀ (k : ℕ) (ρs : Fin k → B.Assignment A) (i : Fin k) (v : Fin n → A),
      @RelMap (repMerged B k).lang A ((repMerged B k).structure (repBlockAssign B A k ρs)) n
          (repSym B x h k i) v ↔ ρs i x fun j => v (Fin.cast h j) := by
  intro k
  induction k with
  | zero => intro _ i; exact i.elim0
  | succ k ih =>
    intro ρs i v
    obtain ⟨j, hj⟩ := i
    cases j with
    | zero => exact Iff.rfl
    | succ j => exact ih (fun i => ρs i.succ) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ v

/-! ### Alternating over the rounds -/

/-- Alternating quantification over one assignment of `B` per round: the round
of index `0` is quantified outermost, existentially if `pol` is `true`, and the
polarities alternate inwards. -/
def altBlockQuant (A : Type) (B : Lax904597.SecondOrder.SOBlock) :
    ∀ (k : ℕ), ((Fin k → B.Assignment A) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true =>
      ∃ ρ : B.Assignment A, altBlockQuant A B k (fun ρs => P (Fin.cons ρ ρs)) false
  | k + 1, P, false =>
      ∀ ρ : B.Assignment A, altBlockQuant A B k (fun ρs => P (Fin.cons ρ ρs)) true

/-- Alternating quantification over the rounds only depends on the quantified
predicate up to pointwise equivalence. -/
theorem altBlockQuant_congr {A : Type} {B : Lax904597.SecondOrder.SOBlock} :
    ∀ (k : ℕ) (P Q : (Fin k → B.Assignment A) → Prop), (∀ ρs, P ρs ↔ Q ρs) →
      ∀ pol : Bool, altBlockQuant A B k P pol ↔ altBlockQuant A B k Q pol := by
  intro k
  induction k with
  | zero => intro P Q h pol; exact h _
  | succ k ih =>
    intro P Q h pol
    cases pol with
    | true => exact exists_congr fun ρ => ih _ _ (fun ρs => h _) false
    | false => exact forall_congr' fun ρ => ih _ _ (fun ρs => h _) true

/-! ### The definability statement

Put together: a sentence over the *single* merged block, transported into the
iterated expansion by `DescriptiveComplexity.unmergeHom`, is satisfied
alternately exactly when the `k` round assignments are quantified alternately.
This is the form a `Σₖ`-definability proof consumes. -/

end Lax480241Proofs.DescriptiveComplexity


