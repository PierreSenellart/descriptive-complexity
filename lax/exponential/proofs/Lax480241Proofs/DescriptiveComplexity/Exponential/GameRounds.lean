/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameMove
import Lax480241Proofs.DescriptiveComplexity.Exponential.Translate
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

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# Moving whole rounds

The state of the game that carries `DescriptiveComplexity.EXPTIME` to SO-GAME
is a tuple of **rounds**
– `DescriptiveComplexity.repMerged` of the point block – carrying a phase in its
tag bits. Its moves never touch one relation variable at a time: they *keep* a
round, *overwrite* a round, or *shift* a round onto another one (the points of
the node just chosen become the points the next position reads). This file
states those three at the level of rounds, on top of the variable-level gadgets
of `DescriptiveComplexity.Exponential.GameMove`.

* `DescriptiveComplexity.repIx` names round `i`'s copy of a variable inside the
  merged block, and `DescriptiveComplexity.repBlockAssign_repIx` reads it back –
  `DescriptiveComplexity.relMap_repSym` stated about assignments rather than
  about `RelMap`, as `DescriptiveComplexity.ExpExpansion.homAssign_roundOneIx`
  is for a whole round.
* `DescriptiveComplexity.roundsAgreeS` is the move sentence “round `a` of the
  state I leave is round `b` of the state I enter”, one conjunct per listed
  pair; `DescriptiveComplexity.realize_roundsAgreeS` says exactly that. Freezing
  is the diagonal list, shifting is any other.

Nothing here mentions an expansion: a round is any block, replicated.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### One round's copy of a variable -/

/-- Round `i`'s copy of the variable `x`, as a relation variable of the merged
block. -/
def repIx (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (i : Fin n) : B.ι → (repMerged B n).ι :=
  fun x => (repSym B x rfl n i).1

theorem repIx_arity (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (i : Fin n) (x : B.ι) :
    (repMerged B n).arity (repIx B n i x) = B.arity x :=
  (repSym B x rfl n i).2

/-- **Reading back one variable of one round.** -/
theorem repBlockAssign_repIx (B : Lax904597.SecondOrder.SOBlock) (A : Type) (n : ℕ)
    (ρs : Fin n → B.Assignment A) (i : Fin n) (x : B.ι) (v : Fin (B.arity x) → A) :
    (repBlockAssign B A n ρs (repIx B n i x) fun j => v (Fin.cast (repIx_arity B n i x) j)) ↔
      ρs i x v :=
  relMap_repSym B x rfl n ρs i v

/-! ### Whole rounds, moved -/

open Classical in
/-- The variable pairs saying that round `a` of the first copy is round `b` of
the second. -/
noncomputable def repPairIx (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (a b : Fin n) :
    List {p : (repMerged B n).ι × (repMerged B n).ι //
      (repMerged B n).arity p.2 = (repMerged B n).arity p.1} :=
  (finEnum B.ι).map fun x =>
    ⟨(repIx B n a x, repIx B n b x),
      (repIx_arity B n b x).trans (repIx_arity B n a x).symm⟩

open Classical in
/-- The variable pairs of a list of round pairs. -/
noncomputable def roundPairIx (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (ab : List (Fin n × Fin n)) :
    List {p : (repMerged B n).ι × (repMerged B n).ι //
      (repMerged B n).arity p.2 = (repMerged B n).arity p.1} :=
  ab.flatMap fun e => repPairIx B n e.1 e.2

open Classical in
/-- **The move carries round `a` onto round `b`, for each listed pair.** The
diagonal list freezes the rounds it names. -/
noncomputable def roundsAgreeS (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (n : ℕ) (T : Type) [Finite T]
    (ab : List (Fin n × Fin n)) :
    (((L.sum Language.order).sum ((repMerged B n).withTag T).lang).sum
      ((repMerged B n).withTag T).lang).Sentence :=
  varsPairAgreeS L (repMerged B n) T (roundPairIx B n ab)

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {n : ℕ} {T : Type} [Finite T]

variable {A : Type} [instL : L.Structure A] [LinearOrder A]

open Classical in
/-- **What moving rounds says**: the listed rounds of the state the move leaves
are the corresponding rounds of the state it enters. -/
theorem realize_roundsAgreeS (p q : T) (ρs σs : Fin n → B.Assignment A)
    (ab : List (Fin n × Fin n)) :
    (@Sentence.Realize _ A
        (@Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) ((repMerged B n).withTag T) A
          (@Lax904597.Interpretations.sumOrderStructure L A instL _)
          (SOBlock.tagAssign p (repBlockAssign B A n ρs))
          (SOBlock.tagAssign q (repBlockAssign B A n σs)))
        (roundsAgreeS L B n T ab) ↔
      ∀ e ∈ ab, ρs e.1 = σs e.2) := by
  classical
  rw [roundsAgreeS, realize_varsPairAgreeS]
  constructor
  · intro h e he
    funext x v
    have hmem : (⟨(repIx B n e.1 x, repIx B n e.2 x),
        (repIx_arity B n e.2 x).trans (repIx_arity B n e.1 x).symm⟩ :
          {p : (repMerged B n).ι × (repMerged B n).ι //
            (repMerged B n).arity p.2 = (repMerged B n).arity p.1}) ∈
        roundPairIx B n ab :=
      List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨x, mem_finEnum x, rfl⟩⟩
    have hx : (repBlockAssign B A n ρs (repIx B n e.1 x) fun j =>
          v (Fin.cast (repIx_arity B n e.1 x) j)) ↔
        (repBlockAssign B A n σs (repIx B n e.2 x) fun k =>
          v (Fin.cast (repIx_arity B n e.2 x) k)) :=
      h _ hmem fun j => v (Fin.cast (repIx_arity B n e.1 x) j)
    rw [repBlockAssign_repIx, repBlockAssign_repIx] at hx
    exact propext hx
  · rintro h ⟨⟨i, j⟩, hij⟩ hmem y
    obtain ⟨e, he, hin⟩ := List.mem_flatMap.mp hmem
    obtain ⟨x, -, heq⟩ := List.mem_map.mp hin
    have hpair : (repIx B n e.1 x, repIx B n e.2 x) = (i, j) := congrArg Subtype.val heq
    have hi : i = repIx B n e.1 x := (congrArg Prod.fst hpair).symm
    have hj : j = repIx B n e.2 x := (congrArg Prod.snd hpair).symm
    subst hi
    subst hj
    have h1 := repBlockAssign_repIx B A n ρs e.1 x
      fun k' => y (Fin.cast (repIx_arity B n e.1 x).symm k')
    have h2 := repBlockAssign_repIx B A n σs e.2 x
      fun k' => y (Fin.cast (repIx_arity B n e.1 x).symm k')
    exact h1.trans ((iff_of_eq (congrFun (congrFun (h e he) x) _)).trans h2.symm)

end Lax480241Proofs.DescriptiveComplexity


