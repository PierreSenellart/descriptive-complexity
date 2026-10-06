/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltKernel
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

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax564036Proofs.DescriptiveComplexity.ATMData
end Lax564036Proofs.DescriptiveComplexity.ATMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData atmData)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SORealize SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax564036Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax564036.AlternatingMachines (turingAlt)
end FirstOrder.Language

/-!
# Alternating acceptance is `Σₖ`-definable

The membership half of the machine bridge for the polynomial hierarchy:
`ATMAccept (k+1) true` is `Σₖ₊₁`-definable, hence in `Σₖ₊₁ᵖ`, and
`ATMAccept (k+1) false` is `Πₖ₊₁`-definable, hence in `Πₖ₊₁ᵖ`. The two are the
same sentence at the two starting polarities.

The proof is the assembly of the four layers below it:

* alternating acceptance is the `k`-round game
  (`DescriptiveComplexity.ATMData.altAccepts_iff_altGame`), and the game is an
  implication ladder (`DescriptiveComplexity.ATMData.altGame_iff_altLadder`),
  provided a start state exists – which is what
  `DescriptiveComplexity.akStartExClause` contributes to the kernel;
* the ladder over walks is the ladder over the relations a block guesses
  (`DescriptiveComplexity.ATMData.altLadder_iff_runAltLadder`);
* the ladder's own quantifiers are the alternating prefix over one guess per
  round (`DescriptiveComplexity.ATMData.altBlockQuant_runMatrix`), leaving the
  quantifier-free matrix behind;
* the matrix is the kernel (`DescriptiveComplexity.realize_akKernel`), and the
  prefix is `k+1` copies of one block
  (`DescriptiveComplexity.sorealize_repBlocks`).
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

/-- **Acceptance is the ladder, together with the existence of a start
state.** The second conjunct is the one existence clause the ladder cannot
carry itself (see `DescriptiveComplexity.Problems.Machine.AltLadder`); it is
first-order, so the kernel states it outright. -/
theorem altAccepts_iff_start_and_altLadder (hwf : M.toTMData.WellFormed)
    (hbwf : M.BlocksWellFormed k) (hk : 0 < k) (start : Bool) :
    M.AltAccepts start ↔ (∃ q, M.Start q) ∧ M.AltLadder start k := by
  have hlin : Lax904597.Machines.IsLinOrd M.Le := hwf.1
  obtain ⟨p₀, hmin⟩ := exists_minPos hlin hwf.2.1
  obtain ⟨p₁, hmax⟩ := exists_maxPos hlin hwf.2.1
  constructor
  · intro h
    have hinit : ∃ c₀, M.IsInit c₀ := by
      cases start with
      | true => exact ⟨h.choose, h.choose_spec.1⟩
      | false => exact h.1
    exact ⟨⟨hinit.choose.state, hinit.choose_spec.1⟩,
      (altAccepts_iff_altLadder hbwf hlin hmin hmax hk hinit start).mp h⟩
  · rintro ⟨⟨q, hq⟩, hlad⟩
    exact (altAccepts_iff_altLadder hbwf hlin hmin hmax hk
      ((TMData.exists_isInit hwf hq).imp fun _ h => h.1) start).mpr hlad

end ATMData

end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax564036Proofs.DescriptiveComplexity.ATMData (altAccepts_iff_start_and_altLadder)

end Lax564036.AlternatingMachines.ATMData

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ATMData

variable {A : Type} [Finite A] {M : Lax564036.AlternatingMachines.ATMData A} {k : ℕ}

end ATMData

/-! ### Definability -/

section Definability

variable (k : ℕ)

private theorem atm_definable_aux (pol : Bool) (A : Type)
    (instA : (Lax564036.AlternatingMachines.turingAlt (k + 1)).Structure A) [Finite A] [Nonempty A] :
    @Lax904597.Problems.DecisionProblem.Holds _ _ (ATMAccept (k + 1) pol) A instA ↔
      @Lax904597.SecondOrder.SORealize (Lax564036.AlternatingMachines.turingAlt (k + 1)) A instA (repBlocks tmGuessBlock (k + 1))
        ((unmergeHom (repBlocks tmGuessBlock (k + 1)) (Lax564036.AlternatingMachines.turingAlt (k + 1))).onSentence
          (akKernel pol (k + 1))) pol := by
  have hchain : (@Lax904597.SecondOrder.SORealize (Lax564036.AlternatingMachines.turingAlt (k + 1)) A instA (repBlocks tmGuessBlock (k + 1))
        ((unmergeHom (repBlocks tmGuessBlock (k + 1)) (Lax564036.AlternatingMachines.turingAlt (k + 1))).onSentence
          (akKernel pol (k + 1))) pol) ↔
      (@Lax564036.AlternatingMachines.ATMData.toTMData A (Lax564036.AlternatingMachines.atmData (k + 1) A)).WellFormed ∧
        ((Lax564036.AlternatingMachines.atmData (k + 1) A).BlocksWellFormed (k + 1) ∧
          ((∃ q, (Lax564036.AlternatingMachines.atmData (k + 1) A).Start q) ∧
            (Lax564036.AlternatingMachines.atmData (k + 1) A).AltLadder pol (k + 1))) := by
    refine (sorealize_repBlocks tmGuessBlock (Lax564036.AlternatingMachines.turingAlt (k + 1)) A instA (k + 1)
      (akKernel pol (k + 1)) pol).trans ?_
    refine (altBlockQuant_congr (k + 1) _ _ (fun ρs => realize_akKernel ρs pol) pol).trans ?_
    refine (altBlockQuant_and_left (fun _ _ => True) _ _ _ pol).trans (and_congr Iff.rfl ?_)
    refine (altBlockQuant_and_left (fun _ _ => True) _ _ _ pol).trans (and_congr Iff.rfl ?_)
    refine (altBlockQuant_and_left (fun _ _ => True) _ _ _ pol).trans (and_congr Iff.rfl ?_)
    exact (ATMData.altBlockQuant_runMatrix (k + 1)).trans
      (ATMData.altLadder_iff_runAltLadder (Lax564036.AlternatingMachines.atmData (k + 1) A) pol (k + 1)).symm
  constructor
  · rintro ⟨hwf, hbwf, hacc⟩
    exact hchain.mpr ⟨hwf, hbwf,
      (ATMData.altAccepts_iff_start_and_altLadder hwf hbwf (Nat.succ_pos k) pol).mp hacc⟩
  · intro h
    obtain ⟨hwf, hbwf, hrest⟩ := hchain.mp h
    exact ⟨hwf, hbwf,
      (ATMData.altAccepts_iff_start_and_altLadder hwf hbwf (Nat.succ_pos k) pol).mpr hrest⟩

/-- **Alternating acceptance with an existential first block is
`Σₖ₊₁`-definable**: one block guesses the run of each round, and the
first-order kernel checks the ladder. -/
theorem atmAccept_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable (k + 1) (ATMAccept (k + 1) true) :=
  ⟨repBlocks tmGuessBlock (k + 1), repBlocks_length tmGuessBlock (k + 1),
    (unmergeHom (repBlocks tmGuessBlock (k + 1)) (Lax564036.AlternatingMachines.turingAlt (k + 1))).onSentence
      (akKernel true (k + 1)),
    fun A instA _ _ => atm_definable_aux k true A instA⟩

/-- **Alternating acceptance with a universal first block is
`Πₖ₊₁`-definable**, by the same sentence at the other starting polarity. -/
theorem atmAccept_piSODefinable : Lax904597.SecondOrder.PiSODefinable (k + 1) (ATMAccept (k + 1) false) :=
  ⟨repBlocks tmGuessBlock (k + 1), repBlocks_length tmGuessBlock (k + 1),
    (unmergeHom (repBlocks tmGuessBlock (k + 1)) (Lax564036.AlternatingMachines.turingAlt (k + 1))).onSentence
      (akKernel false (k + 1)),
    fun A instA _ _ => atm_definable_aux k false A instA⟩

/-- **Alternating acceptance is in `Σₖ₊₁ᵖ`.** -/
theorem atmAccept_mem_sigmaP : ATMAccept (k + 1) true ∈ SigmaP (k + 1) :=
  atmAccept_sigmaSODefinable k

/-- **Alternating acceptance at the other polarity is in `Πₖ₊₁ᵖ`.** -/
theorem atmAccept_mem_piP : ATMAccept (k + 1) false ∈ PiP (k + 1) :=
  atmAccept_piSODefinable k

end Definability

end Lax564036Proofs.DescriptiveComplexity


