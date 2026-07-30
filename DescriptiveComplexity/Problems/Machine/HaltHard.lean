/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Correct
import DescriptiveComplexity.Problems.Machine.HaltMem
import DescriptiveComplexity.Problems.FinSat
import DescriptiveComplexity.Computability.Catalog
import DescriptiveComplexity.Computability.CodeHalt

/-!
# The halting problem is RE-complete

**`DescriptiveComplexity.orderedReduction_halt`**: every decision problem
whose concrete instances form a recursively enumerable set reduces to
`DescriptiveComplexity.HALT` by an ordered first-order reduction – the
machine bridge for RE, at the machine model. The reduction draws the
fixed simulating machine of `DescriptiveComplexity.HaltHard.simTM` – whose
states, symbols and transitions are tags, free at every instance size –
together with the instance's own relation tables as the chain of one-bit
`comp` frames on the initial tape
(`DescriptiveComplexity.HaltHard.inputChain`).

With membership (`DescriptiveComplexity.halt_mem_RE`), this makes `HALT`
RE-complete (`DescriptiveComplexity.halt_RE_complete`): the machine model now
states “RE is the class of semi-decidable problems” alongside the code model
(`DescriptiveComplexity.codehalt_RE_complete`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Turing.ToPartrec (Code)

variable {L : Language.{0, 0}} [L.IsRelational] {V : FinVocab L}

/-- **A semi-decidable problem reduces to HALT.** The reduction draws the
fixed simulating machine – `Turing.ToPartrec.Code.exists_code` supplies its
fold and semi-decision codes – and spells the instance's bit table as the
input chain on the initial tape. -/
theorem orderedReduction_halt (P : DecisionProblem L) (h : REPred (P.toPred V)) :
    Nonempty (P ≤ᶠᵒ[≤] HALT) := by
  classical
  obtain ⟨cF, cP, hF, hP⟩ := HaltHard.exists_chain_codes P h
  refine ⟨{ Tag := HaltHard.HTag V cF cP
            dim := dimOf V
            toInterpretation := HaltHard.haltTuringInterp V cF cP
            correct := fun A _ _ _ _ => ?_ }⟩
  classical
  have hcard : Nat.card A - 1 + 1 = Nat.card A := Nat.succ_pred_eq_of_pos Nat.card_pos
  exact (HaltHard.holds_haltMap_iff V cF cP (Nat.card A - 1)
    ((Fin.castOrderIso hcard).trans (ordEnum A)) hF hP).symm

/-- **HALT is RE-hard.** Finite satisfiability is RE-hard and recursively
enumerable, so it reduces to `HALT`, and hardness travels forward. -/
theorem halt_RE_hard : RE.Hard HALT :=
  (orderedReduction_halt FINSAT finsat_rePred).elim fun f =>
    RE.hard_of_orderedReduction f finsat_RE_hard

/-- **HALT is RE-complete.** -/
theorem halt_RE_complete : RE.Complete HALT :=
  ⟨halt_mem_RE, halt_RE_hard⟩

/-- **The halting problem is undecidable**, in the concrete sense: no
numbering of its instances has a computable characteristic function. -/
theorem halt_not_computable (V' : FinVocab Language.turing) :
    ¬ComputablePred (HALT.toPred V') :=
  not_computablePred_of_RE_hard halt_RE_hard V'

end DescriptiveComplexity
