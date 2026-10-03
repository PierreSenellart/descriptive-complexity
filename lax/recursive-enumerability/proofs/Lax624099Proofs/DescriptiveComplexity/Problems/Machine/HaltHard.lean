/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltHard.Correct
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltMem
import Lax624099Proofs.DescriptiveComplexity.Problems.FinSat
import Lax624099Proofs.DescriptiveComplexity.Computability.Catalog
import Lax624099Proofs.DescriptiveComplexity.Computability.CodeHalt
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax904597.Problems.DecisionProblem
export Lax624099.ConcreteInstances.DecisionProblem (toPred)
end Lax904597.Problems.DecisionProblem

/-!
# The halting problem is RE-complete

**`Lax624099Proofs.DescriptiveComplexity.orderedReduction_halt`**: every decision problem
whose concrete instances form a recursively enumerable set reduces to
`Lax624099Proofs.DescriptiveComplexity.HALT` by an ordered first-order reduction – the
machine bridge for RE, at the machine model. The reduction draws the
fixed simulating machine of `Lax624099Proofs.DescriptiveComplexity.HaltHard.simTM` – whose
states, symbols and transitions are tags, free at every instance size –
together with the instance's own relation tables as the chain of one-bit
`comp` frames on the initial tape
(`Lax624099Proofs.DescriptiveComplexity.HaltHard.inputChain`).

With membership (`Lax624099Proofs.DescriptiveComplexity.halt_mem_RE`), this makes `HALT`
RE-complete (`Lax624099Proofs.DescriptiveComplexity.halt_RE_complete`): the machine model now
states “RE is the class of semi-decidable problems” alongside the code model
(`Lax624099Proofs.DescriptiveComplexity.codehalt_RE_complete`).
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Turing.ToPartrec (Code)

variable {L : Language.{0, 0}} [L.IsRelational] {V : Lax624099.ConcreteInstances.FinVocab L}

/-- **A semi-decidable problem reduces to HALT.** The reduction draws the
fixed simulating machine – `Turing.ToPartrec.Code.exists_code` supplies its
fold and semi-decision codes – and spells the instance's bit table as the
input chain on the initial tape. -/
theorem orderedReduction_halt (P : Lax904597.Problems.DecisionProblem L) (h : REPred (P.toPred V)) :
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

/-- **The halting problem is undecidable**, in the concrete sense: no
numbering of its instances has a computable characteristic function. -/
theorem halt_not_computable (V' : Lax624099.ConcreteInstances.FinVocab Lax904597.Machines.turing) :
    ¬ComputablePred (HALT.toPred V') :=
  not_computablePred_of_RE_hard halt_RE_hard V'

end Lax624099Proofs.DescriptiveComplexity


