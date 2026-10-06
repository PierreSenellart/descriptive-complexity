import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: The polynomial hierarchy by alternating Turing machines
type: theorem
---
For every $k \ge 1$, alternating machine acceptance with $k$ blocks is
$\Sigma_k^p$-complete when the first block is existential and
$\Pi_k^p$-complete when it is universal, under first-order reductions; and
a decision problem is in $\Sigma_k^p$, respectively $\Pi_k^p$, if and only
if it reduces to the corresponding acceptance problem by an ordered
first-order reduction. Each level of the logically defined hierarchy is thus
the corresponding level of the alternating-machine hierarchy of Chandra,
Kozen and Stockmeyer; at one block these are the nondeterministic machine
and its dual, the machine model of coNP. Membership reads a run as a game
of $k$ rounds, each guessing one walk; hardness builds, inside the instance,
the machine of a quantified Boolean formula, which sweeps the tape once per
quantifier block.
-/

namespace Lax564036.AlternatingMachineComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Alternating acceptance with `k + 1` blocks, existential first, is
`Σₖ₊₁ᵖ`-complete. -/
axiom atmAccept_sigmaP_complete : ∀ (k : ℕ),
  (SigmaP (k + 1)).Complete (ATMAccept (k + 1) true)

/-- Alternating acceptance with `k + 1` blocks, universal first, is
`Πₖ₊₁ᵖ`-complete. -/
axiom atmAccept_piP_complete : ∀ (k : ℕ),
  (PiP (k + 1)).Complete (ATMAccept (k + 1) false)

/-- `Σₖ₊₁ᵖ` is reducibility to alternating acceptance, existential first. -/
axiom mem_sigmaP_iff_le_atmAccept :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (k : ℕ) (P : DecisionProblem L),
  (SigmaP (k + 1)).Mem P ↔ Nonempty (OrderedFOReduction P (ATMAccept (k + 1) true))

/-- `Πₖ₊₁ᵖ` is reducibility to alternating acceptance, universal first. -/
axiom mem_piP_iff_le_atmAccept :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (k : ℕ) (P : DecisionProblem L),
  (PiP (k + 1)).Mem P ↔ Nonempty (OrderedFOReduction P (ATMAccept (k + 1) false))

/-- Acceptance with one existential block is NP-complete. -/
axiom atmAccept_one_NP_complete : NP.Complete (ATMAccept 1 true)

/-- Acceptance with one universal block is coNP-complete. -/
axiom atmAccept_one_coNP_complete : coNP.Complete (ATMAccept 1 false)

end Lax564036.AlternatingMachineComplete
