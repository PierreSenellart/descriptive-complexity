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
title: NP ∪ coNP ⊆ DP ⊆ Σ₂ ∩ Π₂
type: theorem
---
NP and coNP are contained in DP, a condition of one kind being conjoined
with a trivial condition of the other, and DP is contained in both
$\Sigma_2^p$ and $\Pi_2^p$, the two kernels of a DP definition merging
into one alternation in either order of the blocks.
-/

namespace Lax564036.DPInclusions

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- NP is contained in DP. -/
axiom NP_subset_DP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L), NP.Mem P → DP.Mem P

/-- coNP is contained in DP. -/
axiom coNP_subset_DP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L), coNP.Mem P → DP.Mem P

/-- DP is contained in `Σ₂ᵖ`. -/
axiom DP_subset_sigmaP_two : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  DP.Mem P → (SigmaP 2).Mem P

/-- DP is contained in `Π₂ᵖ`. -/
axiom DP_subset_piP_two : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  DP.Mem P → (PiP 2).Mem P

end Lax564036.DPInclusions
