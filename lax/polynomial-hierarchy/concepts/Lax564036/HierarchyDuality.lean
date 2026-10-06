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
title: Π_k is co-Σ_k
type: theorem
---
For every $k$, a decision problem is in $\Pi_k^p$ if and only if its
complement is in $\Sigma_k^p$. At level 0 this is the definition of
coPTIME; above, negating a second-order sentence exchanges the two kinds of
quantifier blocks. In particular the complement of a problem is in coNP
exactly when the problem is in NP.
-/

namespace Lax564036.HierarchyDuality

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- `Πₖᵖ` is the class of complements of `Σₖᵖ` problems. -/
axiom mem_piP_iff : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  (PiP k).Mem P ↔ (SigmaP k).Mem (DecisionProblem.compl P)

/-- The complement of a problem is in coNP exactly when the problem is in NP. -/
axiom compl_mem_coNP_iff : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  coNP.Mem (DecisionProblem.compl P) ↔ NP.Mem P

end Lax564036.HierarchyDuality
