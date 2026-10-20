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
title: QBF with k alternations is complete for the k-th level
type: theorem
---
For every $k \ge 1$, QBF$_k$ is $\Sigma_k^p$-complete and
QBF$^\forall_k$ is $\Pi_k^p$-complete under first-order reductions,
theorems of Stockmeyer and Wrathall. Every problem of the level reduces to
the corresponding QBF problem by the reduction of the Cook–Levin theorem
carrying the block marks: the second-order quantifier blocks of a definition
become the quantifier blocks of the formula. At $k = 1$ these are an
NP-complete and a coNP-complete problem.
-/

namespace Lax564036.QbfComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- QBF with `k + 1` blocks, existential first, is `Σₖ₊₁ᵖ`-complete. -/
axiom qbf_complete : ∀ (k : ℕ), (SigmaP (k + 1)).Complete (QBF (k + 1))

/-- QBF with `k + 1` blocks, universal first, is `Πₖ₊₁ᵖ`-complete. -/
axiom qbfPi_complete : ∀ (k : ℕ), (PiP (k + 1)).Complete (QBFPi (k + 1))

/-- QBF with one existential block is NP-complete. -/
axiom qbf_one_NP_complete : NP.Complete (QBF 1)

/-- QBF with one universal block is coNP-complete. -/
axiom qbfPi_one_coNP_complete : coNP.Complete (QBFPi 1)

end Lax564036.QbfComplete
