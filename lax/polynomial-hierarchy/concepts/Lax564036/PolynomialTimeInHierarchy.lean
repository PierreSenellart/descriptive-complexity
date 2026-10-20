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
title: PTIME at the bottom of the polynomial hierarchy
type: theorem
---
Polynomial time is the bottom of the hierarchy: PTIME is contained in coNP,
and in $\Sigma_k^p$ for every $k$; with PTIME $\subseteq$ NP this places
it in NP $\cap$ coNP. The inclusion in coNP is the dual of the inclusion
in NP, PTIME being closed under complement.
-/

namespace Lax564036.PolynomialTimeInHierarchy

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- PTIME is contained in coNP. -/
axiom PTIME_subset_coNP : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PTIME.Mem P → coNP.Mem P

/-- PTIME is contained in every `Σ` level. -/
axiom PTIME_subset_sigmaP : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), PTIME.Mem P → (SigmaP k).Mem P

/-- The two classes of level `0` coincide. -/
axiom piP_zero_eq : PiP 0 = SigmaP 0

end Lax564036.PolynomialTimeInHierarchy
