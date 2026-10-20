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
title: The levels of the polynomial hierarchy are nested
type: theorem
---
The levels of the polynomial hierarchy increase:
$\Sigma_j^p \subseteq \Sigma_k^p$ and $\Pi_j^p \subseteq \Pi_k^p$ for
$j \le k$, and each of $\Sigma_k^p$ and $\Pi_k^p$ is contained in both
$\Sigma_{k+1}^p$ and $\Pi_{k+1}^p$, for $k \ge 1$. Every level is
contained in PH. From level 1 up, a definition is padded with a vacuous
quantifier block; the step from level 0 goes through the complete problem
HORN-SAT.
-/

namespace Lax564036.HierarchyInclusions

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- `Σₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`. -/
axiom sigmaP_subset_sigmaP_succ : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (SigmaP (k + 1)).Mem P → (SigmaP (k + 2)).Mem P

/-- `Σₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
axiom sigmaP_subset_piP_succ : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (SigmaP (k + 1)).Mem P → (PiP (k + 2)).Mem P

/-- `Πₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`. -/
axiom piP_subset_sigmaP_succ : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (PiP (k + 1)).Mem P → (SigmaP (k + 2)).Mem P

/-- `Πₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
axiom piP_subset_piP_succ : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (PiP (k + 1)).Mem P → (PiP (k + 2)).Mem P

/-- The `Σ` levels increase. -/
axiom sigmaP_mono :
  ∀ {j k : ℕ}, j ≤ k → ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  (SigmaP j).Mem P → (SigmaP k).Mem P

/-- The `Π` levels increase. -/
axiom piP_mono :
  ∀ {j k : ℕ}, j ≤ k → ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  (PiP j).Mem P → (PiP k).Mem P

/-- Every `Σ` level is contained in PH. -/
axiom sigmaP_subset_PH : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (SigmaP k).Mem P → PH.Mem P

/-- Every `Π` level is contained in PH. -/
axiom piP_subset_PH : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
  (P : DecisionProblem L), (PiP k).Mem P → PH.Mem P

end Lax564036.HierarchyInclusions
