import Lax904597.Problems
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax535992.ClassPTIME

/-!
---
title: The polynomial hierarchy, coNP and PH
type: definition
---
The levels of the polynomial hierarchy are defined by logics. Level 0 is
polynomial time: $\Sigma_0^p$ is PTIME and $\Pi_0^p$ is coPTIME. For
$k \ge 1$, $\Sigma_k^p$ is the class of decision problems definable by a
second-order sentence with $k$ alternating blocks of second-order
quantifiers, the first existential, over a first-order kernel, and
$\Pi_k^p$ the class of those definable with the first block universal;
these are the levels of the hierarchy by the theorems of Fagin and
Stockmeyer. In particular $\Sigma_1^p$ is NP, and coNP is $\Pi_1^p$, the
problems definable in universal second-order logic. Hardness for each level
is the cofinal hardness of the NP core, under relativized ordered
first-order reductions.

PH is the union of the levels: a problem is in PH when it is in
$\Sigma_k^p$ for some $k$, and PH-hard when it is hard for every level.
-/

namespace Lax564036.Hierarchy

open Lax904597.Problems Lax904597.SecondOrder Lax904597.Classes Lax535992.ClassPTIME

/-- The level `Σₖᵖ` of the polynomial hierarchy: polynomial time at level `0`,
and the problems definable with `k` alternating blocks of second-order
quantifiers, existential first, above. -/
def SigmaP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => sigmaLevel k

/-- The level `Πₖᵖ` of the polynomial hierarchy: the complements of polynomial
time problems at level `0`, and the problems definable with `k` alternating
blocks of second-order quantifiers, universal first, above. -/
def PiP : ℕ → ComplexityClass
  | 0 => coPTIME
  | k + 1 => ComplexityClass.ofMem fun P => PiSODefinable (k + 1) P

/-- **coNP** is `Π₁ᵖ`: the problems definable in universal second-order
logic. -/
def coNP : ComplexityClass := PiP 1

/-- **PH**, the polynomial hierarchy: the union of its levels. A problem is
PH-hard when it is hard for every level. -/
def PH : ComplexityClass where
  Mem P := ∃ k, (SigmaP k).Mem P
  Hard P := ∀ k, (SigmaP k).Hard P

end Lax564036.Hierarchy
