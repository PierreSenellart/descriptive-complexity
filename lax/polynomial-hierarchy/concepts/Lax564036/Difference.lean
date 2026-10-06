import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax904597.SecondOrder
import Lax904597.Classes

/-!
---
title: The class DP
type: definition
---
A decision problem $P$ is DP-definable when there are a
$\Sigma_1$-definable problem $S$ and a $\Pi_1$-definable problem $T$ over
the same vocabulary such that, on nonempty finite structures, $P$ holds
exactly when both $S$ and $T$ hold: the conjunction of an NP condition and a
coNP condition, or equivalently the difference of two NP problems. DP is the
class of the DP-definable problems, the class of Papadimitriou and
Yannakakis, with the cofinal hardness of the NP core.
-/

namespace Lax564036.Difference

open Lax904597.Problems Lax904597.SecondOrder Lax904597.Classes

open FirstOrder

open Language Structure

/-- A decision problem is **DP-definable** if, on nonempty finite structures,
it is the conjunction of a `Σ₁`-definable and a `Π₁`-definable problem: an NP
condition and a coNP one, imposed together. Equivalently, it is the difference
`S \ Tᶜ` of two NP problems. -/
def DPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ S T : DecisionProblem L, SigmaSODefinable 1 S ∧ PiSODefinable 1 T ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ (S A ∧ T A)

/-- **DP**: the class of the DP-definable problems, with cofinal hardness. -/
def DP : ComplexityClass :=
  ComplexityClass.ofMem fun P => DPDefinable P

end Lax564036.Difference
