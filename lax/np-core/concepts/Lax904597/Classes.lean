import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder

/-!
---
title: Complexity classes, cofinal hardness, and NP
type: definition
---
A complexity class is given by a membership predicate and a hardness
predicate on decision problems over arbitrary relational vocabularies. The
classes of this development are built from their membership predicate
alone, with hardness read *cofinally*: a problem $P$ is hard when every
member of the class reduces, by a relativized ordered first-order reduction,
to every problem that $P$ itself reduces to. Over a relational vocabulary
this is the usual “every member reduces to $P$” (stated in *NP is a
complexity class*), and the cofinal form makes hardness travel forward
along reductions through non-relational vocabularies. A problem is
complete for a class when it belongs to it and is hard for it.

NP is the class whose members are the $\Sigma_1$-definable problems, by
Fagin's theorem; more generally the level $\Sigma_{k+1}$ of the polynomial
hierarchy has the $\Sigma_{k+1}$-definable problems as members. The
library this submission comes from makes closure under first-order
reductions part of the definition of a class; that NP is closed is stated
separately, in *NP is a complexity class*.
-/

namespace Lax904597.Classes

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

/-- A complexity class: a membership predicate and a hardness predicate on
decision problems, over arbitrary relational vocabularies. -/
structure ComplexityClass where
  /-- The problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to. -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Cofinal hardness for a collection of problems: every problem of the
collection reduces to every relational problem that `P` reduces to. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (RelOrderedFOReduction P S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (RelOrderedFOReduction Q S)

/-- The class with the given membership and cofinal hardness. -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := CofinalHard Mem P

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def ComplexityClass.Complete (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  C.Mem P ∧ C.Hard P

/-- The level `Σₖ₊₁ᵖ` of the polynomial hierarchy: the problems definable with
`k + 1` alternating blocks of second-order quantifiers, existential first. -/
def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem fun P => SigmaSODefinable (k + 1) P

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
def NP : ComplexityClass := sigmaLevel 0

end Lax904597.Classes
