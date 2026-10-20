import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Problems
import Lax485149.Complement
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints

/-!
---
title: The exponential classes
type: definition
---
A problem $P$ is definable in a class $C$ one exponential up when an
exponential expansion $X$ and a problem $Q$ of $C$ over its vocabulary are
such that $P(A)$ holds exactly when $Q(X(A))$ does, for every nonempty
finite structure $A$ and every linear order on it; these problems form the
class $C^{\exp}$, with cofinal hardness. EXPTIME and EXPSPACE are the
classes of the problems definable in SO(≤, LFP) and in SO(≤, PFP), NEXPTIME
is NP$^{\exp}$, and coEXPTIME and coEXPSPACE are the classes of the
complements of their problems.
-/

namespace Lax480241.ExponentialClasses

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax485149.Complement
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints

/-- **Definability one exponential up**: some expansion turns the problem into a
problem of the class. -/
def ExpDefinable (C : ComplexityClass) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), C.Mem Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

/-- **The exponential of a class**: the problems definable in it one exponential
up, with cofinal hardness. -/
def expClass (C : ComplexityClass) : ComplexityClass :=
  ComplexityClass.ofMem fun P => ExpDefinable C P

/-- **EXPTIME**: the problems definable in SO(≤, LFP). -/
def EXPTIME : ComplexityClass :=
  ComplexityClass.ofMem fun P => SOLFPDefinable P

/-- **EXPSPACE**: the problems definable in SO(≤, PFP). -/
def EXPSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SOPFPDefinable P

/-- **NEXPTIME**: NP read one exponential up. -/
def NEXPTIME : ComplexityClass :=
  expClass NP

/-- **coEXPTIME**: the complements of the problems of EXPTIME. -/
def coEXPTIME : ComplexityClass :=
  ComplexityClass.ofMem fun P => EXPTIME.Mem (DecisionProblem.compl P)

/-- **coEXPSPACE**: the complements of the problems of EXPSPACE. -/
def coEXPSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => EXPSPACE.Mem (DecisionProblem.compl P)

end Lax480241.ExponentialClasses
