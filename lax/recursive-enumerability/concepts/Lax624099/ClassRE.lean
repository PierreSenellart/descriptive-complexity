import Lax904597.Problems
import Lax904597.Classes
import Lax624099.ValueInvention

/-!
---
title: The classes RE and co-RE
type: definition
---
RE is the class of decision problems definable in existential second-order
logic with value invention, with the cofinal hardness of the NP core: a
problem is RE-hard when every problem it reduces to, by a relativized ordered
first-order reduction, is reduced to by every problem of RE. The complement
of a decision problem has the no-instances of the problem as yes-instances,
and co-RE is the class of problems whose complement is in RE. RE-completeness
is membership together with RE-hardness.
-/

namespace Lax624099.ClassRE

open Lax904597.Problems Lax904597.Classes Lax624099.ValueInvention

open FirstOrder

open Language

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

/-- **RE**, the recursively enumerable problems: the class of the
`∃SO[new]`-definable problems, with cofinal hardness. -/
noncomputable def RE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSONewDefinable P

/-- **co-RE**: the problems whose complement is recursively enumerable. -/
noncomputable def coRE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSONewDefinable (DecisionProblem.compl P)

end Lax624099.ClassRE
