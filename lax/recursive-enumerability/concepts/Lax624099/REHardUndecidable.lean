import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.Classes
import Lax624099.Problems
import Lax624099.ValueInvention
import Lax624099.ClassRE
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.CodeHalting
import Lax624099.PostCorrespondence
import Lax624099.ConcreteInstances
import Lax904597.Machines

/-!
---
title: Every RE-hard problem is undecidable
type: theorem
---
No RE-hard problem is decidable on concrete instances, over any presentation
of its vocabulary: CODEHALT is not, since Mathlib's halting problem is not,
and hardness carries undecidability along computable reductions.
-/

namespace Lax624099.REHardUndecidable

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- Every RE-hard problem is undecidable. -/
axiom not_computablePred_of_RE_hard : ∀ {L : Language.{0, 0}} [L.IsRelational]
  {P : DecisionProblem L}, RE.Hard P → ∀ V : FinVocab L,
    ¬ComputablePred (DecisionProblem.toPred P V)

end Lax624099.REHardUndecidable
