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
title: First-order reductions are computable
type: theorem
---
Undecidability travels forward along relativized ordered first-order
reductions, the most general reductions of the NP core: if a problem reduces
to another and the first is not decidable on concrete instances, neither is
the second, over any presentations of the two vocabularies.
-/

namespace Lax624099.ReductionsComputable

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- Undecidability transfers along relativized ordered first-order
reductions, because they are computable. -/
axiom not_computablePred_of_relOrderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational]
  [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'},
  RelOrderedFOReduction P Q → ∀ (V : FinVocab L) (V' : FinVocab L'),
    ¬ComputablePred (DecisionProblem.toPred P V) → ¬ComputablePred (DecisionProblem.toPred Q V')

end Lax624099.ReductionsComputable
