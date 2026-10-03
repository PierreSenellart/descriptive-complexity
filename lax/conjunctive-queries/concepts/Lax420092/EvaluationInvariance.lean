import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Classes
import Lax799700.Problems
import Lax420092.QueryDatabases
import Lax420092.Evaluation
import Lax420092.QueryPairs
import Lax420092.PackagedInstances

/-!
---
title: Invariance and characterization of evaluation
type: lemma
---
Whether the query of an instance holds in its database is invariant under
isomorphism of instances, and an instance is a yes-instance of CQEval exactly
when its query holds in its database.
-/

namespace Lax420092.EvaluationInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- The property `QueryHolds` is isomorphism-invariant. -/
axiom queryHolds_iso : ∀ {A B : Type} [queryDb.Structure A] [queryDb.Structure B],
  (A ≃[queryDb] B) → (QueryHolds A ↔ QueryHolds B)

/-- The yes-instances of CQEval are exactly the instances whose query holds. -/
axiom cqEval_iff : ∀ (A : Type) [queryDb.Structure A], CQEval A ↔ QueryHolds A

end Lax420092.EvaluationInvariance
