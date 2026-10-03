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
title: Invariance and characterization of containment
type: lemma
---
Containment of the left query in the right one is invariant under isomorphism
of pairs, and a pair is a yes-instance of CQContainment exactly when its left
query is contained in its right query.
-/

namespace Lax420092.ContainmentInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- The property `QueryContained` is isomorphism-invariant. -/
axiom queryContained_iso : ∀ {A B : Type} [queryPair.Structure A] [queryPair.Structure B],
  (A ≃[queryPair] B) → (QueryContained A ↔ QueryContained B)

/-- The yes-instances of CQContainment are exactly the pairs whose left query
is contained in the right one. -/
axiom cqContainment_iff : ∀ (A : Type) [queryPair.Structure A],
  CQContainment A ↔ QueryContained A

end Lax420092.ContainmentInvariance
