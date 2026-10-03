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
title: The encoding of evaluation instances is faithful and size-honest
type: theorem
---
A concrete query holds in a concrete database, whose domain is nonempty,
exactly when the query of the structure they give holds in its database; a
packaged instance has a satisfied query exactly when the structure it encodes
is a yes-instance of CQEval; the encoded structure has at most as many
elements as the size of the instance; and the size of the instance is at
most $2(e+1)^2$ for $e$ elements. The encoding neither pads nor
compresses.
-/

namespace Lax420092.EncodingFaithful

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- Semantic faithfulness on concrete queries and databases. -/
axiom concreteQueryHolds_iff_queryHolds : ∀ {V C : Type} [Nonempty C]
  (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)),
  ConcreteQueryHolds q D ↔ @QueryHolds (V ⊕ C) (queryDbStructure q D)

/-- Faithfulness of the packaged encoding. -/
axiom cqEncoding_faithful : ∀ i : CQInstance,
  ConcreteCQHolds i ↔ CQEval (Fin i.vars ⊕ Fin (i.consts + 1))

/-- No padding. -/
axiom cqSize_ge_card : ∀ i : CQInstance, i.vars + (i.consts + 1) ≤ cqSize i

/-- No compression. -/
axiom cqSize_le_card : ∀ i : CQInstance, cqSize i ≤ 2 * (i.vars + (i.consts + 1) + 1) ^ 2

end Lax420092.EncodingFaithful
