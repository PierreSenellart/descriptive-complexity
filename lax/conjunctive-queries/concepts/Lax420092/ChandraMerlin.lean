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
title: The Chandra–Merlin theorem
type: theorem
---
The left query of a pair is contained in the right one exactly when there is
a homomorphism from the right query to the canonical database of the left
one: a map of the universe to itself, fixing the constants, that sends every
atom of the right query to an atom of the left query. This is the theorem of
Chandra and Merlin (1977), at the schema of graph databases.
-/

namespace Lax420092.ChandraMerlin

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- The Chandra–Merlin theorem. -/
axiom queryContained_iff_hom : ∀ (A : Type) [queryPair.Structure A],
  QueryContained A ↔ CQHom (PairVar (A := A)) (RAtom (A := A)) (LAtom (A := A))

end Lax420092.ChandraMerlin
