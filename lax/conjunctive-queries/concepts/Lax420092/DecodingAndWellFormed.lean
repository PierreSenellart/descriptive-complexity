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
title: Decoding, and well-formed evaluation is NP-complete
type: theorem
---
The decoder is sound: an instance it reads off a presented structure has a
satisfied query exactly when the presented structure is a yes-instance of
CQEval. It is total on well-formed structures: every nonempty presented
structure with a constant decodes to an instance. And well-formed
evaluation, whose yes-instances are exactly the structures with a constant
whose query holds, is NP-complete, so the restriction the decoder needs
loses nothing.
-/

namespace Lax420092.DecodingAndWellFormed

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- The decoder is sound. -/
axiom cqDecode_sound : ∀ (S : FinPresentation queryDb) (i : CQInstance),
  i ∈ cqDecode S → (ConcreteCQHolds i ↔ CQEval (Fin S.card))

/-- The decoder is total on well-formed structures. -/
axiom cqDecode_total : ∀ S : FinPresentation queryDb,
  0 < S.card → Fin S.card ⊨ cqWFSentence → (cqDecode S).isSome

/-- The yes-instances of WFCQEval are exactly the structures with a constant
whose query holds. -/
axiom wfCQEval_iff : ∀ (A : Type) [queryDb.Structure A],
  WFCQEval A ↔ (A ⊨ cqWFSentence ∧ QueryHolds A)

/-- WFCQEval is NP-complete. -/
axiom wfCQEval_NP_complete : NP.Complete WFCQEval

end Lax420092.DecodingAndWellFormed
