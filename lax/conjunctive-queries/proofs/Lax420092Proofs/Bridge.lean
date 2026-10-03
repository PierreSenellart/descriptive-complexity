import Lax904597.NPClass
import Lax799700.ThreeColorability
import Lax420092.QueryDatabases
import Lax420092.Evaluation
import Lax420092.QueryPairs
import Lax420092.PackagedInstances
import Lax420092.EvaluationInvariance
import Lax420092.ContainmentInvariance
import Lax420092.ChandraMerlin
import Lax420092.EvaluationNPComplete
import Lax420092.ContainmentNPComplete
import Lax420092.EvaluationContainmentReductions
import Lax420092.EncodingFaithful
import Lax420092.DecodingAndWellFormed
import Lax420092Proofs.DescriptiveComplexity.Examples.ConjunctiveQueries

/-!
# The conjunctive-query statements, from the library's theorems

Each claim is proved from the library's theorem of the same name, transported
along the agreement between the library's bundled problem and the concept's,
which the invariance of the property gives. Hardness of evaluation assumes the
catalog's statement for 3-colorability; containment's membership and hardness
assume this submission's statement for evaluation, so the archive's proof
network shows the two reductions.
-/

namespace Lax420092Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- For an invariant property, the problem it gives holds exactly where the
property does. -/
theorem ofPred_iff {L : Language.{0, 0}} [L.IsRelational] {P : ∀ (A : Type) [L.Structure A], Prop}
    (hP : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → (P A ↔ P B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred P V ↔ P V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hP f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

/-- A first-order reduction transported along agreements of its two ends. -/
def FOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q Q' : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : FOReduction P Q) : FOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }

/-! ### Invariance, characterization, agreement -/

/--
---
conclusion: Lax420092.EvaluationInvariance.queryHolds_iso
---
The library's invariance theorem for evaluation.
-/
theorem queryHolds_iso {A B : Type} [queryDb.Structure A] [queryDb.Structure B]
    (e : A ≃[queryDb] B) : QueryHolds A ↔ QueryHolds B :=
  DescriptiveComplexity.queryHolds_iso e

/--
---
conclusion: Lax420092.EvaluationInvariance.cqEval_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem cqEval_iff (A : Type) [queryDb.Structure A] : CQEval A ↔ QueryHolds A :=
  ofPred_iff @DescriptiveComplexity.queryHolds_iso A

/-- The library's bundled CQEval and the concept's agree on every instance. -/
theorem cqEval_agree (A : Type) [queryDb.Structure A] :
    DescriptiveComplexity.CQEval A ↔ CQEval A :=
  (cqEval_iff A).symm

/--
---
conclusion: Lax420092.ContainmentInvariance.queryContained_iso
---
The library's invariance theorem for containment, through the Chandra–Merlin
theorem.
-/
theorem queryContained_iso {A B : Type} [queryPair.Structure A] [queryPair.Structure B]
    (e : A ≃[queryPair] B) : QueryContained A ↔ QueryContained B :=
  DescriptiveComplexity.queryContained_iso e

/--
---
conclusion: Lax420092.ContainmentInvariance.cqContainment_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem cqContainment_iff (A : Type) [queryPair.Structure A] :
    CQContainment A ↔ QueryContained A :=
  ofPred_iff @DescriptiveComplexity.queryContained_iso A

/-- The library's bundled CQContainment and the concept's agree on every
pair. -/
theorem cqContainment_agree (A : Type) [queryPair.Structure A] :
    DescriptiveComplexity.CQContainment A ↔ CQContainment A :=
  (cqContainment_iff A).symm

/-- The library's bundled 3-colorability and the catalog's agree on every
graph, by the catalog's characterization of its problem. -/
theorem threeCol_agree (A : Type) [FirstOrder.Language.graph.Structure A] :
    DescriptiveComplexity.ThreeCol A ↔ Lax799700.ThreeColorability.ThreeCol A :=
  (Lax799700.ThreeColorability.threeCol_iff A).symm

/-! ### The theorems -/

/--
---
conclusion: Lax420092.ChandraMerlin.queryContained_iff_hom
---
The library's Chandra–Merlin theorem.
-/
theorem queryContained_iff_hom (A : Type) [queryPair.Structure A] :
    QueryContained A ↔ CQHom (PairVar (A := A)) (RAtom (A := A)) (LAtom (A := A)) :=
  DescriptiveComplexity.queryContained_iff_hom A

/--
---
conclusion: Lax420092.EvaluationNPComplete.cqEval_NP_complete
---
Membership from the library's existential second-order definition of
evaluation; hardness from the library's first-order reduction of
3-colorability to evaluation, 3-colorability being NP-hard by the catalog's
statement for it. Both are transported along the agreements.
-/
theorem cqEval_NP_complete : NP.Complete CQEval :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => cqEval_agree A).mp
      DescriptiveComplexity.cqEval_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (FOReduction.congr threeCol_agree cqEval_agree
        DescriptiveComplexity.threeCol_fo_reduction_cqEval)
      Lax799700.ThreeColorability.threeCol_NP_complete.2⟩

/--
---
conclusion: Lax420092.EvaluationContainmentReductions.cqContainment_reduces_to_cqEval
---
The library's reduction, the Chandra–Merlin theorem in reduction form,
transported along the agreements.
-/
theorem cqContainment_reduces_to_cqEval : Nonempty (FOReduction CQContainment CQEval) :=
  ⟨FOReduction.congr cqContainment_agree cqEval_agree
    DescriptiveComplexity.cqContainment_fo_reduction_cqEval⟩

/--
---
conclusion: Lax420092.EvaluationContainmentReductions.cqEval_reduces_to_cqContainment
---
The library's reduction, a database read as a variable-free query,
transported along the agreements.
-/
theorem cqEval_reduces_to_cqContainment : Nonempty (FOReduction CQEval CQContainment) :=
  ⟨FOReduction.congr cqEval_agree cqContainment_agree
    DescriptiveComplexity.cqEval_fo_reduction_cqContainment⟩

/--
---
conclusion: Lax420092.ContainmentNPComplete.cqContainment_NP_complete
---
Membership along the reduction to evaluation and hardness along the reduction
from evaluation, both of this submission, evaluation being NP-complete by this
submission's statement.
-/
theorem cqContainment_NP_complete : NP.Complete CQContainment :=
  Lax420092.EvaluationContainmentReductions.cqContainment_reduces_to_cqEval.elim fun f =>
    Lax420092.EvaluationContainmentReductions.cqEval_reduces_to_cqContainment.elim fun g =>
      ⟨Lax904597.NPClass.NP_mem_of_foReduction f
          Lax420092.EvaluationNPComplete.cqEval_NP_complete.1,
        Lax904597.NPClass.cofinalHard_of_foReduction g
          Lax420092.EvaluationNPComplete.cqEval_NP_complete.2⟩

/-! ### Encoding -/

/--
---
conclusion: Lax420092.EncodingFaithful.concreteQueryHolds_iff_queryHolds
---
The library's semantic faithfulness theorem on concrete queries and
databases.
-/
theorem concreteQueryHolds_iff_queryHolds {V C : Type} [Nonempty C]
    (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) :
    ConcreteQueryHolds q D ↔ @QueryHolds (V ⊕ C) (queryDbStructure q D) :=
  DescriptiveComplexity.concreteQueryHolds_iff_queryHolds q D

/--
---
conclusion: Lax420092.EncodingFaithful.cqEncoding_faithful
---
The library's faithfulness theorem for its bundled encoding, whose structure
on the elements of an instance is the concept's.
-/
theorem cqEncoding_faithful (i : CQInstance) :
    ConcreteCQHolds i ↔ CQEval (Fin i.vars ⊕ Fin (i.consts + 1)) :=
  (DescriptiveComplexity.cqEncoding_faithful i).trans (cqEval_agree _)

/--
---
conclusion: Lax420092.EncodingFaithful.cqSize_ge_card
---
The elements are summands of the textbook size.
-/
theorem cqSize_ge_card (i : CQInstance) : i.vars + (i.consts + 1) ≤ cqSize i := by
  obtain ⟨n, m, q, D⟩ := i
  simp only [cqSize]
  omega

/--
---
conclusion: Lax420092.EncodingFaithful.cqSize_le_card
---
The bound the library discharges when it bundles the encoding: atoms are at
most quadratic in the elements, facts at most quadratic in the constants.
-/
theorem cqSize_le_card (i : CQInstance) : cqSize i ≤ 2 * (i.vars + (i.consts + 1) + 1) ^ 2 := by
  obtain ⟨n, m, q, D⟩ := i
  have hq : q.card ≤ (n + (m + 1)) * (n + (m + 1)) := by
    simpa [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin] using q.card_le_univ
  have hD : D.card ≤ (m + 1) * (m + 1) := by
    simpa [Fintype.card_prod, Fintype.card_fin] using D.card_le_univ
  simp only [cqSize]
  nlinarith

/-! ### Decoding -/

/-- The concept's decoder is the library's. -/
theorem cqDecode_eq (S : FinPresentation queryDb) :
    cqDecode S = DescriptiveComplexity.cqDecode S :=
  rfl

/--
---
conclusion: Lax420092.DecodingAndWellFormed.cqDecode_sound
---
The library's soundness theorem for its decoder, the structure a presentation
presents being the concept's.
-/
theorem cqDecode_sound (S : FinPresentation queryDb) (i : CQInstance) (hi : i ∈ cqDecode S) :
    ConcreteCQHolds i ↔ CQEval (Fin S.card) :=
  (DescriptiveComplexity.cqDecode_sound S i (cqDecode_eq S ▸ hi)).trans (cqEval_agree _)

/--
---
conclusion: Lax420092.DecodingAndWellFormed.cqDecode_total
---
The library's totality theorem for its decoder.
-/
theorem cqDecode_total (S : FinPresentation queryDb) (hpos : 0 < S.card)
    (hwf : Fin S.card ⊨ cqWFSentence) : (cqDecode S).isSome :=
  cqDecode_eq S ▸ DescriptiveComplexity.cqDecode_total S hpos hwf

/-- Well-formedness together with the evaluation property is invariant. -/
theorem wf_and_queryHolds_iso {A B : Type} [queryDb.Structure A] [queryDb.Structure B]
    (e : A ≃[queryDb] B) :
    (A ⊨ cqWFSentence ∧ QueryHolds A) ↔ (B ⊨ cqWFSentence ∧ QueryHolds B) :=
  and_congr (StrongHomClass.realize_sentence e _) (DescriptiveComplexity.queryHolds_iso e)

/--
---
conclusion: Lax420092.DecodingAndWellFormed.wfCQEval_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem wfCQEval_iff (A : Type) [queryDb.Structure A] :
    WFCQEval A ↔ (A ⊨ cqWFSentence ∧ QueryHolds A) :=
  ofPred_iff @wf_and_queryHolds_iso A

/-- The library's well-formed problem, the meet of the well-formedness
sentence with its bundled problem, and the concept's agree on every
instance. -/
theorem wfCQEval_agree (A : Type) [queryDb.Structure A] :
    (DecisionProblem.ofSentence cqWFSentence ⊓ DescriptiveComplexity.CQEval) A ↔ WFCQEval A :=
  ((DescriptiveComplexity.DecisionProblem.min_holds _ _ A).trans
    (and_congr (DescriptiveComplexity.DecisionProblem.ofSentence_holds _ A)
      ((cqEval_agree A).trans (cqEval_iff A)))).trans (wfCQEval_iff A).symm

/--
---
conclusion: Lax420092.DecodingAndWellFormed.wfCQEval_NP_complete
---
Membership from the library's existential second-order definition of
evaluation, strengthened by the well-formedness sentence; hardness from the
library's reduction of 3-colorability to evaluation, whose image is
well-formed, 3-colorability being NP-hard by the catalog's statement for it.
-/
theorem wfCQEval_NP_complete : NP.Complete WFCQEval :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => wfCQEval_agree A).mp
      (DescriptiveComplexity.cqEval_sigmaSODefinable.inf_ofSentence cqWFSentence),
    Lax904597.NPClass.cofinalHard_of_foReduction
      (FOReduction.congr threeCol_agree wfCQEval_agree
        (DescriptiveComplexity.threeCol_fo_reduction_cqEval.withInvariant _
          fun V _ _ => DescriptiveComplexity.threeColToCQEval_wf V))
      Lax799700.ThreeColorability.threeCol_NP_complete.2⟩

end Lax420092Proofs.Bridge
