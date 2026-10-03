import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Feedback
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Reductions
import Lax799700Proofs.Bridge.CliqueFamily

namespace Lax799700Proofs.Bridge.Feedback

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Feedback

/--
---
conclusion: Lax799700.Feedback.hasSmallFeedbackSet_iso
---
The library's invariance theorem for HasSmallFeedbackSet.
-/
theorem hasSmallFeedbackSet_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasSmallFeedbackSet A ↔ HasSmallFeedbackSet B :=
  DescriptiveComplexity.hasSmallFeedbackSet_iso e

/--
---
conclusion: Lax799700.Feedback.feedbackVertexSet_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem feedbackVertexSet_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : FeedbackVertexSet A ↔ HasSmallFeedbackSet A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallFeedbackSet_iso A

/-- The library's bundled FeedbackVertexSet and the catalog's agree on every structure. -/
theorem feedbackVertexSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.FeedbackVertexSet A ↔ FeedbackVertexSet A :=
  (feedbackVertexSet_iff A).symm

/--
---
conclusion: Lax799700.Feedback.feedbackVertexSet_NP_complete
---
Membership from the library's existential second-order definition of
FeedbackVertexSet; hardness from the library's reduction out of VertexCover,
which is NP-hard by the catalog’s statement for it. Both are transported to
the catalog's problems along the agreements.
-/
theorem feedbackVertexSet_NP_complete : NP.Complete FeedbackVertexSet :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => feedbackVertexSet_agree A).mp DescriptiveComplexity.feedbackVertexSet_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.vertexCover_agree feedbackVertexSet_agree DescriptiveComplexity.vertexCover_fo_reduction_feedbackVertexSet) Lax799700.CliqueFamily.vertexCover_NP_complete.2⟩

/--
---
conclusion: Lax799700.Feedback.hasSmallFeedbackArcSet_iso
---
The library's invariance theorem for HasSmallFeedbackArcSet.
-/
theorem hasSmallFeedbackArcSet_iso {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A] [Lax799700.Feedback.markedArcGraph.Structure B] (e : A ≃[Lax799700.Feedback.markedArcGraph] B) :
    HasSmallFeedbackArcSet A ↔ HasSmallFeedbackArcSet B :=
  DescriptiveComplexity.hasSmallFeedbackArcSet_iso e

/--
---
conclusion: Lax799700.Feedback.feedbackArcSet_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem feedbackArcSet_iff (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] : FeedbackArcSet A ↔ HasSmallFeedbackArcSet A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallFeedbackArcSet_iso A

/-- The library's bundled FeedbackArcSet and the catalog's agree on every structure. -/
theorem feedbackArcSet_agree (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] : DescriptiveComplexity.FeedbackArcSet A ↔ FeedbackArcSet A :=
  (feedbackArcSet_iff A).symm

/--
---
conclusion: Lax799700.Feedback.feedbackArcSet_NP_complete
---
Membership from the library's existential second-order definition of
FeedbackArcSet; hardness from the library's reduction out of
FeedbackVertexSet, which is NP-hard by the catalog’s statement for it. Both
are transported to the catalog's problems along the agreements.
-/
theorem feedbackArcSet_NP_complete : NP.Complete FeedbackArcSet :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => feedbackArcSet_agree A).mp DescriptiveComplexity.feedbackArcSet_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.Feedback.feedbackVertexSet_agree feedbackArcSet_agree DescriptiveComplexity.feedbackVertexSet_fo_reduction_feedbackArcSet) Lax799700.Feedback.feedbackVertexSet_NP_complete.2⟩

end Lax799700Proofs.Bridge.Feedback
