import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.SetFamily
import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem
import Lax117614.GraphCrawlingInvariance
import Lax117614.GraphCrawlingNPComplete
import Lax117614.CrawlInstances
import Lax117614.CrawlEncoding
import Lax117614.CrawlDecoding
import Lax117614Proofs.DescriptiveComplexity.Examples.GraphCrawling

/-!
# The crawling statements, from the library's theorems

Each claim of the concept module is proved from the library's theorem of the
same name, transported along the agreement between the library's bundled
problem and the concept's, which is given by the invariance of the property.
NP-completeness assumes the catalog's statement for Set Cover and the core's
closure laws, so the archive's proof network shows the reduction from Set
Cover as an edge.
-/

namespace Lax117614Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem Lax117614.CrawlInstances

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

/-- An ordered first-order reduction transported along agreements of its two
ends. -/
def OrderedFOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q Q' : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : OrderedFOReduction P Q) : OrderedFOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }

/--
---
conclusion: Lax117614.GraphCrawlingInvariance.hasCheapCrawl_iso
---
The library's invariance theorem for HasCheapCrawl.
-/
theorem hasCheapCrawl_iso {A B : Type} [siteGraph.Structure A] [siteGraph.Structure B]
    (e : A ≃[siteGraph] B) : HasCheapCrawl A ↔ HasCheapCrawl B :=
  DescriptiveComplexity.hasCheapCrawl_iso e

/--
---
conclusion: Lax117614.GraphCrawlingInvariance.graphCrawling_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem graphCrawling_iff (A : Type) [siteGraph.Structure A] : GraphCrawling A ↔ HasCheapCrawl A :=
  ofPred_iff @DescriptiveComplexity.hasCheapCrawl_iso A

/-- The library's bundled GraphCrawling and the concept's agree on every
website graph. -/
theorem graphCrawling_agree (A : Type) [siteGraph.Structure A] :
    DescriptiveComplexity.GraphCrawling A ↔ GraphCrawling A :=
  (graphCrawling_iff A).symm

/-- The library's bundled Set Cover and the catalog's agree on every set
system, by the catalog's characterization of its problem. -/
theorem setCover_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SetCover A ↔ Lax799700.SetFamily.SetCover A :=
  (Lax799700.SetFamily.setCover_iff A).symm

/--
---
conclusion: Lax117614.GraphCrawlingNPComplete.graphCrawling_NP_complete
---
Membership from the library's existential second-order definition of graph
crawling; hardness from the library's ordered first-order reduction out of
Set Cover, which is NP-hard by the catalog's statement for it. Both are
transported to the concept's problem along the agreements.
-/
theorem graphCrawling_NP_complete : NP.Complete GraphCrawling :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => graphCrawling_agree A).mp
      DescriptiveComplexity.graphCrawling_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (OrderedFOReduction.congr setCover_agree graphCrawling_agree
        DescriptiveComplexity.setCover_ordered_fo_reduction_graphCrawling)
      Lax799700.SetFamily.setCover_NP_complete.2⟩

/--
---
conclusion: Lax117614.CrawlEncoding.crawlEncoding_faithful
---
The library's faithfulness theorem for its bundled encoding, whose structure
on the pages of an instance is the concept's.
-/
theorem crawlEncoding_faithful (i : CrawlInstance) :
    ConcreteCrawlHolds i ↔ GraphCrawling (Fin (i.n + 1)) :=
  (DescriptiveComplexity.crawlEncoding_faithful i).trans (graphCrawling_agree _)

/--
---
conclusion: Lax117614.CrawlEncoding.crawlSize_ge_card
---
The page count is one of the summands of the textbook size.
-/
theorem crawlSize_ge_card (i : CrawlInstance) : i.n + 1 ≤ crawlSize i := by
  obtain ⟨n, E, r, T, B⟩ := i
  simp only [crawlSize]
  omega

/--
---
conclusion: Lax117614.CrawlEncoding.crawlSize_le_card
---
The bound the library discharges when it bundles the encoding: links are at
most quadratic in the pages, targets and the clamped budget at most linear.
-/
theorem crawlSize_le_card (i : CrawlInstance) : crawlSize i ≤ 4 * (i.n + 2) ^ 2 := by
  obtain ⟨n, E, r, T, B⟩ := i
  have hE : E.card ≤ (n + 1) * (n + 1) := by
    simpa [Fintype.card_prod, Fintype.card_fin] using E.card_le_univ
  have hT : T.card ≤ n + 1 := by
    simpa [Fintype.card_fin] using T.card_le_univ
  have hB : B.1 < n + 2 := B.isLt
  simp only [crawlSize]
  nlinarith

/--
---
conclusion: Lax117614.CrawlDecoding.crawlDecode_sound
---
The library's soundness theorem for its decoder, the structure a presentation
presents being the concept's.
-/
theorem crawlDecode_sound (S : FinPresentation siteGraph) (i : CrawlInstance)
    (hi : i ∈ crawlDecode S) : ConcreteCrawlHolds i ↔ GraphCrawling (Fin S.card) :=
  (DescriptiveComplexity.crawlDecode_sound S i hi).trans (graphCrawling_agree _)

/--
---
conclusion: Lax117614.CrawlDecoding.crawlDecode_total
---
The library's totality theorem for its decoder.
-/
theorem crawlDecode_total (S : FinPresentation siteGraph) (hpos : 0 < S.card)
    (hwf : Fin S.card ⊨ crawlWFSentence) : (crawlDecode S).isSome :=
  DescriptiveComplexity.crawlDecode_total S hpos hwf

/-- Well-formedness together with the crawling property is invariant. -/
theorem wf_and_hasCheapCrawl_iso {A B : Type} [siteGraph.Structure A] [siteGraph.Structure B]
    (e : A ≃[siteGraph] B) :
    (A ⊨ crawlWFSentence ∧ HasCheapCrawl A) ↔ (B ⊨ crawlWFSentence ∧ HasCheapCrawl B) :=
  and_congr (StrongHomClass.realize_sentence e _) (DescriptiveComplexity.hasCheapCrawl_iso e)

/--
---
conclusion: Lax117614.CrawlDecoding.wfGraphCrawling_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem wfGraphCrawling_iff (A : Type) [siteGraph.Structure A] :
    WFGraphCrawling A ↔ (A ⊨ crawlWFSentence ∧ HasCheapCrawl A) :=
  ofPred_iff @wf_and_hasCheapCrawl_iso A

/-- The library's well-formed problem, the meet of the well-formedness
sentence with its bundled problem, and the concept's agree on every website
graph. -/
theorem wfGraphCrawling_agree (A : Type) [siteGraph.Structure A] :
    (DecisionProblem.ofSentence crawlWFSentence ⊓ DescriptiveComplexity.GraphCrawling) A ↔
      WFGraphCrawling A :=
  ((DescriptiveComplexity.DecisionProblem.min_holds _ _ A).trans
    (and_congr (DescriptiveComplexity.DecisionProblem.ofSentence_holds _ A)
      ((graphCrawling_agree A).trans (graphCrawling_iff A)))).trans
    (wfGraphCrawling_iff A).symm

/--
---
conclusion: Lax117614.CrawlDecoding.wfGraphCrawling_NP_complete
---
Membership from the library's existential second-order definition of graph
crawling, strengthened by the first-order well-formedness sentence; hardness
from the library's ordered first-order reduction out of Set Cover, whose image
is well-formed, Set Cover being NP-hard by the catalog's statement for it.
Both are transported to the concept's problem along the agreements.
-/
theorem wfGraphCrawling_NP_complete : NP.Complete WFGraphCrawling :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => wfGraphCrawling_agree A).mp
      (DescriptiveComplexity.graphCrawling_sigmaSODefinable.inf_ofSentence crawlWFSentence),
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (OrderedFOReduction.congr setCover_agree wfGraphCrawling_agree
        (DescriptiveComplexity.setCover_ordered_fo_reduction_graphCrawling.withInvariant _
          fun A _ _ _ _ => DescriptiveComplexity.crawlInterp_wf A))
      Lax799700.SetFamily.setCover_NP_complete.2⟩

end Lax117614Proofs.Bridge
