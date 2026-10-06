import Lax904597.NPClass
import Lax485149.TwoSatInvariance
import Lax535992.HornSatInvariance
import Lax564036.TautologyInvariance
import Lax624099.FiniteSatisfiabilityInvariance
import Lax604544.IsomorphismInvariance
import Lax604544.RelationIsomorphismSemantics
import Lax604544.DegreeOfAProblem
import Lax604544.ClassesAsDegrees
import Lax604544.IsomorphismInNP
import Lax604544.GraphIsomorphismDegree
import Lax604544Proofs.DescriptiveComplexity.ClassDegrees
import Lax604544Proofs.DescriptiveComplexity.Degree
import Lax604544Proofs.DescriptiveComplexity.IsoGadget
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso.Defs
import Lax604544Proofs.DescriptiveComplexity.Problems.DigraphIso
import Lax604544Proofs.DescriptiveComplexity.Problems.GIDegree
import Lax604544Proofs.DescriptiveComplexity.Problems.GraphIso.Defs
import Lax604544Proofs.DescriptiveComplexity.Problems.GraphIso.Hardness

/-!
# The degree statements, from the library's theorems

The degree of a problem is defined in the concepts as the class of the
problems reducing to it, with cofinal hardness, which is what the library's
degree is once its closure proofs are forgotten. The isomorphism problems are
bundled in the concepts from their defining properties, and statements about
them are transported along the agreement with the library's problems. The
identities between a class and the degree of its complete problem are the
library's, each read on the concept's class and the concept's problem, whose
instances are those of the library's by the characterization lemmas of the
submissions that define them.
-/

namespace Lax604544Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

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

/-- Two classes with equivalent membership predicates are equal, hardness
being read off membership. -/
theorem ofMem_congr
    {M M' : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    (h : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (P : DecisionProblem L₀), M P ↔ M' P) :
    ComplexityClass.ofMem M = ComplexityClass.ofMem M' := by
  have hM : @M = @M' := by
    funext L₀ inst P
    exact propext (h P)
  rw [hM]

/-- Equal classes of the library have the same members. -/
theorem mem_of_lib_eq {C C' : DescriptiveComplexity.ComplexityClass} (h : C = C')
    {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : C.Mem P ↔ C'.Mem P := by
  rw [h]

/-- Reducing to a problem and reducing to one with the same instances are the
same thing. -/
theorem below_mem_agree {L₀ : Language.{0, 0}} [L₀.IsRelational] {Q Q' : DecisionProblem L₀}
    (hQ : ∀ (A : Type) [L₀.Structure A], Q A ↔ Q' A) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    Nonempty (OrderedFOReduction P Q) ↔ Nonempty (OrderedFOReduction P Q') :=
  ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) hQ),
    Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) fun A _ => (hQ A).symm)⟩

/-- Cofinal hardness only depends on the membership predicate up to
equivalence. -/
theorem cofinalHard_congr_mem
    {M M' : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    (h : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀), M Q ↔ M' Q)
    {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (hP : CofinalHard M P) : CofinalHard M' P :=
  by
  intro L' _ S hS L'' _ Q hQ
  exact hP S hS Q ((h Q).mpr hQ)

/--
---
conclusion: Lax604544.IsomorphismInvariance.hasDigraphIso_iso
---
The library's invariance theorem.
-/
theorem hasDigraphIso_iso {A B : Type} [twoGraphs.Structure A] [twoGraphs.Structure B]
    (e : A ≃[twoGraphs] B) :
    HasDigraphIso A ↔ HasDigraphIso B :=
  DescriptiveComplexity.hasDigraphIso_iso e

/--
---
conclusion: Lax604544.IsomorphismInvariance.digraphIso_iff
---
The property is invariant, by this submission's statement.
-/
theorem digraphIso_iff (A : Type) [twoGraphs.Structure A] : DigraphIso A ↔ HasDigraphIso A :=
  ofPred_iff (P := fun A _ => HasDigraphIso A)
    Lax604544.IsomorphismInvariance.hasDigraphIso_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem digraphIso_agree (A : Type) [twoGraphs.Structure A] :
    DescriptiveComplexity.DigraphIso A ↔ DigraphIso A :=
  (digraphIso_iff A).symm

/--
---
conclusion: Lax604544.IsomorphismInvariance.hasGraphIso_iso
---
The library's invariance theorem.
-/
theorem hasGraphIso_iso {A B : Type} [twoGraphs.Structure A] [twoGraphs.Structure B]
    (e : A ≃[twoGraphs] B) :
    HasGraphIso A ↔ HasGraphIso B :=
  DescriptiveComplexity.hasGraphIso_iso e

/--
---
conclusion: Lax604544.IsomorphismInvariance.graphIso_iff
---
The property is invariant, by this submission's statement.
-/
theorem graphIso_iff (A : Type) [twoGraphs.Structure A] : GraphIso A ↔ HasGraphIso A :=
  ofPred_iff (P := fun A _ => HasGraphIso A)
    Lax604544.IsomorphismInvariance.hasGraphIso_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem graphIso_agree (A : Type) [twoGraphs.Structure A] :
    DescriptiveComplexity.GraphIso A ↔ GraphIso A :=
  (graphIso_iff A).symm

/--
---
conclusion: Lax604544.IsomorphismInvariance.hasDagIso_iso
---
The library's invariance theorem.
-/
theorem hasDagIso_iso {A B : Type} [twoDags.Structure A] [twoDags.Structure B]
    (e : A ≃[twoDags] B) :
    HasDagIso A ↔ HasDagIso B :=
  DescriptiveComplexity.hasDagIso_iso e

/--
---
conclusion: Lax604544.IsomorphismInvariance.dagIso_iff
---
The property is invariant, by this submission's statement.
-/
theorem dagIso_iff (A : Type) [twoDags.Structure A] : DagIso A ↔ HasDagIso A :=
  ofPred_iff (P := fun A _ => HasDagIso A)
    Lax604544.IsomorphismInvariance.hasDagIso_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem dagIso_agree (A : Type) [twoDags.Structure A] :
    DescriptiveComplexity.DagIso A ↔ DagIso A :=
  (dagIso_iff A).symm

/--
---
conclusion: Lax604544.RelationIsomorphismSemantics.relIsoOn_iff_equiv
---
The library's theorem.
-/
theorem relIsoOn_iff_equiv {A : Type} (PV HV : A → Prop) (PE HE : A → A → Prop) :
    RelIsoOn PV HV PE HE ↔
      ∃ e : {x // PV x} ≃ {x // HV x}, ∀ (x y : {x // PV x}), PE ↑x ↑y ↔ HE ↑(e x) ↑(e y) :=
  DescriptiveComplexity.relIsoOn_iff_equiv PV HV PE HE

/--
---
conclusion: Lax604544.DegreeOfAProblem.below_complete_self
---
The library's theorem: the identity reduction.
-/
theorem below_complete_self {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q₀ : DecisionProblem L₀) :
    (below Q₀).Complete Q₀ :=
  let h := DescriptiveComplexity.ComplexityClass.below_complete_self Q₀
  ⟨h.1, h.2⟩

/--
---
conclusion: Lax604544.DegreeOfAProblem.complete_below_iff
---
The library's theorem, by composition of reductions.
-/
theorem complete_below_iff {L₀ : Language.{0, 0}} [L₀.IsRelational] {L : Language.{0, 0}}
    [L.IsRelational]
    {Q₀ : DecisionProblem L₀} (P : DecisionProblem L) :
    (below Q₀).Complete P ↔
      Nonempty (OrderedFOReduction P Q₀) ∧ Nonempty (RelOrderedFOReduction Q₀ P) :=
  ⟨fun h => (DescriptiveComplexity.ComplexityClass.complete_below_iff (Q₀ := Q₀) P).mp ⟨h.1, h.2⟩,
    fun h =>
      let c := (DescriptiveComplexity.ComplexityClass.complete_below_iff (Q₀ := Q₀) P).mpr h
      ⟨c.1, c.2⟩⟩

/--
---
conclusion: Lax604544.DegreeOfAProblem.below_congr
---
The library's composition of ordered reductions; the two degrees have the
same members, and hardness is read off membership.
-/
theorem below_congr {L₀ : Language.{0, 0}} [L₀.IsRelational] {L₁ : Language.{0, 0}}
    [L₁.IsRelational]
    {Q₀ : DecisionProblem L₀} {Q₁ : DecisionProblem L₁} (h₀ : Nonempty (OrderedFOReduction Q₀ Q₁))
    (h₁ : Nonempty (OrderedFOReduction Q₁ Q₀)) : below Q₀ = below Q₁ :=
  ofMem_congr fun _ =>
    ⟨fun h => h.elim fun f => h₀.elim fun g =>
        ⟨DescriptiveComplexity.OrderedFOReduction.trans f g⟩,
      fun h => h.elim fun f => h₁.elim fun g =>
        ⟨DescriptiveComplexity.OrderedFOReduction.trans f g⟩⟩

/--
---
conclusion: Lax604544.ClassesAsDegrees.NP_eq_below_sat
---
The library's theorem.
-/
theorem NP_eq_below_sat : NP = below SAT :=
  ofMem_congr fun P => mem_of_lib_eq DescriptiveComplexity.NP_eq_below_sat P

/--
---
conclusion: Lax604544.ClassesAsDegrees.coNP_eq_below_taut
---
The library's theorem, the degree being that of the concept's problem,
which has the same instances.
-/
theorem coNP_eq_below_taut : coNP = below TAUT :=
  ofMem_congr fun P =>
    (mem_of_lib_eq DescriptiveComplexity.coNP_eq_below_taut P).trans
      (below_mem_agree (fun A _ => (Lax564036.TautologyInvariance.taut_iff A).symm) P)

/--
---
conclusion: Lax604544.ClassesAsDegrees.PTIME_eq_below_hornSat
---
The library's theorem, the degree being that of the concept's problem,
which has the same instances.
-/
theorem PTIME_eq_below_hornSat : PTIME = below HORNSAT :=
  ofMem_congr fun P =>
    (mem_of_lib_eq DescriptiveComplexity.PTIME_eq_below_hornSat P).trans
      (below_mem_agree (fun A _ => (Lax535992.HornSatInvariance.hornSat_iff A).symm) P)

/--
---
conclusion: Lax604544.ClassesAsDegrees.NL_eq_below_twoSat
---
The library's theorem, the degree being that of the concept's problem,
which has the same instances.
-/
theorem NL_eq_below_twoSat : NL = below TwoSAT :=
  ofMem_congr fun P =>
    (mem_of_lib_eq DescriptiveComplexity.NL_eq_below_twoSat P).trans
      (below_mem_agree (fun A _ => (Lax485149.TwoSatInvariance.twoSat_iff A).symm) P)

/--
---
conclusion: Lax604544.ClassesAsDegrees.RE_eq_below_finsat
---
The library's theorem, the degree being that of the concept's problem,
which has the same instances.
-/
theorem RE_eq_below_finsat : RE = below FINSAT :=
  ofMem_congr fun P =>
    (mem_of_lib_eq DescriptiveComplexity.RE_eq_below_finsat P).trans
      (below_mem_agree (fun A _ => (Lax624099.FiniteSatisfiabilityInvariance.finsat_iff A).symm) P)

/--
---
conclusion: Lax604544.IsomorphismInNP.digraphIso_mem_NP
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem digraphIso_mem_NP : NP.Mem DigraphIso :=
  (Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => digraphIso_agree A).mp
    DescriptiveComplexity.digraphIso_mem_NP

/--
---
conclusion: Lax604544.IsomorphismInNP.graphIso_mem_NP
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem graphIso_mem_NP : NP.Mem GraphIso :=
  (Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => graphIso_agree A).mp
    DescriptiveComplexity.graphIso_mem_NP

/--
---
conclusion: Lax604544.IsomorphismInNP.dagIso_mem_NP
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem dagIso_mem_NP : NP.Mem DagIso :=
  (Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => dagIso_agree A).mp
    DescriptiveComplexity.dagIso_mem_NP

/--
---
conclusion: Lax604544.IsomorphismInNP.GI_subset_NP
---
The library's inclusion, the degree being that of the concept's problem,
which has the same instances.
-/
theorem GI_subset_NP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : GI.Mem P) :
    NP.Mem P :=
  DescriptiveComplexity.GI_subset_NP ((below_mem_agree (fun A _ => (graphIso_agree A).symm) P).mp h)

/--
---
conclusion: Lax604544.GraphIsomorphismDegree.graphIso_GI_complete
---
A problem is complete for its own degree, by this submission's statement.
-/
theorem graphIso_GI_complete : GI.Complete GraphIso :=
  Lax604544.DegreeOfAProblem.below_complete_self GraphIso

/--
---
conclusion: Lax604544.GraphIsomorphismDegree.digraphIso_GI_complete
---
The library's theorem, transported to the concept's problems along the
agreements.
-/
theorem digraphIso_GI_complete : GI.Complete DigraphIso :=
  ⟨(below_mem_agree graphIso_agree DigraphIso).mp
      (DescriptiveComplexity.digraphIso_GI_complete.1.map
    (OrderedFOReduction.congr digraphIso_agree fun _ _ => Iff.rfl)),
    cofinalHard_congr_mem (fun Q => below_mem_agree graphIso_agree Q)
      (Lax904597.NPClass.cofinalHard_congr
    (fun A _ _ => digraphIso_agree A) DescriptiveComplexity.digraphIso_GI_complete.2)⟩

/--
---
conclusion: Lax604544.GraphIsomorphismDegree.dagIso_GI_complete
---
The library's theorem, transported to the concept's problems along the
agreements.
-/
theorem dagIso_GI_complete : GI.Complete DagIso :=
  ⟨(below_mem_agree graphIso_agree DagIso).mp
      (DescriptiveComplexity.dagIso_GI_complete.1.map
    (OrderedFOReduction.congr dagIso_agree fun _ _ => Iff.rfl)),
    cofinalHard_congr_mem (fun Q => below_mem_agree graphIso_agree Q)
      (Lax904597.NPClass.cofinalHard_congr
    (fun A _ _ => dagIso_agree A) DescriptiveComplexity.dagIso_GI_complete.2)⟩

/--
---
conclusion: Lax604544.GraphIsomorphismDegree.GI_eq_below_digraphIso
---
The library's theorem, the two degrees being those of the concept's problems,
which have the same instances.
-/
theorem GI_eq_below_digraphIso : GI = below DigraphIso :=
  ofMem_congr fun P =>
    ((below_mem_agree (fun A _ => (graphIso_agree A).symm) P).trans
      (mem_of_lib_eq DescriptiveComplexity.GI_eq_below_digraphIso P)).trans
      (below_mem_agree digraphIso_agree P)

end Lax604544Proofs.Bridge
