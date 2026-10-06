import Lax904597.NPClass
import Lax535992.InflationaryIsLeastFixedPoint
import Lax134656.QsatInvariance
import Lax134656.SuccinctReachInvariance
import Lax134656.SpaceBoundedMachineInvariance
import Lax134656.PSPACEClosure
import Lax134656.TransitiveClosureWithoutOrder
import Lax134656.PSPACEEqCoPSPACE
import Lax134656.HierarchyInPSPACE
import Lax134656.PartialFixedPointCapture
import Lax134656.InflationaryInPartial
import Lax134656.PartialFixedPointClosure
import Lax134656.QsatPSPACEComplete
import Lax134656.SuccinctReachPSPACEComplete
import Lax134656.SpaceMachinesPSPACEComplete
import Lax134656.AbiteboulVianuOrdered
import Lax134656.AbiteboulVianu
import Lax134656Proofs.DescriptiveComplexity.AbiteboulVianu
import Lax134656Proofs.DescriptiveComplexity.Complexity
import Lax134656Proofs.DescriptiveComplexity.Exponential.Inclusions
import Lax134656Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax134656Proofs.DescriptiveComplexity.FixedPointOrderTransfer
import Lax134656Proofs.DescriptiveComplexity.FixedPointPartial
import Lax134656Proofs.DescriptiveComplexity.FixedPointPartialMachine
import Lax134656Proofs.DescriptiveComplexity.FixedPointPartialSpace
import Lax134656Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax134656Proofs.DescriptiveComplexity.Hierarchy
import Lax134656Proofs.DescriptiveComplexity.Interpretation
import Lax134656Proofs.DescriptiveComplexity.OrderedComposition
import Lax134656Proofs.DescriptiveComplexity.PSpace
import Lax134656Proofs.DescriptiveComplexity.PSpaceCompl
import Lax134656Proofs.DescriptiveComplexity.PSpaceHierarchy
import Lax134656Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax134656Proofs.DescriptiveComplexity.Problems.Qsat.Defs
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach.Defs
import Lax134656Proofs.DescriptiveComplexity.RelComposition
import Lax134656Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax134656Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax134656Proofs.DescriptiveComplexity.SecondOrderPull
import Lax134656Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax134656Proofs.DescriptiveComplexity.SecondOrderTransitiveClosureFree
import Lax134656Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull

/-!
# The PSPACE statements, from the library's theorems

Each claim is proved from the library's theorem of the same name. The logics
and the properties defining the problems are restated by the concepts; the
bundled problems are transported along the agreement between the library's
problem and the concept's, and the classes along the agreement of their
membership predicates. Where the library composes its own results the bridges
assume the submission's statements instead: the equality of PSPACE and
coPSPACE, the capture by partial fixed points, the inclusion of PH, and the
Abiteboul–Vianu theorem on ordered structures, which also assumes the capture
of PTIME by inflationary fixed points from the submission on polynomial time.
-/

namespace Lax134656Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

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

/-- Equal classes have the same members. -/
theorem mem_of_eq {C C' : ComplexityClass} (h : C = C') {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    C.Mem P ↔ C'.Mem P := by
  rw [h]

/-- The concept's `Σ` level and the library's have the same members. -/
theorem sigma_mem_agree (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    (SigmaP k).Mem P ↔ (DescriptiveComplexity.SigmaP k).Mem P := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact Iff.rfl

/-- The concept's `Π` level and the library's have the same members. -/
theorem pi_mem_agree (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    (PiP k).Mem P ↔ (DescriptiveComplexity.PiP k).Mem P := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact Iff.rfl

/-- The library's classes PTIME and PSPACE are equal exactly when the concept's
are: both say that the two membership predicates agree. -/
theorem ptime_eq_pspace_agree :
    DescriptiveComplexity.PTIME = DescriptiveComplexity.PSPACE ↔ PTIME = PSPACE := by
  constructor
  · intro h
    refine ofMem_congr fun P => ?_
    have hm : (DescriptiveComplexity.PTIME).Mem P ↔ (DescriptiveComplexity.PSPACE).Mem P := by
      rw [h]
    exact hm
  · intro h
    have hmem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (P : DecisionProblem L₀),
        (DescriptiveComplexity.PTIME).Mem P ↔ (DescriptiveComplexity.PSPACE).Mem P :=
      fun P => mem_of_eq h P
    refine DescriptiveComplexity.ComplexityClass.ext hmem fun P => ?_
    have hM : (fun {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀) =>
          (DescriptiveComplexity.PTIME).Mem Q) =
        (fun {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀) =>
          (DescriptiveComplexity.PSPACE).Mem Q) := by
      funext L₀ inst Q
      exact propext (hmem Q)
    show CofinalHard (fun {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀) =>
          (DescriptiveComplexity.PTIME).Mem Q) P ↔
        CofinalHard (fun {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀) =>
          (DescriptiveComplexity.PSPACE).Mem Q) P
    rw [hM]

/--
---
conclusion: Lax134656.QsatInvariance.qsatHolds_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem qsatHolds_iso {A B : Type} [qsat.Structure A] [qsat.Structure B] (e : A ≃[qsat] B) :
    QsatHolds A ↔ QsatHolds B :=
  (DescriptiveComplexity.QSAT).iso_invariant e

/--
---
conclusion: Lax134656.QsatInvariance.qsat_iff
---
The property is invariant, by this submission's statement.
-/
theorem qsat_iff (A : Type) [qsat.Structure A] : QSAT A ↔ QsatHolds A :=
  ofPred_iff (P := fun A _ => QsatHolds A)
    Lax134656.QsatInvariance.qsatHolds_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem qsat_agree (A : Type) [qsat.Structure A] :
    DescriptiveComplexity.QSAT A ↔ QSAT A :=
  (qsat_iff A).symm

/--
---
conclusion: Lax134656.SuccinctReachInvariance.succinctReachable_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem succinctReachable_iso {A B : Type} [transSys.Structure A] [transSys.Structure B]
    (e : A ≃[transSys] B) :
    SuccinctReachable A ↔ SuccinctReachable B :=
  (DescriptiveComplexity.SUCCINCTREACH).iso_invariant e

/--
---
conclusion: Lax134656.SuccinctReachInvariance.succinctReach_iff
---
The property is invariant, by this submission's statement.
-/
theorem succinctReach_iff (A : Type)
    [transSys.Structure A] : SUCCINCTREACH A ↔ SuccinctReachable A :=
  ofPred_iff (P := fun A _ => SuccinctReachable A)
    Lax134656.SuccinctReachInvariance.succinctReachable_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem succinctReach_agree (A : Type) [transSys.Structure A] :
    DescriptiveComplexity.SUCCINCTREACH A ↔ SUCCINCTREACH A :=
  (succinctReach_iff A).symm

/--
---
conclusion: Lax134656.SpaceBoundedMachineInvariance.ntmAcceptsSpace_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem ntmAcceptsSpace_iso {A B : Type} [turing.Structure A] [turing.Structure B]
    (e : A ≃[turing] B) :
    NTMAcceptsSpace A ↔ NTMAcceptsSpace B :=
  (DescriptiveComplexity.NTMAcceptSpace).iso_invariant e

/--
---
conclusion: Lax134656.SpaceBoundedMachineInvariance.dtmAcceptsSpace_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem dtmAcceptsSpace_iso {A B : Type} [turing.Structure A] [turing.Structure B]
    (e : A ≃[turing] B) :
    DTMAcceptsSpace A ↔ DTMAcceptsSpace B :=
  (DescriptiveComplexity.DTMAcceptSpace).iso_invariant e

/--
---
conclusion: Lax134656.SpaceBoundedMachineInvariance.ntmAcceptSpace_iff
---
The property is invariant, by this submission's statement.
-/
theorem ntmAcceptSpace_iff (A : Type) [turing.Structure A] : NTMAcceptSpace A ↔ NTMAcceptsSpace A :=
  ofPred_iff (P := fun A _ => NTMAcceptsSpace A)
    Lax134656.SpaceBoundedMachineInvariance.ntmAcceptsSpace_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem ntmAcceptSpace_agree (A : Type) [turing.Structure A] :
    DescriptiveComplexity.NTMAcceptSpace A ↔ NTMAcceptSpace A :=
  (ntmAcceptSpace_iff A).symm

/--
---
conclusion: Lax134656.SpaceBoundedMachineInvariance.dtmAcceptSpace_iff
---
The property is invariant, by this submission's statement.
-/
theorem dtmAcceptSpace_iff (A : Type) [turing.Structure A] : DTMAcceptSpace A ↔ DTMAcceptsSpace A :=
  ofPred_iff (P := fun A _ => DTMAcceptsSpace A)
    Lax134656.SpaceBoundedMachineInvariance.dtmAcceptsSpace_iso A

/-- The library's problem and the concept's have the same instances. -/
theorem dtmAcceptSpace_agree (A : Type) [turing.Structure A] :
    DescriptiveComplexity.DTMAcceptSpace A ↔ DTMAcceptSpace A :=
  (dtmAcceptSpace_iff A).symm

/--
---
conclusion: Lax134656.PSPACEClosure.PSPACE_mem_of_foReduction
---
The library's closure of SO(TC) definability under first-order reductions.
-/
theorem PSPACE_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : PSPACE.Mem Q) :
    PSPACE.Mem P :=
  DescriptiveComplexity.SOTCDefinable.of_foReduction f h

/--
---
conclusion: Lax134656.PSPACEClosure.PSPACE_mem_of_orderedReduction
---
The library's closure of SO(TC) definability under ordered first-order
reductions.
-/
theorem PSPACE_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : PSPACE.Mem Q) : PSPACE.Mem P :=
  DescriptiveComplexity.SOTCDefinable.of_orderedReduction f h

/--
---
conclusion: Lax134656.PSPACEClosure.PSPACE_mem_congr_finite
---
SO(TC) definability reads a problem on finite structures only.
-/
theorem PSPACE_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : PSPACE.Mem P ↔ PSPACE.Mem Q :=
  DescriptiveComplexity.sotcDefinable_congr h

/--
---
conclusion: Lax134656.TransitiveClosureWithoutOrder.sotcDefinable_iff_free
---
The library's walk guessing its order into its state.
-/
theorem sotcDefinable_iff_free {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L} :
    SOTCDefinable P ↔ SOTCDefinableFree P :=
  DescriptiveComplexity.sotcDefinable_iff_free

/--
---
conclusion: Lax134656.TransitiveClosureWithoutOrder.mem_PSPACE_iff_sotcDefinableFree
---
Membership in PSPACE is SO(TC) definability, which needs no order by this
submission's statement.
-/
theorem mem_PSPACE_iff_sotcDefinableFree {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    PSPACE.Mem P ↔ SOTCDefinableFree P :=
  Lax134656.TransitiveClosureWithoutOrder.sotcDefinable_iff_free

/--
---
conclusion: Lax134656.PSPACEEqCoPSPACE.sotcDefinable_compl
---
The library's theorem, through QSAT and its deterministic walk.
-/
theorem sotcDefinable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : SOTCDefinable P) : SOTCDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.SOTCDefinable.compl h

/--
---
conclusion: Lax134656.PSPACEEqCoPSPACE.PSPACE_eq_coPSPACE
---
SO(TC) definability is closed under complement, by this submission's
statement, and a problem has the finite instances of its double complement;
so the two classes have the same members, and hardness is read off
membership.
-/
theorem PSPACE_eq_coPSPACE : PSPACE = coPSPACE :=
  ofMem_congr fun P =>
    ⟨Lax134656.PSPACEEqCoPSPACE.sotcDefinable_compl, fun h =>
      (Lax134656.PSPACEClosure.PSPACE_mem_congr_finite
        (P := DecisionProblem.compl (DecisionProblem.compl P)) (Q := P)
        fun _ _ _ => not_not).mp
        (Lax134656.PSPACEEqCoPSPACE.sotcDefinable_compl h)⟩

/--
---
conclusion: Lax134656.HierarchyInPSPACE.NP_subset_PSPACE
---
The library's walk guessing its state and taking no step.
-/
theorem NP_subset_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : NP.Mem P) :
    PSPACE.Mem P :=
  DescriptiveComplexity.NP_subset_PSPACE h

/--
---
conclusion: Lax134656.HierarchyInPSPACE.PTIME_subset_PSPACE
---
The library's inclusion.
-/
theorem PTIME_subset_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PTIME.Mem P) :
    PSPACE.Mem P :=
  DescriptiveComplexity.PTIME_subset_PSPACE h

/--
---
conclusion: Lax134656.HierarchyInPSPACE.sigmaP_subset_PSPACE
---
The library's inclusion, the levels agreeing with the library's.
-/
theorem sigmaP_subset_PSPACE (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : (SigmaP k).Mem P) : PSPACE.Mem P :=
  DescriptiveComplexity.sigmaP_subset_PSPACE k ((sigma_mem_agree k P).mp h)

/--
---
conclusion: Lax134656.HierarchyInPSPACE.piP_subset_PSPACE
---
The library's inclusion, the levels agreeing with the library's.
-/
theorem piP_subset_PSPACE (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : (PiP k).Mem P) : PSPACE.Mem P :=
  DescriptiveComplexity.piP_subset_PSPACE k ((pi_mem_agree k P).mp h)

/--
---
conclusion: Lax134656.HierarchyInPSPACE.PH_subset_PSPACE
---
PH is the union of its levels, each contained in PSPACE by this submission's
statement.
-/
theorem PH_subset_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PH.Mem P) :
    PSPACE.Mem P :=
  h.elim fun k hk => Lax134656.HierarchyInPSPACE.sigmaP_subset_PSPACE k P hk

/--
---
conclusion: Lax134656.PartialFixedPointCapture.pfpDefinable_sotcDefinable
---
The library's reading of a partial iteration as a deterministic walk.
-/
theorem pfpDefinable_sotcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : PFPDefinable P) : SOTCDefinable P :=
  DescriptiveComplexity.PFPDefinable.sotcDefinable h

/--
---
conclusion: Lax134656.PartialFixedPointCapture.pfpDefinable_of_mem_PSPACE
---
The library's partial fixed point iterating the complete machine problem.
-/
theorem pfpDefinable_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : PSPACE.Mem P) : PFPDefinable P :=
  DescriptiveComplexity.pfpDefinable_of_mem_PSPACE h

/--
---
conclusion: Lax134656.PartialFixedPointCapture.pfpDefinable_iff_mem_PSPACE
---
The two inclusions of this submission.
-/
theorem pfpDefinable_iff_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    PFPDefinable P ↔ PSPACE.Mem P :=
  ⟨Lax134656.PartialFixedPointCapture.pfpDefinable_sotcDefinable,
    Lax134656.PartialFixedPointCapture.pfpDefinable_of_mem_PSPACE⟩

/--
---
conclusion: Lax134656.InflationaryInPartial.ifpDefinable_pfpDefinable
---
The library's inflation of the step formulas.
-/
theorem ifpDefinable_pfpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinable P) : PFPDefinable P :=
  DescriptiveComplexity.IFPDefinable.pfpDefinable h

/--
---
conclusion: Lax134656.InflationaryInPartial.ifpDefinableFree_pfpDefinableFree
---
The library's inflation of the step formulas.
-/
theorem ifpDefinableFree_pfpDefinableFree {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L}
    (h : IFPDefinableFree P) : PFPDefinableFree P :=
  DescriptiveComplexity.IFPDefinableFree.pfpDefinableFree h

/--
---
conclusion: Lax134656.InflationaryInPartial.ifpDefinableFree_ifpDefinable
---
The library's reading of a definition over the ordered expansion.
-/
theorem ifpDefinableFree_ifpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinableFree P) : IFPDefinable P :=
  DescriptiveComplexity.IFPDefinableFree.ifpDefinable h

/--
---
conclusion: Lax134656.InflationaryInPartial.pfpDefinableFree_pfpDefinable
---
The library's reading of a definition over the ordered expansion.
-/
theorem pfpDefinableFree_pfpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : PFPDefinableFree P) : PFPDefinable P :=
  DescriptiveComplexity.PFPDefinableFree.pfpDefinable h

/--
---
conclusion: Lax134656.PartialFixedPointClosure.pfpDefinable_of_foReduction
---
The library's pullback of a simultaneous induction.
-/
theorem pfpDefinable_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : PFPDefinable Q) :
    PFPDefinable P :=
  DescriptiveComplexity.PFPDefinable.of_foReduction f h

/--
---
conclusion: Lax134656.PartialFixedPointClosure.pfpDefinable_of_orderedReduction
---
The library's pullback of a simultaneous induction.
-/
theorem pfpDefinable_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : PFPDefinable Q) : PFPDefinable P :=
  DescriptiveComplexity.PFPDefinable.of_orderedReduction f h

/--
---
conclusion: Lax134656.PartialFixedPointClosure.pfpDefinable_of_relOrderedReduction
---
The library's pullback onto the definable domain.
-/
theorem pfpDefinable_of_relOrderedReduction {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : RelOrderedFOReduction P Q)
    (h : PFPDefinable Q) : PFPDefinable P :=
  DescriptiveComplexity.PFPDefinable.of_relOrderedReduction f h

/--
---
conclusion: Lax134656.PartialFixedPointClosure.pfpDefinable_congr_finite
---
The definability notion reads a problem on finite structures only.
-/
theorem pfpDefinable_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    PFPDefinable P ↔ PFPDefinable Q :=
  DescriptiveComplexity.pfpDefinable_congr h

/--
---
conclusion: Lax134656.QsatPSPACEComplete.qsat_PSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem qsat_PSPACE_complete : PSPACE.Complete QSAT :=
  ⟨(Lax134656.PSPACEClosure.PSPACE_mem_congr_finite fun A _ _ => qsat_agree A).mp
      DescriptiveComplexity.QSAT_PSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => qsat_agree A)
      DescriptiveComplexity.QSAT_PSPACE_complete.2⟩

/--
---
conclusion: Lax134656.QsatPSPACEComplete.qsat_coPSPACE_complete
---
The two classes are equal, by this submission's statements.
-/
theorem qsat_coPSPACE_complete : coPSPACE.Complete QSAT :=
  Lax134656.PSPACEEqCoPSPACE.PSPACE_eq_coPSPACE ▸ Lax134656.QsatPSPACEComplete.qsat_PSPACE_complete

/--
---
conclusion: Lax134656.SuccinctReachPSPACEComplete.succinctReach_PSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem succinctReach_PSPACE_complete : PSPACE.Complete SUCCINCTREACH :=
  ⟨(Lax134656.PSPACEClosure.PSPACE_mem_congr_finite fun A _ _ => succinctReach_agree A).mp
      DescriptiveComplexity.SUCCINCTREACH_PSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => succinctReach_agree A)
      DescriptiveComplexity.SUCCINCTREACH_PSPACE_complete.2⟩

/--
---
conclusion: Lax134656.SpaceMachinesPSPACEComplete.dtmAcceptSpace_PSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem dtmAcceptSpace_PSPACE_complete : PSPACE.Complete DTMAcceptSpace :=
  ⟨(Lax134656.PSPACEClosure.PSPACE_mem_congr_finite fun A _ _ => dtmAcceptSpace_agree A).mp
      DescriptiveComplexity.dtmAcceptSpace_PSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => dtmAcceptSpace_agree A)
      DescriptiveComplexity.dtmAcceptSpace_PSPACE_complete.2⟩

/--
---
conclusion: Lax134656.SpaceMachinesPSPACEComplete.ntmAcceptSpace_PSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem ntmAcceptSpace_PSPACE_complete : PSPACE.Complete NTMAcceptSpace :=
  ⟨(Lax134656.PSPACEClosure.PSPACE_mem_congr_finite fun A _ _ => ntmAcceptSpace_agree A).mp
      DescriptiveComplexity.ntmAcceptSpace_PSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => ntmAcceptSpace_agree A)
      DescriptiveComplexity.ntmAcceptSpace_PSPACE_complete.2⟩

/--
---
conclusion: Lax134656.SpaceMachinesPSPACEComplete.le_dtmAcceptSpace_of_mem_PSPACE
---
The deterministic problem is PSPACE-hard, by this submission's statement, and
cofinal hardness is the usual one, a statement of the core.
-/
theorem le_dtmAcceptSpace_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : PSPACE.Mem P) : Nonempty (RelOrderedFOReduction P DTMAcceptSpace) :=
  (Lax904597.NPClass.cofinalHard_iff _ DTMAcceptSpace).mp
    Lax134656.SpaceMachinesPSPACEComplete.dtmAcceptSpace_PSPACE_complete.2 P h

/--
---
conclusion: Lax134656.AbiteboulVianuOrdered.ifpDefinable_eq_pfpDefinable_iff_ptime_eq_pspace
---
The two capture theorems: FO(≤, IFP) is PTIME, a statement of the submission
on polynomial time, and FO(≤, PFP) is PSPACE, by this submission's statement.
-/
theorem ifpDefinable_eq_pfpDefinable_iff_ptime_eq_pspace :
    (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
        IFPDefinable P ↔ PFPDefinable P) ↔
      PTIME = PSPACE :=
  ⟨fun h => ofMem_congr fun P =>
      (Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_iff_mem_PTIME P).symm.trans
        ((h P).trans (Lax134656.PartialFixedPointCapture.pfpDefinable_iff_mem_PSPACE P)),
    fun h _ _ P =>
      (Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_iff_mem_PTIME P).trans
        ((mem_of_eq h P).trans
          (Lax134656.PartialFixedPointCapture.pfpDefinable_iff_mem_PSPACE P).symm)⟩

/--
---
conclusion: Lax134656.AbiteboulVianu.ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace
---
The library's theorem, the equality of its two classes being the equality of
the concept's.
-/
theorem ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace :
    (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
        IFPDefinableFree P ↔ PFPDefinableFree P) ↔
      PTIME = PSPACE :=
  DescriptiveComplexity.ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace.trans
    ptime_eq_pspace_agree

end Lax134656Proofs.Bridge
