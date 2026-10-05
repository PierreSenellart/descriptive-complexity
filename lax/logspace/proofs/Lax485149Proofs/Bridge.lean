import Lax904597.NPClass
import Lax485149.ReachabilityInvariance
import Lax485149.DeterministicReachabilityInvariance
import Lax485149.TwoSatInvariance
import Lax485149.NLClosure
import Lax485149.LClosure
import Lax485149.TransitiveClosureClosure
import Lax485149.FirstOrderInTransitiveClosure
import Lax485149.ImmermanSzelepcsenyi
import Lax485149.KromAndTransitiveClosure
import Lax485149.NLIsTransitiveClosure
import Lax485149.NLEqCoNL
import Lax485149.ReachNLComplete
import Lax485149.UnreachNLComplete
import Lax485149.TwoSatNLComplete
import Lax485149.LSubsetNL
import Lax485149.ReachdLComplete
import Lax485149.UnreachdLComplete
import Lax485149.LEqCoL
import Lax485149.NLSubsetNP
import Lax485149.NLByAutomata
import Lax485149.LByAutomata
import Lax485149Proofs.DescriptiveComplexity.ImmermanSzelepcsenyi
import Lax485149Proofs.DescriptiveComplexity.TransitiveClosureReach
import Lax485149Proofs.DescriptiveComplexity.TransitiveClosureFO
import Lax485149Proofs.DescriptiveComplexity.TransitiveClosurePull
import Lax485149Proofs.DescriptiveComplexity.DetLogSpace
import Lax485149Proofs.DescriptiveComplexity.HeadCapture
import Lax485149Proofs.DescriptiveComplexity.HeadCaptureDet
import Lax485149Proofs.DescriptiveComplexity.Problems.TwoSat
import Lax485149Proofs.DescriptiveComplexity.Problems.ReachabilityDet.Complement

/-!
# The L and NL statements, from the library's theorems

Each claim is proved from the library's theorem of the same name. The logics,
the automata and the properties defining the problems are restated by the
concepts, so the library's theorems about them are the claims themselves; the
bundled problems are transported along the agreement between the library's
problem and the concept's, which the invariance of the property gives, and the
classes along the agreement of their membership predicates. Where the library
composes its own results, the bridges assume the submission's statements
instead: `NL = coNL` from the capture of NL by FO(TC) and
the closure of FO(TC) under complement, `L ⊆ NL` from the inclusion of the
logics.
-/

namespace Lax485149Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

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

/-! ### The problems: invariance, characterization, agreement -/

/--
---
conclusion: Lax485149.ReachabilityInvariance.reachable_iso
---
The library's invariance theorem for reachability.
-/
theorem reachable_iso {A B : Type} [stGraph.Structure A] [stGraph.Structure B] (e : A ≃[stGraph] B) :
    Reachable A ↔ Reachable B :=
  DescriptiveComplexity.reachable_iso e

/--
---
conclusion: Lax485149.ReachabilityInvariance.reach_iff
---
The property is invariant, by this submission's statement.
-/
theorem reach_iff (A : Type) [stGraph.Structure A] : REACH A ↔ Reachable A :=
  ofPred_iff Lax485149.ReachabilityInvariance.reachable_iso A

/--
---
conclusion: Lax485149.ReachabilityInvariance.unreach_iff
---
The complement of the characterization of REACH.
-/
theorem unreach_iff (A : Type) [stGraph.Structure A] : UNREACH A ↔ ¬Reachable A :=
  not_congr (Lax485149.ReachabilityInvariance.reach_iff A)

/-- The library's REACH and the concept's have the same instances. -/
theorem reach_agree (A : Type) [stGraph.Structure A] : DescriptiveComplexity.REACH A ↔ REACH A :=
  (reach_iff A).symm

/-- The library's UNREACH and the concept's have the same instances. -/
theorem unreach_agree (A : Type) [stGraph.Structure A] :
    DescriptiveComplexity.UNREACH A ↔ UNREACH A :=
  not_congr (reach_agree A)

/--
---
conclusion: Lax485149.DeterministicReachabilityInvariance.detReachable_iso
---
The library's invariance theorem for deterministic reachability.
-/
theorem detReachable_iso {A B : Type} [stGraph.Structure A] [stGraph.Structure B]
    (e : A ≃[stGraph] B) : DetReachable A ↔ DetReachable B :=
  DescriptiveComplexity.detReachable_iso e

/--
---
conclusion: Lax485149.DeterministicReachabilityInvariance.reachd_iff
---
The property is invariant, by this submission's statement.
-/
theorem reachd_iff (A : Type) [stGraph.Structure A] : REACHd A ↔ DetReachable A :=
  ofPred_iff Lax485149.DeterministicReachabilityInvariance.detReachable_iso A

/--
---
conclusion: Lax485149.DeterministicReachabilityInvariance.unreachd_iff
---
The complement of the characterization of REACHd.
-/
theorem unreachd_iff (A : Type) [stGraph.Structure A] : UNREACHd A ↔ ¬DetReachable A :=
  not_congr (Lax485149.DeterministicReachabilityInvariance.reachd_iff A)

/-- The library's REACHd and the concept's have the same instances. -/
theorem reachd_agree (A : Type) [stGraph.Structure A] : DescriptiveComplexity.REACHd A ↔ REACHd A :=
  (reachd_iff A).symm

/-- The library's UNREACHd and the concept's have the same instances. -/
theorem unreachd_agree (A : Type) [stGraph.Structure A] :
    DescriptiveComplexity.UNREACHd A ↔ UNREACHd A :=
  not_congr (reachd_agree A)

/--
---
conclusion: Lax485149.TwoSatInvariance.twoSatisfiable_iso
---
The library's invariance theorem for 2SAT.
-/
theorem twoSatisfiable_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    TwoSatisfiable A ↔ TwoSatisfiable B :=
  DescriptiveComplexity.twoSatisfiable_iso e

/--
---
conclusion: Lax485149.TwoSatInvariance.twoSat_iff
---
The property is invariant, by this submission's statement.
-/
theorem twoSat_iff (A : Type) [sat.Structure A] : TwoSAT A ↔ TwoSatisfiable A :=
  ofPred_iff Lax485149.TwoSatInvariance.twoSatisfiable_iso A

/-- The library's 2SAT and the concept's have the same instances. -/
theorem twoSat_agree (A : Type) [sat.Structure A] : DescriptiveComplexity.TwoSAT A ↔ TwoSAT A :=
  (twoSat_iff A).symm

/-! ### Closure laws -/

/--
---
conclusion: Lax485149.NLClosure.NL_mem_of_foReduction
---
The library's closure of SO-Krom definability under first-order reductions.
-/
theorem NL_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : NL.Mem Q) :
    NL.Mem P :=
  DescriptiveComplexity.SigmaSOKromDefinable.of_foReduction f h

/--
---
conclusion: Lax485149.NLClosure.NL_mem_of_orderedReduction
---
The library's closure of SO-Krom definability under ordered first-order
reductions.
-/
theorem NL_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q) (h : NL.Mem Q) :
    NL.Mem P :=
  DescriptiveComplexity.SigmaSOKromDefinable.of_orderedReduction f h

/--
---
conclusion: Lax485149.NLClosure.NL_mem_congr_finite
---
SO-Krom definability reads a problem on finite structures only.
-/
theorem NL_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : NL.Mem P ↔ NL.Mem Q :=
  DescriptiveComplexity.sigmaSOKromDefinable_congr h

/--
---
conclusion: Lax485149.LClosure.LOGSPACE_mem_of_foReduction
---
The library's closure of FO(DTC) definability under first-order reductions.
-/
theorem LOGSPACE_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : LOGSPACE.Mem Q) :
    LOGSPACE.Mem P :=
  DescriptiveComplexity.DTCDefinable.of_foReduction f h

/--
---
conclusion: Lax485149.LClosure.LOGSPACE_mem_of_orderedReduction
---
The library's closure of FO(DTC) definability under ordered first-order
reductions.
-/
theorem LOGSPACE_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : LOGSPACE.Mem Q) : LOGSPACE.Mem P :=
  DescriptiveComplexity.DTCDefinable.of_orderedReduction f h

/--
---
conclusion: Lax485149.LClosure.LOGSPACE_mem_congr_finite
---
FO(DTC) definability reads a problem on finite structures only.
-/
theorem LOGSPACE_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : LOGSPACE.Mem P ↔ LOGSPACE.Mem Q :=
  DescriptiveComplexity.dtcDefinable_congr h

/--
---
conclusion: Lax485149.TransitiveClosureClosure.tcDefinable_of_foReduction
---
The library's closure of FO(TC) definability under first-order reductions.
-/
theorem tcDefinable_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : TCDefinable Q) :
    TCDefinable P :=
  DescriptiveComplexity.TCDefinable.of_foReduction f h

/--
---
conclusion: Lax485149.TransitiveClosureClosure.tcDefinable_of_orderedReduction
---
The library's closure of FO(TC) definability under ordered first-order
reductions.
-/
theorem tcDefinable_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : TCDefinable Q) : TCDefinable P :=
  DescriptiveComplexity.TCDefinable.of_orderedReduction f h

/--
---
conclusion: Lax485149.TransitiveClosureClosure.tcDefinable_congr_finite
---
FO(TC) definability reads a problem on finite structures only.
-/
theorem tcDefinable_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : TCDefinable P ↔ TCDefinable Q :=
  DescriptiveComplexity.tcDefinable_congr h

/-! ### The logics -/

/--
---
conclusion: Lax485149.FirstOrderInTransitiveClosure.foDefinable_dtcDefinable
---
The library's walk that takes no step, a first-order sentence its condition
on starting nodes.
-/
theorem foDefinable_dtcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : FODefinable P) : DTCDefinable P :=
  DescriptiveComplexity.FODefinable.dtcDefinable h

/--
---
conclusion: Lax485149.FirstOrderInTransitiveClosure.dtcDefinable_tcDefinable
---
The library's reading of a determinized specification as a specification.
-/
theorem dtcDefinable_tcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : DTCDefinable P) : TCDefinable P :=
  DescriptiveComplexity.DTCDefinable.tcDefinable h

/--
---
conclusion: Lax485149.FirstOrderInTransitiveClosure.foDefinable_tcDefinable
---
The two inclusions of this submission, composed.
-/
theorem foDefinable_tcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : FODefinable P) : TCDefinable P :=
  Lax485149.FirstOrderInTransitiveClosure.dtcDefinable_tcDefinable
    (Lax485149.FirstOrderInTransitiveClosure.foDefinable_dtcDefinable h)

/--
---
conclusion: Lax485149.ImmermanSzelepcsenyi.tcDefinable_compl
---
The library's inductive-counting walk.
-/
theorem tcDefinable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : TCDefinable P) : TCDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.TCDefinable.compl h

/--
---
conclusion: Lax485149.KromAndTransitiveClosure.tcDefinable_compl_of_sigmaSOKromDefinable
---
The library's translation of a Krom program into the reachability condition of
its implication graph.
-/
theorem tcDefinable_compl_of_sigmaSOKromDefinable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (h : SigmaSOKromDefinable P) : TCDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.TCDefinable.compl_of_sigmaSOKromDefinable h

/--
---
conclusion: Lax485149.KromAndTransitiveClosure.sigmaSOKromDefinable_compl_of_tcDefinable
---
The library's Krom program guessing a set of nodes that contains the targets
and is closed under predecessors.
-/
theorem sigmaSOKromDefinable_compl_of_tcDefinable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (h : TCDefinable P) : SigmaSOKromDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.SigmaSOKromDefinable.compl_of_tcDefinable h

/--
---
conclusion: Lax485149.NLIsTransitiveClosure.tcDefinable_iff_mem_NL
---
The library's theorem, which composes the two translations with the closure
of FO(TC) under complement.
-/
theorem tcDefinable_iff_mem_NL {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    TCDefinable P ↔ NL.Mem P :=
  DescriptiveComplexity.tcDefinable_iff_mem_NL P

/--
---
conclusion: Lax485149.NLIsTransitiveClosure.mem_NL_iff_tcDefinable_compl
---
The library's theorem, the two translations composed.
-/
theorem mem_NL_iff_tcDefinable_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : NL.Mem P ↔ TCDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.mem_NL_iff_tcDefinable_compl P

/--
---
conclusion: Lax485149.NLEqCoNL.NL_eq_coNL
---
A problem is in NL exactly when its complement is FO(TC) definable, and
FO(TC) definability is membership in NL, both by this submission's statements;
so the two classes have the same members, and hardness is read off
membership.
-/
theorem NL_eq_coNL : NL = coNL :=
  ofMem_congr fun P =>
    (Lax485149.NLIsTransitiveClosure.mem_NL_iff_tcDefinable_compl P).trans
      (Lax485149.NLIsTransitiveClosure.tcDefinable_iff_mem_NL (DecisionProblem.compl P))

/-! ### Complete problems -/

/--
---
conclusion: Lax485149.ReachNLComplete.reach_tcDefinable
---
The library's one-mode specification, transported to the concept's problem.
-/
theorem reach_tcDefinable : TCDefinable REACH :=
  (Lax485149.TransitiveClosureClosure.tcDefinable_congr_finite fun A _ _ => reach_agree A).mp
    DescriptiveComplexity.reach_tcDefinable

/--
---
conclusion: Lax485149.ReachNLComplete.reach_hard_of_tcDefinable
---
The library's reduction building the graph of a specification, transported to
the concept's problem.
-/
theorem reach_hard_of_tcDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : TCDefinable P) : Nonempty (OrderedFOReduction P REACH) :=
  (DescriptiveComplexity.reach_hard_of_tcDefinable P h).map
    (OrderedFOReduction.congr (fun _ _ => Iff.rfl) reach_agree)

/--
---
conclusion: Lax485149.ReachNLComplete.reach_NL_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem reach_NL_complete : NL.Complete REACH :=
  ⟨(Lax485149.NLClosure.NL_mem_congr_finite fun A _ _ => reach_agree A).mp
      DescriptiveComplexity.REACH_NL_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => reach_agree A)
      DescriptiveComplexity.REACH_NL_complete.2⟩

/--
---
conclusion: Lax485149.UnreachNLComplete.unreach_NL_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem unreach_NL_complete : NL.Complete UNREACH :=
  ⟨(Lax485149.NLClosure.NL_mem_congr_finite fun A _ _ => unreach_agree A).mp
      DescriptiveComplexity.UNREACH_NL_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => unreach_agree A)
      DescriptiveComplexity.UNREACH_NL_complete.2⟩

/--
---
conclusion: Lax485149.TwoSatNLComplete.twoSat_NL_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem twoSat_NL_complete : NL.Complete TwoSAT :=
  ⟨(Lax485149.NLClosure.NL_mem_congr_finite fun A _ _ => twoSat_agree A).mp
      DescriptiveComplexity.TwoSAT_NL_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => twoSat_agree A)
      DescriptiveComplexity.TwoSAT_NL_complete.2⟩

/--
---
conclusion: Lax485149.LSubsetNL.LOGSPACE_subset_NL
---
An FO(DTC) definable problem is FO(TC) definable, and FO(TC) definability is
membership in NL, both by this submission's statements.
-/
theorem LOGSPACE_subset_NL {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : LOGSPACE.Mem P) : NL.Mem P :=
  (Lax485149.NLIsTransitiveClosure.tcDefinable_iff_mem_NL P).mp
    (Lax485149.FirstOrderInTransitiveClosure.dtcDefinable_tcDefinable h)

/--
---
conclusion: Lax485149.ReachdLComplete.reachd_dtcDefinable
---
The library's determinized one-mode specification, transported to the
concept's problem.
-/
theorem reachd_dtcDefinable : DTCDefinable REACHd :=
  (Lax485149.LClosure.LOGSPACE_mem_congr_finite fun A _ _ => reachd_agree A).mp
    DescriptiveComplexity.reachd_dtcDefinable

/--
---
conclusion: Lax485149.ReachdLComplete.reachd_hard_of_dtcDefinable
---
The library's reduction building the graph of a determinized specification,
transported to the concept's problem.
-/
theorem reachd_hard_of_dtcDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : DTCDefinable P) : Nonempty (OrderedFOReduction P REACHd) :=
  (DescriptiveComplexity.reachd_hard_of_dtcDefinable P h).map
    (OrderedFOReduction.congr (fun _ _ => Iff.rfl) reachd_agree)

/--
---
conclusion: Lax485149.ReachdLComplete.reachd_LOGSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem reachd_LOGSPACE_complete : LOGSPACE.Complete REACHd :=
  ⟨(Lax485149.LClosure.LOGSPACE_mem_congr_finite fun A _ _ => reachd_agree A).mp
      DescriptiveComplexity.REACHd_LOGSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => reachd_agree A)
      DescriptiveComplexity.REACHd_LOGSPACE_complete.2⟩

/--
---
conclusion: Lax485149.UnreachdLComplete.unreachd_LOGSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem unreachd_LOGSPACE_complete : LOGSPACE.Complete UNREACHd :=
  ⟨(Lax485149.LClosure.LOGSPACE_mem_congr_finite fun A _ _ => unreachd_agree A).mp
      DescriptiveComplexity.UNREACHd_LOGSPACE_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => unreachd_agree A)
      DescriptiveComplexity.UNREACHd_LOGSPACE_complete.2⟩

/--
---
conclusion: Lax485149.LEqCoL.LOGSPACE_eq_coLOGSPACE
---
The library's closure of FO(DTC) definability under complement, by the
step-counting walk; hardness is read off membership.
-/
theorem LOGSPACE_eq_coLOGSPACE : LOGSPACE = coLOGSPACE :=
  ofMem_congr fun P => (DescriptiveComplexity.mem_LOGSPACE_compl_iff P).symm

/--
---
conclusion: Lax485149.NLSubsetNP.NL_subset_NP
---
The library's inclusion, through 2SAT, the Horn fragment and HORN-SAT.
-/
theorem NL_subset_NP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : NL.Mem P) : NP.Mem P :=
  DescriptiveComplexity.NL_subset_NP h

/-! ### Automata -/

/--
---
conclusion: Lax485149.NLByAutomata.mem_NL_iff_automaton
---
The library's theorem: an automaton is a specification, and a specification is
compiled into an automaton.
-/
theorem mem_NL_iff_automaton {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L} :
    NL.Mem P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A :=
  DescriptiveComplexity.mem_NL_iff_automaton

/--
---
conclusion: Lax485149.NLByAutomata.tcDefinable_iff_automaton
---
The library's theorem.
-/
theorem tcDefinable_iff_automaton {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L} :
    TCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A :=
  DescriptiveComplexity.tcDefinable_iff_automaton

/--
---
conclusion: Lax485149.LByAutomata.mem_LOGSPACE_iff_automaton
---
The library's theorem, its determinism hypothesis read as a conjunct.
-/
theorem mem_LOGSPACE_iff_automaton {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L} :
    LOGSPACE.Mem P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k), M.IsDeterministic ∧
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A :=
  DescriptiveComplexity.mem_LOGSPACE_iff_automaton.trans
    ⟨fun ⟨k, M, hd, h⟩ => ⟨k, M, hd, h⟩, fun ⟨k, M, hd, h⟩ => ⟨k, M, hd, h⟩⟩

/--
---
conclusion: Lax485149.LByAutomata.dtcDefinable_iff_automaton
---
The library's theorem, its determinism hypothesis read as a conjunct.
-/
theorem dtcDefinable_iff_automaton {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L} :
    DTCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k), M.IsDeterministic ∧
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A :=
  DescriptiveComplexity.dtcDefinable_iff_automaton.trans
    ⟨fun ⟨k, M, hd, h⟩ => ⟨k, M, hd, h⟩, fun ⟨k, M, hd, h⟩ => ⟨k, M, hd, h⟩⟩

end Lax485149Proofs.Bridge
