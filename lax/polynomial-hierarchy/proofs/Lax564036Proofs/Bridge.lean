import Lax904597.NPClass
import Lax535992.PTIMEEqCoPTIME
import Lax564036.TautologyInvariance
import Lax564036.ThreeDnfTautologyInvariance
import Lax564036.SatUnsatInvariance
import Lax564036.QuantifiedBooleanFormulasInvariance
import Lax564036.AlternatingMachineInvariance
import Lax564036.HierarchyDuality
import Lax564036.HierarchyInclusions
import Lax564036.PolynomialTimeInHierarchy
import Lax564036.CoNPClosure
import Lax564036.DPClosure
import Lax564036.DPInclusions
import Lax564036.TautCoNPComplete
import Lax564036.ThreeDnfTautCoNPComplete
import Lax564036.SatUnsatDPComplete
import Lax564036.QbfComplete
import Lax564036.AlternatingMachineComplete
import Lax564036Proofs.DescriptiveComplexity.Complexity
import Lax564036Proofs.DescriptiveComplexity.Difference
import Lax564036Proofs.DescriptiveComplexity.Hierarchy
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat
import Lax564036Proofs.DescriptiveComplexity.Problems.Machine.AltDefs
import Lax564036Proofs.DescriptiveComplexity.Problems.MachineAlt
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf.Defs
import Lax564036Proofs.DescriptiveComplexity.Problems.SatUnsat
import Lax564036Proofs.DescriptiveComplexity.Problems.SatUnsat.Hardness
import Lax564036Proofs.DescriptiveComplexity.Problems.Taut
import Lax564036Proofs.DescriptiveComplexity.Problems.ThreeDnfTaut
import Lax564036Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax564036Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax564036Proofs.DescriptiveComplexity.SecondOrderPull

/-!
# The hierarchy statements, from the library's theorems

Each claim is proved from the library's theorem of the same name. The
properties defining the problems are restated by the concepts; the bundled
problems are transported along the agreement between the library's problem and
the concept's, which the invariance of the property gives. The levels of the
hierarchy are defined in the concepts by the same case distinction as in the
library, on the classes of the submissions this one requires, and agree with
the library's level by level. The one-block completeness statements are
instances of the general ones, and the equality of the two classes of level
zero is the closure of polynomial time under complement, a statement of the
submission on polynomial time.
-/

namespace Lax564036Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

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

/-- Completeness for a class of the library, transported along an agreement of
the finite instances. -/
theorem complete_congr (C : DescriptiveComplexity.ComplexityClass) {L : Language.{0, 0}}
    [L.IsRelational]
    {P P' : DecisionProblem L} (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A)
    (hc : C.Complete P) : C.Mem P' ∧ C.Hard P' :=
  ⟨(C.mem_congr_finite h).mp hc.1, (C.hard_congr_finite h).mp hc.2⟩

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

/-- Membership in the library's PH is membership in the concept's. -/
theorem ph_of_lib {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : DescriptiveComplexity.PH.Mem P) : PH.Mem P :=
  h.elim fun k hk => ⟨k, (sigma_mem_agree k P).mpr hk⟩

/-! ### The problems: invariance, characterization, agreement -/

/--
---
conclusion: Lax564036.TautologyInvariance.tautology_iso
---
The library's invariance theorem.
-/
theorem tautology_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    Tautology A ↔ Tautology B :=
  DescriptiveComplexity.tautology_iso e

/--
---
conclusion: Lax564036.TautologyInvariance.taut_iff
---
The property is invariant, by this submission's statement.
-/
theorem taut_iff (A : Type) [sat.Structure A] : TAUT A ↔ Tautology A :=
  ofPred_iff Lax564036.TautologyInvariance.tautology_iso A

/-- The library's TAUT and the concept's have the same instances. -/
theorem taut_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.TAUT A ↔ TAUT A :=
  (taut_iff A).symm

/--
---
conclusion: Lax564036.ThreeDnfTautologyInvariance.threeDnfTautology_iso
---
The library's invariance theorem.
-/
theorem threeDnfTautology_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    ThreeDnfTautology A ↔ ThreeDnfTautology B :=
  DescriptiveComplexity.threeDnfTautology_iso e

/--
---
conclusion: Lax564036.ThreeDnfTautologyInvariance.threeDnfTaut_iff
---
The property is invariant, by this submission's statement.
-/
theorem threeDnfTaut_iff (A : Type) [sat.Structure A] : ThreeDnfTAUT A ↔ ThreeDnfTautology A :=
  ofPred_iff Lax564036.ThreeDnfTautologyInvariance.threeDnfTautology_iso A

/-- The library's 3-DNF-TAUT and the concept's have the same instances. -/
theorem threeDnfTaut_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.ThreeDnfTAUT A ↔ ThreeDnfTAUT A :=
  (threeDnfTaut_iff A).symm

/--
---
conclusion: Lax564036.ThreeDnfTautologyInvariance.threeUnsatisfiable_iso
---
The library's invariance theorem.
-/
theorem threeUnsatisfiable_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    ThreeUnsatisfiable A ↔ ThreeUnsatisfiable B :=
  DescriptiveComplexity.threeUnsatisfiable_iso e

/--
---
conclusion: Lax564036.ThreeDnfTautologyInvariance.threeUnsat_iff
---
The property is invariant, by this submission's statement.
-/
theorem threeUnsat_iff (A : Type) [sat.Structure A] : ThreeUNSAT A ↔ ThreeUnsatisfiable A :=
  ofPred_iff Lax564036.ThreeDnfTautologyInvariance.threeUnsatisfiable_iso A

/-- The library's 3-UNSAT and the concept's have the same instances. -/
theorem threeUnsat_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.ThreeUNSAT A ↔ ThreeUNSAT A :=
  (threeUnsat_iff A).symm

/--
---
conclusion: Lax564036.SatUnsatInvariance.satWith_iso
---
The library's invariance theorem.
-/
theorem satWith_iso {A B : Type} [satPair.Structure A] [satPair.Structure B] (e : A ≃[satPair] B)
    (isCl : satPair.Relations 1) (pos neg : satPair.Relations 2) :
    SatWith A isCl pos neg ↔ SatWith B isCl pos neg :=
  DescriptiveComplexity.satWith_iso e isCl pos neg

/--
---
conclusion: Lax564036.SatUnsatInvariance.satUnsat_iff
---
Both sides are invariant, by this submission's statement.
-/
theorem satUnsat_iff (A : Type) [satPair.Structure A] :
    SATUNSAT A ↔ (SatWith A spIsCl₁ spPos₁ spNeg₁ ∧ ¬SatWith A spIsCl₂ spPos₂ spNeg₂) :=
  ofPred_iff (P := fun A _ =>
      (SatWith A spIsCl₁ spPos₁ spNeg₁ ∧ ¬SatWith A spIsCl₂ spPos₂ spNeg₂))
    (fun e => and_congr (Lax564036.SatUnsatInvariance.satWith_iso e _ _ _)
      (not_congr (Lax564036.SatUnsatInvariance.satWith_iso e _ _ _))) A

/-- The library's SAT-UNSAT and the concept's have the same instances. -/
theorem satUnsat_agree (A : Type) [satPair.Structure A] :
    DescriptiveComplexity.SATUNSAT A ↔ SATUNSAT A :=
  (satUnsat_iff A).symm

/--
---
conclusion: Lax564036.QuantifiedBooleanFormulasInvariance.qbfTrue_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem qbfTrue_iso (k : ℕ) (start cnf : Bool) {A B : Type} [(qbf k).Structure A]
    [(qbf k).Structure B] (e : A ≃[qbf k] B) :
    altQuant A k (fun νs => QbfMatrix cnf νs) start ↔
      altQuant B k (fun νs => QbfMatrix cnf νs) start :=
  (DescriptiveComplexity.QbfProblem k start cnf).iso_invariant e

/--
---
conclusion: Lax564036.QuantifiedBooleanFormulasInvariance.qbfProblem_iff
---
The property is invariant, by this submission's statement.
-/
theorem qbfProblem_iff (k : ℕ) (start cnf : Bool) (A : Type) [(qbf k).Structure A] :
    QbfProblem k start cnf A ↔ altQuant A k (fun νs => QbfMatrix cnf νs) start :=
  ofPred_iff (P := fun A _ => altQuant A k (fun νs => QbfMatrix cnf νs) start)
    (Lax564036.QuantifiedBooleanFormulasInvariance.qbfTrue_iso k start cnf) A

/-- The library's QBF problem and the concept's have the same instances. -/
theorem qbfProblem_agree (k : ℕ) (start cnf : Bool) (A : Type) [(qbf k).Structure A] :
    DescriptiveComplexity.QbfProblem k start cnf A ↔ QbfProblem k start cnf A :=
  (qbfProblem_iff k start cnf A).symm

/--
---
conclusion: Lax564036.AlternatingMachineInvariance.atmAccepts_iso
---
The invariance the library proves when it bundles the problem, from the
agreement of the machines of two isomorphic instances.
-/
theorem atmAccepts_iso (k : ℕ) (start : Bool) {A B : Type} [(turingAlt k).Structure A]
    [(turingAlt k).Structure B] (e : A ≃[turingAlt k] B) :
    ATMAccepts k start A ↔ ATMAccepts k start B :=
  (DescriptiveComplexity.ATMAccept k start).iso_invariant e

/--
---
conclusion: Lax564036.AlternatingMachineInvariance.atmAccept_iff
---
The property is invariant, by this submission's statement.
-/
theorem atmAccept_iff (k : ℕ) (start : Bool) (A : Type) [(turingAlt k).Structure A] :
    ATMAccept k start A ↔ ATMAccepts k start A :=
  ofPred_iff (P := fun A _ => ATMAccepts k start A)
    (Lax564036.AlternatingMachineInvariance.atmAccepts_iso k start) A

/-- The library's alternating acceptance and the concept's have the same instances. -/
theorem atmAccept_agree (k : ℕ) (start : Bool) (A : Type) [(turingAlt k).Structure A] :
    DescriptiveComplexity.ATMAccept k start A ↔ ATMAccept k start A :=
  (atmAccept_iff k start A).symm

/-! ### The levels -/

/--
---
conclusion: Lax564036.HierarchyDuality.mem_piP_iff
---
At level zero both sides are SO-Horn definability of the complement; above,
the library's duality of the two kinds of second-order sentences.
-/
theorem mem_piP_iff (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    (PiP k).Mem P ↔ (SigmaP k).Mem (DecisionProblem.compl P) := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact DescriptiveComplexity.mem_piP_iff (k + 1) P

/--
---
conclusion: Lax564036.HierarchyDuality.compl_mem_coNP_iff
---
The library's theorem, the duality at level one.
-/
theorem compl_mem_coNP_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    coNP.Mem (DecisionProblem.compl P) ↔ NP.Mem P :=
  DescriptiveComplexity.compl_mem_coNP_iff P

/--
---
conclusion: Lax564036.HierarchyInclusions.sigmaP_subset_sigmaP_succ
---
The library's padding of a definition with a vacuous quantifier block.
-/
theorem sigmaP_subset_sigmaP_succ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : (SigmaP (k + 1)).Mem P) : (SigmaP (k + 2)).Mem P :=
  DescriptiveComplexity.sigmaP_subset_sigmaP_succ k h

/--
---
conclusion: Lax564036.HierarchyInclusions.sigmaP_subset_piP_succ
---
The library's padding of a definition with a vacuous quantifier block.
-/
theorem sigmaP_subset_piP_succ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : (SigmaP (k + 1)).Mem P) : (PiP (k + 2)).Mem P :=
  DescriptiveComplexity.sigmaP_subset_piP_succ k h

/--
---
conclusion: Lax564036.HierarchyInclusions.piP_subset_sigmaP_succ
---
The library's padding of a definition with a vacuous quantifier block.
-/
theorem piP_subset_sigmaP_succ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : (PiP (k + 1)).Mem P) : (SigmaP (k + 2)).Mem P :=
  DescriptiveComplexity.piP_subset_sigmaP_succ k h

/--
---
conclusion: Lax564036.HierarchyInclusions.piP_subset_piP_succ
---
The library's padding of a definition with a vacuous quantifier block.
-/
theorem piP_subset_piP_succ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : (PiP (k + 1)).Mem P) : (PiP (k + 2)).Mem P :=
  DescriptiveComplexity.piP_subset_piP_succ k h

/--
---
conclusion: Lax564036.HierarchyInclusions.sigmaP_mono
---
The library's monotonicity, the levels agreeing with the library's.
-/
theorem sigmaP_mono {j k : ℕ} (hjk : j ≤ k) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : (SigmaP j).Mem P) : (SigmaP k).Mem P :=
  (sigma_mem_agree k P).mpr (DescriptiveComplexity.sigmaP_mono hjk ((sigma_mem_agree j P).mp h))

/--
---
conclusion: Lax564036.HierarchyInclusions.piP_mono
---
The library's monotonicity, the levels agreeing with the library's.
-/
theorem piP_mono {j k : ℕ} (hjk : j ≤ k) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (h : (PiP j).Mem P) : (PiP k).Mem P :=
  (pi_mem_agree k P).mpr (DescriptiveComplexity.piP_mono hjk ((pi_mem_agree j P).mp h))

/--
---
conclusion: Lax564036.HierarchyInclusions.sigmaP_subset_PH
---
By the definition of PH as the union of the levels.
-/
theorem sigmaP_subset_PH (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : (SigmaP k).Mem P) : PH.Mem P :=
  ⟨k, h⟩

/--
---
conclusion: Lax564036.HierarchyInclusions.piP_subset_PH
---
The library's inclusions, at level zero and above.
-/
theorem piP_subset_PH (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : (PiP k).Mem P) : PH.Mem P := by
  cases k with
  | zero => exact ph_of_lib (DescriptiveComplexity.piP_zero_subset_PH h)
  | succ k => exact ph_of_lib (DescriptiveComplexity.piP_subset_PH k h)

/--
---
conclusion: Lax564036.PolynomialTimeInHierarchy.PTIME_subset_coNP
---
The library's inclusion.
-/
theorem PTIME_subset_coNP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PTIME.Mem P) :
    coNP.Mem P :=
  DescriptiveComplexity.PTIME_subset_coNP h

/--
---
conclusion: Lax564036.PolynomialTimeInHierarchy.PTIME_subset_sigmaP
---
The library's inclusion, the levels agreeing with the library's.
-/
theorem PTIME_subset_sigmaP (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PTIME.Mem P) : (SigmaP k).Mem P :=
  (sigma_mem_agree k P).mpr (DescriptiveComplexity.PTIME_subset_sigmaP k h)

/--
---
conclusion: Lax564036.PolynomialTimeInHierarchy.piP_zero_eq
---
The two classes of level zero are coPTIME and PTIME, equal by a statement of
the submission on polynomial time.
-/
theorem piP_zero_eq : PiP 0 = SigmaP 0 :=
  Lax535992.PTIMEEqCoPTIME.PTIME_eq_coPTIME.symm

/-! ### Closure laws and DP -/

/--
---
conclusion: Lax564036.CoNPClosure.coNP_mem_of_foReduction
---
The library's closure of universal second-order definability under first-order reductions.
-/
theorem coNP_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : coNP.Mem Q) :
    coNP.Mem P :=
  DescriptiveComplexity.coNP.mem_of_foReduction f h

/--
---
conclusion: Lax564036.CoNPClosure.coNP_mem_of_orderedReduction
---
The library's closure of universal second-order definability under ordered first-order
reductions.
-/
theorem coNP_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : coNP.Mem Q) : coNP.Mem P :=
  DescriptiveComplexity.coNP.mem_of_orderedReduction f h

/--
---
conclusion: Lax564036.CoNPClosure.coNP_mem_congr_finite
---
The definability notion reads a problem on finite structures only.
-/
theorem coNP_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : coNP.Mem P ↔ coNP.Mem Q :=
  DescriptiveComplexity.coNP.mem_congr_finite h

/--
---
conclusion: Lax564036.DPClosure.DP_mem_of_foReduction
---
The library's closure of DP-definability under first-order reductions.
-/
theorem DP_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : DP.Mem Q) :
    DP.Mem P :=
  DescriptiveComplexity.DPDefinable.of_foReduction f h

/--
---
conclusion: Lax564036.DPClosure.DP_mem_of_orderedReduction
---
The library's closure of DP-definability under ordered first-order
reductions.
-/
theorem DP_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : DP.Mem Q) : DP.Mem P :=
  DescriptiveComplexity.DPDefinable.of_orderedReduction f h

/--
---
conclusion: Lax564036.DPClosure.DP_mem_congr_finite
---
The definability notion reads a problem on finite structures only.
-/
theorem DP_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : DP.Mem P ↔ DP.Mem Q :=
  DescriptiveComplexity.dpDefinable_congr h

/--
---
conclusion: Lax564036.DPInclusions.NP_subset_DP
---
The library's inclusion, a trivial coNP half.
-/
theorem NP_subset_DP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : NP.Mem P) :
    DP.Mem P :=
  DescriptiveComplexity.NP_subset_DP h

/--
---
conclusion: Lax564036.DPInclusions.coNP_subset_DP
---
The library's inclusion, a trivial NP half.
-/
theorem coNP_subset_DP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : coNP.Mem P) :
    DP.Mem P :=
  DescriptiveComplexity.coNP_subset_DP h

/--
---
conclusion: Lax564036.DPInclusions.DP_subset_sigmaP_two
---
The library's merge of the two kernels, existential block first.
-/
theorem DP_subset_sigmaP_two {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : DP.Mem P) :
    (SigmaP 2).Mem P :=
  DescriptiveComplexity.DP_subset_sigmaP_two h

/--
---
conclusion: Lax564036.DPInclusions.DP_subset_piP_two
---
The library's merge of the two kernels, universal block first.
-/
theorem DP_subset_piP_two {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : DP.Mem P) :
    (PiP 2).Mem P :=
  DescriptiveComplexity.DP_subset_piP_two h

/-! ### Complete problems -/

/--
---
conclusion: Lax564036.TautCoNPComplete.taut_coNP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem taut_coNP_complete : coNP.Complete TAUT := by
  have h := complete_congr DescriptiveComplexity.coNP (fun A _ _ => taut_agree A)
    DescriptiveComplexity.TAUT_coNP_complete
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.ThreeDnfTautCoNPComplete.threeDnfTaut_coNP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem threeDnfTaut_coNP_complete : coNP.Complete ThreeDnfTAUT := by
  have h := complete_congr DescriptiveComplexity.coNP (fun A _ _ => threeDnfTaut_agree A)
    DescriptiveComplexity.ThreeDnfTAUT_coNP_complete
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.ThreeDnfTautCoNPComplete.threeUnsat_coNP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem threeUnsat_coNP_complete : coNP.Complete ThreeUNSAT := by
  have h := complete_congr DescriptiveComplexity.coNP (fun A _ _ => threeUnsat_agree A)
    DescriptiveComplexity.ThreeUNSAT_coNP_complete
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.SatUnsatDPComplete.satUnsat_DP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem satUnsat_DP_complete : DP.Complete SATUNSAT := by
  have h := complete_congr DescriptiveComplexity.DP (fun A _ _ => satUnsat_agree A)
    DescriptiveComplexity.SATUNSAT_DP_complete
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.QbfComplete.qbf_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem qbf_complete (k : ℕ) : (SigmaP (k + 1)).Complete (QBF (k + 1)) := by
  have h := complete_congr (DescriptiveComplexity.SigmaP (k + 1))
    (fun A _ _ => qbfProblem_agree (k + 1) true ((k + 1) % 2 == 1) A)
    (DescriptiveComplexity.QBF_complete k)
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.QbfComplete.qbfPi_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem qbfPi_complete (k : ℕ) : (PiP (k + 1)).Complete (QBFPi (k + 1)) := by
  have h := complete_congr (DescriptiveComplexity.PiP (k + 1))
    (fun A _ _ => qbfProblem_agree (k + 1) false ((k + 1) % 2 == 0) A)
    (DescriptiveComplexity.QBFPi_complete k)
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.QbfComplete.qbf_one_NP_complete
---
The case of one block of this submission's general statement.
-/
theorem qbf_one_NP_complete : NP.Complete (QBF 1) :=
  Lax564036.QbfComplete.qbf_complete 0

/--
---
conclusion: Lax564036.QbfComplete.qbfPi_one_coNP_complete
---
The case of one block of this submission's general statement.
-/
theorem qbfPi_one_coNP_complete : coNP.Complete (QBFPi 1) :=
  Lax564036.QbfComplete.qbfPi_complete 0

/--
---
conclusion: Lax564036.AlternatingMachineComplete.atmAccept_sigmaP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem atmAccept_sigmaP_complete (k : ℕ) : (SigmaP (k + 1)).Complete (ATMAccept (k + 1) true) := by
  have h := complete_congr (DescriptiveComplexity.SigmaP (k + 1))
    (fun A _ _ => atmAccept_agree (k + 1) true A)
    (DescriptiveComplexity.atmAccept_sigmaP_complete k)
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.AlternatingMachineComplete.atmAccept_piP_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem atmAccept_piP_complete (k : ℕ) : (PiP (k + 1)).Complete (ATMAccept (k + 1) false) := by
  have h := complete_congr (DescriptiveComplexity.PiP (k + 1))
    (fun A _ _ => atmAccept_agree (k + 1) false A)
    (DescriptiveComplexity.atmAccept_piP_complete k)
  exact ⟨h.1, h.2⟩

/--
---
conclusion: Lax564036.AlternatingMachineComplete.mem_sigmaP_iff_le_atmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_sigmaP_iff_le_atmAccept {L : Language.{0, 0}} [L.IsRelational] (k : ℕ)
    (P : DecisionProblem L) :
    (SigmaP (k + 1)).Mem P ↔ Nonempty (OrderedFOReduction P (ATMAccept (k + 1) true)) :=
  (DescriptiveComplexity.mem_sigmaP_iff_le_atmAccept k P).trans
    ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) (atmAccept_agree (k + 1) true)),
      Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl)
        fun A _ => (atmAccept_agree (k + 1) true A).symm)⟩

/--
---
conclusion: Lax564036.AlternatingMachineComplete.mem_piP_iff_le_atmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_piP_iff_le_atmAccept {L : Language.{0, 0}} [L.IsRelational] (k : ℕ)
    (P : DecisionProblem L) :
    (PiP (k + 1)).Mem P ↔ Nonempty (OrderedFOReduction P (ATMAccept (k + 1) false)) :=
  (DescriptiveComplexity.mem_piP_iff_le_atmAccept k P).trans
    ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) (atmAccept_agree (k + 1) false)),
      Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl)
        fun A _ => (atmAccept_agree (k + 1) false A).symm)⟩

/--
---
conclusion: Lax564036.AlternatingMachineComplete.atmAccept_one_NP_complete
---
The case of one block of this submission's general statement.
-/
theorem atmAccept_one_NP_complete : NP.Complete (ATMAccept 1 true) :=
  Lax564036.AlternatingMachineComplete.atmAccept_sigmaP_complete 0

/--
---
conclusion: Lax564036.AlternatingMachineComplete.atmAccept_one_coNP_complete
---
The case of one block of this submission's general statement.
-/
theorem atmAccept_one_coNP_complete : coNP.Complete (ATMAccept 1 false) :=
  Lax564036.AlternatingMachineComplete.atmAccept_piP_complete 0

end Lax564036Proofs.Bridge
