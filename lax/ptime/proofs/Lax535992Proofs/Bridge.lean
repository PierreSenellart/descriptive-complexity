import Lax904597.NPClass
import Lax485149.LSubsetNL
import Lax535992.HornSatInvariance
import Lax535992.CircuitValueInvariance
import Lax535992.GameInvariance
import Lax535992.DeterministicMachineInvariance
import Lax535992.PTIMEClosure
import Lax535992.HornIsLeastFixedPoint
import Lax535992.ImmermanVardi
import Lax535992.LeastFixedPointComplement
import Lax535992.PTIMEEqCoPTIME
import Lax535992.InflationaryIsLeastFixedPoint
import Lax535992.HornSatPTIMEComplete
import Lax535992.CircuitValuePTIMEComplete
import Lax535992.GamePTIMEComplete
import Lax535992.DeterministicMachinePTIMEComplete
import Lax535992.PTIMESubsetNP
import Lax535992.NLSubsetPTIME
import Lax535992Proofs.DescriptiveComplexity.FixedPoint
import Lax535992Proofs.DescriptiveComplexity.FixedPointHorn
import Lax535992Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax535992Proofs.DescriptiveComplexity.FixedPointInflationaryLFP
import Lax535992Proofs.DescriptiveComplexity.FixedPointReductionClosure
import Lax535992Proofs.DescriptiveComplexity.Problems.Cvp
import Lax535992Proofs.DescriptiveComplexity.Problems.Game.Hardness
import Lax535992Proofs.DescriptiveComplexity.Problems.HornSat
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine
import Lax535992Proofs.DescriptiveComplexity.Problems.TwoSat
import Lax535992Proofs.DescriptiveComplexity.SecondOrderHornPull

/-!
# The PTIME statements, from the library's theorems

Each claim is proved from the library's theorem of the same name. The logics
and the properties defining the problems are restated by the concepts, so the
library's theorems about them are the claims themselves; the bundled problems
are transported along the agreement between the library's problem and the
concept's, which the invariance of the property gives, and the classes along
the agreement of their membership predicates. Where the library composes its
own results, the bridges assume the submission's statements instead: the
Immerman–Vardi theorem from the equivalence of the Horn fragment and FO(LFP),
the equality of PTIME and coPTIME from the closure of the Horn fragment under
complement, the capture by FO(≤, IFP) from the two translations, and the
inclusion of L from that of NL.
-/

namespace Lax535992Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

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
conclusion: Lax535992.HornSatInvariance.hornSatisfiable_iso
---
The library's invariance theorem.
-/
theorem hornSatisfiable_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    HornSatisfiable A ↔ HornSatisfiable B :=
  DescriptiveComplexity.hornSatisfiable_iso e

/--
---
conclusion: Lax535992.HornSatInvariance.hornSat_iff
---
The property is invariant, by this submission's statement.
-/
theorem hornSat_iff (A : Type) [sat.Structure A] : HORNSAT A ↔ HornSatisfiable A :=
  ofPred_iff Lax535992.HornSatInvariance.hornSatisfiable_iso A

/-- The library's HORN-SAT and the concept's have the same instances. -/
theorem hornSat_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.HORNSAT A ↔ HORNSAT A :=
  (hornSat_iff A).symm

/--
---
conclusion: Lax535992.CircuitValueInvariance.circuitAccepts_iso
---
The library's invariance theorem.
-/
theorem circuitAccepts_iso {A B : Type} [circuit.Structure A] [circuit.Structure B]
    (e : A ≃[circuit] B) :
    CircuitAccepts A ↔ CircuitAccepts B :=
  DescriptiveComplexity.circuitAccepts_iso e

/--
---
conclusion: Lax535992.CircuitValueInvariance.cvp_iff
---
The property is invariant, by this submission's statement.
-/
theorem cvp_iff (A : Type) [circuit.Structure A] : CVP A ↔ CircuitAccepts A :=
  ofPred_iff Lax535992.CircuitValueInvariance.circuitAccepts_iso A

/-- The library's CVP and the concept's have the same instances. -/
theorem cvp_agree (A : Type) [circuit.Structure A] :
    DescriptiveComplexity.CVP A ↔ CVP A :=
  (cvp_iff A).symm

/--
---
conclusion: Lax535992.GameInvariance.gameWon_iso
---
The library's invariance theorem.
-/
theorem gameWon_iso {A B : Type} [andOrGraph.Structure A] [andOrGraph.Structure B]
    (e : A ≃[andOrGraph] B) :
    GameWon A ↔ GameWon B :=
  DescriptiveComplexity.gameWon_iso e

/--
---
conclusion: Lax535992.GameInvariance.game_iff
---
The property is invariant, by this submission's statement.
-/
theorem game_iff (A : Type) [andOrGraph.Structure A] : GAME A ↔ GameWon A :=
  ofPred_iff Lax535992.GameInvariance.gameWon_iso A

/-- The library's GAME and the concept's have the same instances. -/
theorem game_agree (A : Type) [andOrGraph.Structure A] :
    DescriptiveComplexity.GAME A ↔ GAME A :=
  (game_iff A).symm

/--
---
conclusion: Lax535992.DeterministicMachineInvariance.dtmAccepts_iso
---
The library's agreement of the machines of two isomorphic instances, which
preserves well-formedness, determinism and acceptance.
-/
theorem dtmAccepts_iso {A B : Type} [turing.Structure A] [turing.Structure B] (e : A ≃[turing] B) :
    ((tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts) ↔
      ((tmData B).WellFormed ∧ TMData.Deterministic (tmData B) ∧ (tmData B).Accepts) :=
  have h := DescriptiveComplexity.agree_of_equiv e
  (and_congr h.wellFormed (and_congr h.deterministic h.accepts)).symm

/--
---
conclusion: Lax535992.DeterministicMachineInvariance.dtmAccept_iff
---
The property is invariant, by this submission's statement.
-/
theorem dtmAccept_iff (A : Type) [turing.Structure A] :
    DTMAccept A ↔ ((tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts) :=
  ofPred_iff (P := fun A _ =>
      ((tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts))
    Lax535992.DeterministicMachineInvariance.dtmAccepts_iso A

/-- The library's deterministic machine acceptance and the concept's have the
same instances. -/
theorem dtmAccept_agree (A : Type) [turing.Structure A] :
    DescriptiveComplexity.DTMAccept A ↔ DTMAccept A :=
  (dtmAccept_iff A).symm

/-! ### Closure laws -/

/--
---
conclusion: Lax535992.PTIMEClosure.PTIME_mem_of_foReduction
---
The library's closure of SO-Horn definability under first-order reductions.
-/
theorem PTIME_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : PTIME.Mem Q) :
    PTIME.Mem P :=
  DescriptiveComplexity.SigmaSOHornDefinable.of_foReduction f h

/--
---
conclusion: Lax535992.PTIMEClosure.PTIME_mem_of_orderedReduction
---
The library's closure of SO-Horn definability under ordered first-order
reductions.
-/
theorem PTIME_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q)
    (h : PTIME.Mem Q) : PTIME.Mem P :=
  DescriptiveComplexity.SigmaSOHornDefinable.of_orderedReduction f h

/--
---
conclusion: Lax535992.PTIMEClosure.PTIME_mem_of_relOrderedReduction
---
The library's closure of PTIME under relativized ordered reductions, through
FO(LFP).
-/
theorem PTIME_mem_of_relOrderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : RelOrderedFOReduction P Q)
    (h : PTIME.Mem Q) : PTIME.Mem P :=
  DescriptiveComplexity.mem_PTIME_of_relOrderedReduction f h

/--
---
conclusion: Lax535992.PTIMEClosure.PTIME_mem_congr_finite
---
SO-Horn definability reads a problem on finite structures only.
-/
theorem PTIME_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : PTIME.Mem P ↔ PTIME.Mem Q :=
  DescriptiveComplexity.sigmaSOHornDefinable_congr h

/-! ### The logics -/

/--
---
conclusion: Lax535992.HornIsLeastFixedPoint.sigmaSOHornDefinable_lfpDefinable
---
The library's reading of a Horn program as a rule system with an output
sentence.
-/
theorem sigmaSOHornDefinable_lfpDefinable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L}
    (h : SigmaSOHornDefinable P) : LFPDefinable P :=
  DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable h

/--
---
conclusion: Lax535992.HornIsLeastFixedPoint.lfpDefinable_sigmaSOHornDefinable
---
The library's compilation of an FO(LFP) definition into a Horn program, stage
by stage along the order.
-/
theorem lfpDefinable_sigmaSOHornDefinable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L}
    (h : LFPDefinable P) : SigmaSOHornDefinable P :=
  DescriptiveComplexity.LFPDefinable.sigmaSOHornDefinable h

/--
---
conclusion: Lax535992.ImmermanVardi.lfpDefinable_iff_mem_PTIME
---
The two translations between FO(LFP) and the Horn fragment, by this
submission's statements; membership in PTIME is SO-Horn definability.
-/
theorem lfpDefinable_iff_mem_PTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    LFPDefinable P ↔ PTIME.Mem P :=
  ⟨Lax535992.HornIsLeastFixedPoint.lfpDefinable_sigmaSOHornDefinable,
    Lax535992.HornIsLeastFixedPoint.sigmaSOHornDefinable_lfpDefinable⟩

/--
---
conclusion: Lax535992.LeastFixedPointComplement.lfpDefinable_compl
---
The library's negation of the output sentence.
-/
theorem lfpDefinable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : LFPDefinable P) : LFPDefinable (DecisionProblem.compl P) :=
  DescriptiveComplexity.LFPDefinable.compl h

/--
---
conclusion: Lax535992.PTIMEEqCoPTIME.sigmaSOHornDefinable_compl
---
Through FO(LFP), by this submission's statements: translate, complement,
translate back.
-/
theorem sigmaSOHornDefinable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSOHornDefinable P) : SigmaSOHornDefinable (DecisionProblem.compl P) :=
  Lax535992.HornIsLeastFixedPoint.lfpDefinable_sigmaSOHornDefinable
    (Lax535992.LeastFixedPointComplement.lfpDefinable_compl
      (Lax535992.HornIsLeastFixedPoint.sigmaSOHornDefinable_lfpDefinable h))

/--
---
conclusion: Lax535992.PTIMEEqCoPTIME.PTIME_eq_coPTIME
---
The Horn fragment is closed under complement, by this submission's statement,
and a problem has the finite instances of its double complement; so the two
classes have the same members, and hardness is read off membership.
-/
theorem PTIME_eq_coPTIME : PTIME = coPTIME :=
  ofMem_congr fun P =>
    ⟨Lax535992.PTIMEEqCoPTIME.sigmaSOHornDefinable_compl, fun h =>
      (Lax535992.PTIMEClosure.PTIME_mem_congr_finite
        (P := DecisionProblem.compl (DecisionProblem.compl P)) (Q := P)
        fun _ _ _ => not_not).mp
        (Lax535992.PTIMEEqCoPTIME.sigmaSOHornDefinable_compl h)⟩

/--
---
conclusion: Lax535992.InflationaryIsLeastFixedPoint.lfpDefinable_ifpDefinable
---
The library's reading of a rule system as one simultaneous step.
-/
theorem lfpDefinable_ifpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : LFPDefinable P) : IFPDefinable P :=
  DescriptiveComplexity.LFPDefinable.ifpDefinable h

/--
---
conclusion: Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_lfpDefinable
---
The library's compilation of an inflationary induction into FO(LFP), walking
the stages with a positive evaluator of truth and falsity.
-/
theorem ifpDefinable_lfpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinable P) : LFPDefinable P :=
  DescriptiveComplexity.IFPDefinable.lfpDefinable h

/--
---
conclusion: Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_iff_mem_PTIME
---
The two translations between FO(≤, IFP) and FO(LFP), and the Immerman–Vardi
theorem, by this submission's statements.
-/
theorem ifpDefinable_iff_mem_PTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    IFPDefinable P ↔ PTIME.Mem P :=
  Iff.trans
    ⟨Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_lfpDefinable,
      Lax535992.InflationaryIsLeastFixedPoint.lfpDefinable_ifpDefinable⟩
    (Lax535992.ImmermanVardi.lfpDefinable_iff_mem_PTIME P)

/-! ### Complete problems -/

/--
---
conclusion: Lax535992.HornSatPTIMEComplete.hornSat_PTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem hornSat_PTIME_complete : PTIME.Complete HORNSAT :=
  ⟨(Lax535992.PTIMEClosure.PTIME_mem_congr_finite fun A _ _ => hornSat_agree A).mp
      DescriptiveComplexity.HORNSAT_PTIME_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => hornSat_agree A)
      DescriptiveComplexity.HORNSAT_PTIME_complete.2⟩

/--
---
conclusion: Lax535992.CircuitValuePTIMEComplete.cvp_PTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem cvp_PTIME_complete : PTIME.Complete CVP :=
  ⟨(Lax535992.PTIMEClosure.PTIME_mem_congr_finite fun A _ _ => cvp_agree A).mp
      DescriptiveComplexity.CVP_PTIME_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => cvp_agree A)
      DescriptiveComplexity.CVP_PTIME_complete.2⟩

/--
---
conclusion: Lax535992.GamePTIMEComplete.game_PTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem game_PTIME_complete : PTIME.Complete GAME :=
  ⟨(Lax535992.PTIMEClosure.PTIME_mem_congr_finite fun A _ _ => game_agree A).mp
      DescriptiveComplexity.game_PTIME_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => game_agree A)
      DescriptiveComplexity.game_PTIME_complete.2⟩

/--
---
conclusion: Lax535992.DeterministicMachinePTIMEComplete.dtmAccept_PTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem dtmAccept_PTIME_complete : PTIME.Complete DTMAccept :=
  ⟨(Lax535992.PTIMEClosure.PTIME_mem_congr_finite fun A _ _ => dtmAccept_agree A).mp
      DescriptiveComplexity.dtmAccept_PTIME_complete.1,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => dtmAccept_agree A)
      DescriptiveComplexity.dtmAccept_PTIME_complete.2⟩

/--
---
conclusion: Lax535992.DeterministicMachinePTIMEComplete.mem_PTIME_iff_le_dtmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_PTIME_iff_le_dtmAccept {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    PTIME.Mem P ↔ Nonempty (OrderedFOReduction P DTMAccept) :=
  (DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept P).trans
    ⟨Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl) dtmAccept_agree),
      Nonempty.map (OrderedFOReduction.congr (fun _ _ => Iff.rfl)
        fun A _ => (dtmAccept_agree A).symm)⟩

/-! ### Inclusions -/

/--
---
conclusion: Lax535992.PTIMESubsetNP.PTIME_subset_NP
---
The library's inclusion, through HORN-SAT.
-/
theorem PTIME_subset_NP {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : PTIME.Mem P) :
    NP.Mem P :=
  DescriptiveComplexity.PTIME_subset_NP h

/--
---
conclusion: Lax535992.NLSubsetPTIME.NL_subset_PTIME
---
The library's inclusion, through 2SAT and its Horn program.
-/
theorem NL_subset_PTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : NL.Mem P) :
    PTIME.Mem P :=
  DescriptiveComplexity.NL_subset_PTIME h

/--
---
conclusion: Lax535992.NLSubsetPTIME.LOGSPACE_subset_PTIME
---
L is contained in NL, a statement of the submission on logarithmic space, and
NL in PTIME, by this submission's statement.
-/
theorem LOGSPACE_subset_PTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L)
    (h : LOGSPACE.Mem P) : PTIME.Mem P :=
  Lax535992.NLSubsetPTIME.NL_subset_PTIME P (Lax485149.LSubsetNL.LOGSPACE_subset_NL P h)

end Lax535992Proofs.Bridge
