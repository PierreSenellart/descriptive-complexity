import Lax366625.SharpSatValue
import Lax366625.CountingRunsValue
import Lax366625.NumbersValue
import Lax366625.SharpPClosure
import Lax366625.FPClosure
import Lax366625.SharpSatComplete
import Lax366625.CountingRunsComplete
import Lax366625.SharpPAndNP
import Lax366625.SharpPAsQuantitativeLogic
import Lax366625.FPByDigits
import Lax366625.FPComplete
import Lax366625.FPAndPTIME
import Lax366625Proofs.DescriptiveComplexity.Counting.Class
import Lax366625Proofs.DescriptiveComplexity.Counting.FP
import Lax366625Proofs.DescriptiveComplexity.Counting.QSOSharpP
import Lax366625Proofs.DescriptiveComplexity.Counting.Quantitative
import Lax366625Proofs.DescriptiveComplexity.Counting.RelClosure
import Lax366625Proofs.DescriptiveComplexity.Counting.Relativized
import Lax366625Proofs.DescriptiveComplexity.Counting.SharpP
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Defs
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Number
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.Counting
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.CountingHardness
import Lax366625Proofs.DescriptiveComplexity.Problems.MachineNumber
import Lax366625Proofs.DescriptiveComplexity.Problems.MachineNumber.Defs
import Lax366625Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Lax366625Proofs.DescriptiveComplexity.Problems.Sat.CountingHardness

/-!
# The counting statements, from the library's theorems

The counting problems, their reductions and the logics are restated by the
concepts, and the library's theorems about them are the claims themselves. The
problems are bundled in the concepts from the numbers they are defined by;
statements about them are transported along the agreement with the library's
problems, which the invariance of each number gives. The classes are built in
the concepts from their membership predicates, with the same hardness as the
library's.
-/

namespace Lax366625Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- For an invariant number, the problem it gives takes that number. -/
theorem ofFun_eq {L : Language.{0, 0}} [L.IsRelational] {f : ∀ (A : Type) [L.Structure A], ℕ}
    (hf : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → f A = f B)
    (A : Type) [L.Structure A] : CountingProblem.ofFun f A = f A := by
  show sInf _ = _
  have hs : {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n} =
      {f A} := by
    ext n
    constructor
    · rintro ⟨B, i, g, rfl⟩
      exact hf g
    · intro h
      exact ⟨A, inferInstance, Language.Equiv.refl _ _, h.symm⟩
  rw [hs, csInf_singleton]

/--
---
conclusion: Lax366625.SharpSatValue.sharpSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSat_count_iso {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B) :
    Nat.card {ν : A → Prop // SatModel A ν} = Nat.card {ν : B → Prop // SatModel B ν} :=
  (DescriptiveComplexity.SharpSAT).iso_invariant e

/--
---
conclusion: Lax366625.SharpSatValue.sharpSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSat_eq (A : Type) [sat.Structure A] : SharpSAT A = Nat.card
    {ν : A → Prop // SatModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card {ν : A →
    Prop // SatModel A ν}) Lax366625.SharpSatValue.sharpSat_count_iso A

/-- The library's problem and the concept's have the same values. -/
theorem sharpSat_agree (A : Type) [sat.Structure A] :
    DescriptiveComplexity.SharpSAT A = SharpSAT A :=
  (sharpSat_eq A).symm

/--
---
conclusion: Lax366625.CountingRunsValue.sharpNtmAccept_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpNtmAccept_count_iso {A B : Type} [turing.Structure A] [turing.Structure B]
    (e : A ≃[turing] B) :
    Nat.card {conf : A → Config A // (tmData A).WellFormed ∧ TMData.IsHaltWalk
    (tmData A) conf} = Nat.card {conf : B → Config B // (tmData B).WellFormed ∧ TMData.IsHaltWalk
    (tmData B) conf} :=
  (DescriptiveComplexity.SharpNTMAccept).iso_invariant e

/--
---
conclusion: Lax366625.CountingRunsValue.sharpNtmAccept_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpNtmAccept_eq (A : Type) [turing.Structure A] : SharpNTMAccept A = Nat.card
    {conf : A → Config A // (tmData A).WellFormed ∧ TMData.IsHaltWalk (tmData A) conf} :=
  ofFun_eq (f := fun A _ => Nat.card {conf : A → Config A //
    (tmData A).WellFormed ∧ TMData.IsHaltWalk
    (tmData A) conf}) Lax366625.CountingRunsValue.sharpNtmAccept_count_iso A

/-- The library's problem and the concept's have the same values. -/
theorem sharpNtmAccept_agree (A : Type) [turing.Structure A] :
    DescriptiveComplexity.SharpNTMAccept A = SharpNTMAccept A :=
  (sharpNtmAccept_eq A).symm

/--
---
conclusion: Lax366625.NumbersValue.circuitNumber_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem circuitNumber_count_iso {A B : Type} [numCircuit.Structure A] [numCircuit.Structure B]
    (e : A ≃[numCircuit] B) :
    circuitNumber A = circuitNumber B :=
  (DescriptiveComplexity.CircuitNumber).iso_invariant e

/--
---
conclusion: Lax366625.NumbersValue.circuitNumber_eq
---
The number is invariant, by this submission's statement.
-/
theorem circuitNumber_eq (A : Type) [numCircuit.Structure A] : CircuitNumber A = circuitNumber A :=
  ofFun_eq (f := fun A _ => circuitNumber A) Lax366625.NumbersValue.circuitNumber_count_iso A

/-- The library's problem and the concept's have the same values. -/
theorem circuitNumber_agree (A : Type) [numCircuit.Structure A] :
    DescriptiveComplexity.CircuitNumber A = CircuitNumber A :=
  (circuitNumber_eq A).symm

/--
---
conclusion: Lax366625.NumbersValue.hornNumber_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem hornNumber_count_iso {A B : Type} [satOut.Structure A] [satOut.Structure B]
    (e : A ≃[satOut] B) :
    hornNumber A = hornNumber B :=
  (DescriptiveComplexity.HornNumber).iso_invariant e

/--
---
conclusion: Lax366625.NumbersValue.hornNumber_eq
---
The number is invariant, by this submission's statement.
-/
theorem hornNumber_eq (A : Type) [satOut.Structure A] : HornNumber A = hornNumber A :=
  ofFun_eq (f := fun A _ => hornNumber A) Lax366625.NumbersValue.hornNumber_count_iso A

/-- The library's problem and the concept's have the same values. -/
theorem hornNumber_agree (A : Type) [satOut.Structure A] :
    DescriptiveComplexity.HornNumber A = HornNumber A :=
  (hornNumber_eq A).symm

/--
---
conclusion: Lax366625.NumbersValue.dtmNumber_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem dtmNumber_count_iso {A B : Type} [turingOut.Structure A] [turingOut.Structure B]
    (e : A ≃[turingOut] B) :
    machineNumber A = machineNumber B :=
  (DescriptiveComplexity.DTMNumber).iso_invariant e

/--
---
conclusion: Lax366625.NumbersValue.dtmNumber_eq
---
The number is invariant, by this submission's statement.
-/
theorem dtmNumber_eq (A : Type) [turingOut.Structure A] : DTMNumber A = machineNumber A :=
  ofFun_eq (f := fun A _ => machineNumber A) Lax366625.NumbersValue.dtmNumber_count_iso A

/-- The library's problem and the concept's have the same values. -/
theorem dtmNumber_agree (A : Type) [turingOut.Structure A] :
    DescriptiveComplexity.DTMNumber A = DTMNumber A :=
  (dtmNumber_eq A).symm

/--
---
conclusion: Lax366625.SharpPClosure.SharpP_mem_of_orderedParsimonious
---
The library's pullback of the definition along the reduction.
-/
theorem SharpP_mem_of_orderedParsimonious {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} (f : OrderedParsimoniousReduction C D)
    (h : SharpP.Mem D) : SharpP.Mem C :=
  DescriptiveComplexity.SharpPDefinable.of_orderedParsimonious f h

/--
---
conclusion: Lax366625.SharpPClosure.SharpP_mem_of_relOrderedParsimonious
---
The library's pullback onto the definable domain.
-/
theorem SharpP_mem_of_relOrderedParsimonious {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} (f : RelOrderedParsimoniousReduction C D)
    (h : SharpP.Mem D) : SharpP.Mem C :=
  DescriptiveComplexity.SharpPDefinable.of_relOrderedParsimonious f h

/--
---
conclusion: Lax366625.SharpPClosure.SharpP_mem_congr_finite
---
The definition reads a problem on finite structures only.
-/
theorem SharpP_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) :
    SharpP.Mem C ↔ SharpP.Mem D :=
  DescriptiveComplexity.SharpP.mem_congr_finite h

/--
---
conclusion: Lax366625.FPClosure.FP_mem_of_orderedParsimonious
---
The library's pullback of the definition along the reduction.
-/
theorem FP_mem_of_orderedParsimonious {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} (f : OrderedParsimoniousReduction C D)
    (h : FP.Mem D) : FP.Mem C :=
  DescriptiveComplexity.FPDefinable.of_orderedParsimonious f h

/--
---
conclusion: Lax366625.FPClosure.FP_mem_of_relOrderedParsimonious
---
The library's pullback onto the definable domain.
-/
theorem FP_mem_of_relOrderedParsimonious {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} (f : RelOrderedParsimoniousReduction C D)
    (h : FP.Mem D) : FP.Mem C :=
  DescriptiveComplexity.mem_FP_of_relOrderedParsimonious f h

/--
---
conclusion: Lax366625.FPClosure.FP_mem_congr_finite
---
The definition reads a problem on finite structures only.
-/
theorem FP_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = D A) :
    FP.Mem C ↔ FP.Mem D :=
  DescriptiveComplexity.FP.mem_congr_finite h

/--
---
conclusion: Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem sharpSat_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpSAT :=
  let h := DescriptiveComplexity.sharpSat_sharpP_parsimoniousComplete
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ => sharpSat_agree A).mp h.1,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite
      fun A _ _ => sharpSat_agree A).mp h.2⟩

/--
---
conclusion: Lax366625.CountingRunsComplete.sharpNtmAccept_sharpP_parsimoniousComplete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem sharpNtmAccept_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpNTMAccept :=
  let h := DescriptiveComplexity.sharpNtmAccept_sharpP_parsimoniousComplete
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ => sharpNtmAccept_agree A).mp h.1,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite
      fun A _ _ => sharpNtmAccept_agree A).mp h.2⟩

/--
---
conclusion: Lax366625.CountingRunsComplete.mem_sharpP_iff_le_sharpNtmAccept
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_sharpP_iff_le_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) :
    SharpP.Mem C ↔ Nonempty (OrderedParsimoniousReduction C SharpNTMAccept) :=
  (DescriptiveComplexity.mem_sharpP_iff_le_sharpNtmAccept C).trans
    ⟨Nonempty.map (DescriptiveComplexity.OrderedParsimoniousReduction.congrTarget
        fun A _ _ => sharpNtmAccept_agree A),
      Nonempty.map (DescriptiveComplexity.OrderedParsimoniousReduction.congrTarget
        fun A _ _ => (sharpNtmAccept_agree A).symm)⟩

/--
---
conclusion: Lax366625.SharpPAndNP.mem_NP_iff_exists_sharpP_support
---
The library's theorem.
-/
theorem mem_NP_iff_exists_sharpP_support {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    NP.Mem P ↔ ∃ C : CountingProblem L, SharpP.Mem C ∧
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], C.support A ↔ P A :=
  DescriptiveComplexity.mem_NP_iff_exists_sharpP_support P

/--
---
conclusion: Lax366625.SharpPAndNP.NP_hard_support_of_sharpP_parsimoniousHard
---
The library's theorem.
-/
theorem NP_hard_support_of_sharpP_parsimoniousHard {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L}
    (h : SharpP.ParsimoniousHard C) : NP.Hard C.support :=
  DescriptiveComplexity.NP_hard_support_of_sharpP_parsimoniousHard h

/--
---
conclusion: Lax366625.SharpPAndNP.NP_subset_PTIME_of_sharpP_parsimoniousHard
---
The library's theorem.
-/
theorem NP_subset_PTIME_of_sharpP_parsimoniousHard {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L}
    (h : SharpP.ParsimoniousHard C) (hs : PTIME.Mem C.support)
    {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L') (hP : NP.Mem P) :
    PTIME.Mem P :=
  DescriptiveComplexity.NP_subset_PTIME_of_sharpP_parsimoniousHard h hs hP

/--
---
conclusion: Lax366625.SharpPAsQuantitativeLogic.mem_sharpP_iff_sqDefinable
---
The library's theorem.
-/
theorem mem_sharpP_iff_sqDefinable {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    SharpP.Mem C ↔ SQDefinable C :=
  DescriptiveComplexity.mem_sharpP_iff_sqDefinable C

/--
---
conclusion: Lax366625.FPByDigits.digitDefinable_iff_mem_FP
---
The library's theorem.
-/
theorem digitDefinable_iff_mem_FP {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    DigitDefinable C ↔ FP.Mem C :=
  DescriptiveComplexity.digitDefinable_iff_mem_FP C

/--
---
conclusion: Lax366625.FPByDigits.fpDefinable_of_qfo
---
The library's theorem.
-/
theorem fpDefinable_of_qfo {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L}
    (t : QTerm (L.sum Language.order) Empty)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], C A = t.value A) :
    FP.Mem C :=
  DescriptiveComplexity.fpDefinable_of_qfo t h

/--
---
conclusion: Lax366625.FPComplete.circuitNumber_FP_parsimoniousComplete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem circuitNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete CircuitNumber :=
  let h := DescriptiveComplexity.circuitNumber_FP_parsimoniousComplete
  ⟨(DescriptiveComplexity.FP.mem_congr_finite fun A _ _ => circuitNumber_agree A).mp h.1,
    (DescriptiveComplexity.FP.parsimoniousHard_congr_finite
      fun A _ _ => circuitNumber_agree A).mp h.2⟩

/--
---
conclusion: Lax366625.FPComplete.hornNumber_FP_parsimoniousComplete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem hornNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete HornNumber :=
  let h := DescriptiveComplexity.hornNumber_FP_parsimoniousComplete
  ⟨(DescriptiveComplexity.FP.mem_congr_finite fun A _ _ => hornNumber_agree A).mp h.1,
    (DescriptiveComplexity.FP.parsimoniousHard_congr_finite
      fun A _ _ => hornNumber_agree A).mp h.2⟩

/--
---
conclusion: Lax366625.FPComplete.dtmNumber_FP_parsimoniousComplete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem dtmNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete DTMNumber :=
  let h := DescriptiveComplexity.dtmNumber_FP_parsimoniousComplete
  ⟨(DescriptiveComplexity.FP.mem_congr_finite fun A _ _ => dtmNumber_agree A).mp h.1,
    (DescriptiveComplexity.FP.parsimoniousHard_congr_finite
      fun A _ _ => dtmNumber_agree A).mp h.2⟩

/--
---
conclusion: Lax366625.FPComplete.mem_FP_iff_le_dtmNumber
---
The library's theorem, the reductions transported to the concept's problem
along the agreement.
-/
theorem mem_FP_iff_le_dtmNumber {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    FP.Mem C ↔ Nonempty (OrderedParsimoniousReduction C DTMNumber) :=
  (DescriptiveComplexity.mem_FP_iff_le_dtmNumber C).trans
    ⟨Nonempty.map (DescriptiveComplexity.OrderedParsimoniousReduction.congrTarget
        fun A _ _ => dtmNumber_agree A),
      Nonempty.map (DescriptiveComplexity.OrderedParsimoniousReduction.congrTarget
        fun A _ _ => (dtmNumber_agree A).symm)⟩

/--
---
conclusion: Lax366625.FPAndPTIME.support_mem_PTIME_of_mem_FP
---
The library's theorem.
-/
theorem support_mem_PTIME_of_mem_FP {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L}
    (h : FP.Mem C) : PTIME.Mem C.support :=
  DescriptiveComplexity.support_mem_PTIME_of_mem_FP h

/--
---
conclusion: Lax366625.FPAndPTIME.NP_subset_PTIME_of_mem_FP_of_parsimoniousHard
---
The support is in PTIME, by this submission's statement, and the support of a
parsimoniously #P-hard problem in PTIME gives NP ⊆ PTIME, by this
submission's statement.
-/
theorem NP_subset_PTIME_of_mem_FP_of_parsimoniousHard {L : Language.{0, 0}} [L.IsRelational]
    {C : CountingProblem L}
    (h : FP.Mem C) (hh : SharpP.ParsimoniousHard C)
    {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L') (hP : NP.Mem P) :
    PTIME.Mem P :=
  Lax366625.SharpPAndNP.NP_subset_PTIME_of_sharpP_parsimoniousHard hh
    (Lax366625.FPAndPTIME.support_mem_PTIME_of_mem_FP h) P hP

end Lax366625Proofs.Bridge
