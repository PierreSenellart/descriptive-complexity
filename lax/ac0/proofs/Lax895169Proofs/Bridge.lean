import Lax895169.ACZeroComplement
import Lax895169.FirstOrderInACZero
import Lax895169.ACZeroFinite
import Lax895169.ACZeroIsBitLogic
import Lax895169.ACZeroIsLogTime
import Lax895169.ACZeroInLogSpace
import Lax895169.ACZeroInPTIME
import Lax895169Proofs.DescriptiveComplexity.ArithmeticDefinable
import Lax895169Proofs.DescriptiveComplexity.ArithmeticFixedPoint
import Lax895169Proofs.DescriptiveComplexity.HeadEvalArith
import Lax895169Proofs.DescriptiveComplexity.LogTime.BitLogic
import Lax895169Proofs.DescriptiveComplexity.LogTime.Compile
import Lax895169Proofs.DescriptiveComplexity.LogTime.Simulate
import Lax895169Proofs.DescriptiveComplexity.LogTime.Translate

/-!
# The AC⁰ statements, from the library's theorems

The logics and the machine model are restated by the concepts, so each claim is
the library's theorem of the same name. The equivalence of AC⁰ definability and
logarithmic time is composed from this submission's statements, through the
bit-level logic, and membership in L from FO(DTC) definability.
-/

namespace Lax895169Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/--
---
conclusion: Lax895169.ACZeroComplement.ac0Definable_compl
---
The library's negation of the defining sentence.
-/
theorem ac0Definable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : AC0Definable (DecisionProblem.compl P) :=
  DescriptiveComplexity.AC0Definable.compl h

/--
---
conclusion: Lax895169.FirstOrderInACZero.foDefinable_ac0Definable
---
The library's transport of a sentence along the map of vocabularies.
-/
theorem foDefinable_ac0Definable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : FODefinable P) : AC0Definable P :=
  DescriptiveComplexity.FODefinable.ac0Definable h

/--
---
conclusion: Lax895169.ACZeroIsBitLogic.ac0Definable_bitDefinable
---
The library's translation, formula by formula, with multiplication defined
from BIT.
-/
theorem ac0Definable_bitDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : BitDefinable P :=
  DescriptiveComplexity.AC0Definable.bitDefinable h

/--
---
conclusion: Lax895169.ACZeroIsBitLogic.bitDefinable_ac0Definable
---
The library's translation, with the powers of two defined from addition and
multiplication.
-/
theorem bitDefinable_ac0Definable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : BitDefinable P) : AC0Definable P :=
  DescriptiveComplexity.BitDefinable.ac0Definable h

/--
---
conclusion: Lax895169.ACZeroIsLogTime.ltDecidable_bitDefinable
---
The library's sentence guessing the history of each sweep.
-/
theorem ltDecidable_bitDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : LTDecidable P) : BitDefinable P :=
  DescriptiveComplexity.LTDecidable.bitDefinable h

/--
---
conclusion: Lax895169.ACZeroIsLogTime.bitDefinable_ltDecidable
---
The library's compilation of a sentence into a machine, atom by atom.
-/
theorem bitDefinable_ltDecidable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : BitDefinable P) : LTDecidable P :=
  DescriptiveComplexity.BitDefinable.ltDecidable h

/--
---
conclusion: Lax895169.ACZeroIsLogTime.ac0Definable_iff_ltDecidable
---
Through the bit-level logic, by this submission's statements.
-/
theorem ac0Definable_iff_ltDecidable {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} :
    AC0Definable P ↔ LTDecidable P :=
  ⟨fun h => Lax895169.ACZeroIsLogTime.bitDefinable_ltDecidable
      (Lax895169.ACZeroIsBitLogic.ac0Definable_bitDefinable h),
    fun h => Lax895169.ACZeroIsBitLogic.bitDefinable_ac0Definable
      (Lax895169.ACZeroIsLogTime.ltDecidable_bitDefinable h)⟩

/--
---
conclusion: Lax895169.ACZeroInLogSpace.ac0Definable_dtcDefinable
---
The library's deterministic multihead evaluation of the sentence.
-/
theorem ac0Definable_dtcDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : DTCDefinable P :=
  DescriptiveComplexity.AC0Definable.dtcDefinable h

/--
---
conclusion: Lax895169.ACZeroInLogSpace.ac0Definable_mem_LOGSPACE
---
Membership in L is FO(DTC) definability, which this submission states.
-/
theorem ac0Definable_mem_LOGSPACE {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : LOGSPACE.Mem P :=
  Lax895169.ACZeroInLogSpace.ac0Definable_dtcDefinable h

/--
---
conclusion: Lax895169.ACZeroInLogSpace.ac0Definable_mem_NL
---
The library's inclusion, through L.
-/
theorem ac0Definable_mem_NL {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : NL.Mem P :=
  DescriptiveComplexity.ac0Definable_mem_NL h

/--
---
conclusion: Lax895169.ACZeroInPTIME.ac0Definable_ifpDefinable
---
The library's simultaneous induction defining the numeric predicates.
-/
theorem ac0Definable_ifpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : IFPDefinable P :=
  DescriptiveComplexity.AC0Definable.ifpDefinable h

/--
---
conclusion: Lax895169.ACZeroInPTIME.ac0Definable_lfpDefinable
---
The library's theorem, the inflationary definition read in FO(LFP).
-/
theorem ac0Definable_lfpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : LFPDefinable P :=
  DescriptiveComplexity.AC0Definable.lfpDefinable h

/--
---
conclusion: Lax895169.ACZeroInPTIME.ac0Definable_mem_PTIME
---
The library's inclusion.
-/
theorem ac0Definable_mem_PTIME {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : AC0Definable P) : PTIME.Mem P :=
  DescriptiveComplexity.ac0Definable_mem_PTIME h

/--
---
conclusion: Lax895169.ACZeroFinite.ac0Definable_congr_finite
---
The library's theorem: the defining equivalence is asked of finite structures
only.
-/
theorem ac0Definable_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    AC0Definable P ↔ AC0Definable Q :=
  DescriptiveComplexity.ac0Definable_congr h

end Lax895169Proofs.Bridge
