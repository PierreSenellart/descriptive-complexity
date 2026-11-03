import Lax832283.MachineBridge
import Lax832283Proofs.DescriptiveComplexity.Strings.NP
import Lax832283Proofs.DescriptiveComplexity.Strings.PTime

/-!
# The bridge, from the two capture theorems

The logical statements are the library's own. Each machine statement is one application of a
capture theorem of a required entry.
-/

namespace Lax832283Proofs.Bridge

open FirstOrder Lax904597.Problems Lax904597.Classes Lax535992.ClassPTIME
open Lax832283.StringProblems Lax988886.FiniteStructures
open Lax988886.NondeterministicPolynomialTime Lax751879.PolynomialTime

/-- The Fagin entry, in the form the library takes as a hypothesis. -/
theorem fagin : DescriptiveComplexity.Strings.Lax.FaginCaptures :=
  fun Q hQ => Lax988886.Fagin.capturesNP Q hQ

/-- The Immerman–Vardi entry, in the form the library takes as a hypothesis. -/
theorem immermanVardi : DescriptiveComplexity.Strings.Lax.ImmermanVardiCaptures :=
  fun Q => Lax751879.ImmermanVardi.capturesPtime Q

/--
---
conclusion: Lax832283.LogicalBridge.mem_NP_iff_definable
---
The library's translation of existential second-order logic.
-/
theorem mem_NP_iff_definable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    NP.Mem P ↔ Lax988886.ExistentialSecondOrder.Definable (toProperty V P) :=
  DescriptiveComplexity.Strings.mem_NP_iff_definable V P

/--
---
conclusion: Lax832283.LogicalBridge.mem_PTIME_iff_definable
---
The library's translations of least fixed points, by Bekić's principle and by iteration.
-/
theorem mem_PTIME_iff_definable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    PTIME.Mem P ↔ Lax751879.FixedPointSemantics.Definable (toQuery V P) :=
  DescriptiveComplexity.Strings.mem_PTIME_iff_definable V P

/--
---
conclusion: Lax832283.MachineBridge.mem_NP_iff_inNP
---
The logical statement and Fagin's theorem.
-/
theorem mem_NP_iff_inNP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : NP.Mem P ↔ InNP (toProperty V P) :=
  (Lax832283.LogicalBridge.mem_NP_iff_definable V P).trans
    (Lax988886.Fagin.capturesNP _ (DescriptiveComplexity.Strings.toProperty_isoInvariant V P))

/--
---
conclusion: Lax832283.MachineBridge.mem_NP_iff_languageInNP
---
Membership in NP as the archive defines it unfolds to the language of encodings.
-/
theorem mem_NP_iff_languageInNP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    NP.Mem P ↔ LanguageInNP (Lax988886.FiniteStructures.language (toProperty V P)) :=
  Lax832283.MachineBridge.mem_NP_iff_inNP V P

/--
---
conclusion: Lax832283.MachineBridge.mem_PTIME_iff_inP
---
The logical statement and the Immerman–Vardi theorem.
-/
theorem mem_PTIME_iff_inP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : PTIME.Mem P ↔ InP (toQuery V P) :=
  (Lax832283.LogicalBridge.mem_PTIME_iff_definable V P).trans
    (Lax751879.ImmermanVardi.capturesPtime _)

/--
---
conclusion: Lax832283.MachineBridge.SAT_languageInNP
---
The Cook–Levin theorem of the core gives the membership.
-/
theorem SAT_languageInNP (V : FinVocab Lax904597.Sat.sat) :
    LanguageInNP (Lax988886.FiniteStructures.language (toProperty V Lax904597.Sat.SAT)) :=
  (Lax832283.MachineBridge.mem_NP_iff_languageInNP V _).mp Lax904597.CookLevin.SAT_NP_complete.1

/--
---
conclusion: Lax832283.MachineBridge.HORNSAT_inP
---
The completeness of HORN-SAT gives the membership.
-/
theorem HORNSAT_inP (V : FinVocab Lax904597.Sat.sat) :
    InP (toQuery V Lax535992.HornSat.HORNSAT) :=
  (Lax832283.MachineBridge.mem_PTIME_iff_inP V _).mp
    Lax535992.HornSatPTIMEComplete.hornSat_PTIME_complete.1

end Lax832283Proofs.Bridge
