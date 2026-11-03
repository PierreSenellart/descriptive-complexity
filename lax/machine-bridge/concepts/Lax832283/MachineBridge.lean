import Lax832283.LogicalBridge
import Lax904597.CookLevin
import Lax535992.HornSatPTIMEComplete
import Lax751879.ImmermanVardi
import Lax988886.Fagin

/-!
---
title: NP and PTIME are the textbook classes on bit strings
type: theorem
---
A decision problem is in NP exactly when the language of the binary encodings of its
yes-instances has polynomially bounded certificates checked by a polynomial-time Mathlib
machine, and in PTIME exactly when a polynomial-time Mathlib machine decides that language.
The encodings of the yes-instances of SAT and of HORN-SAT are examples, for any numbering of
their vocabulary.
-/

namespace Lax832283.MachineBridge

open FirstOrder Lax904597.Problems Lax904597.Classes Lax535992.ClassPTIME
open Lax832283.StringProblems Lax988886.FiniteStructures
open Lax988886.NondeterministicPolynomialTime Lax751879.PolynomialTime

/-- NP is the textbook class. -/
axiom mem_NP_iff_inNP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : NP.Mem P ↔ InNP (toProperty V P)

/-- NP, on bit strings. -/
axiom mem_NP_iff_languageInNP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    NP.Mem P ↔ LanguageInNP (Lax988886.FiniteStructures.language (toProperty V P))

/-- PTIME is the textbook class. -/
axiom mem_PTIME_iff_inP {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : PTIME.Mem P ↔ InP (toQuery V P)

/-- The encodings of satisfiable CNF instances form a language in NP. -/
axiom SAT_languageInNP (V : FinVocab Lax904597.Sat.sat) :
    LanguageInNP (Lax988886.FiniteStructures.language (toProperty V Lax904597.Sat.SAT))

/-- A polynomial-time machine decides the encodings of the satisfiable Horn instances. -/
axiom HORNSAT_inP (V : FinVocab Lax904597.Sat.sat) :
    InP (toQuery V Lax535992.HornSat.HORNSAT)

end Lax832283.MachineBridge
