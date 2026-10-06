import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.SecondOrderCounting
import Lax366625.QuantitativeLogic
import Lax366625.CountingSat
import Lax366625.MachineNumbers
import Lax366625.CountingRuns
import Lax366625.NumberedCircuits
import Lax366625.HornNumbers

/-!
---
title: The value of counting accepting runs
type: lemma
---
The number of halting walks of a well-formed machine instance is invariant
under isomorphism, so the value of counting accepting runs on an instance is
that number.
-/

namespace Lax366625.CountingRunsValue

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The number of halting walks is isomorphism-invariant. -/
axiom sharpNtmAccept_count_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → Nat.card {conf : A → Config A // (tmData A).WellFormed ∧ TMData.IsHaltWalk
    (tmData A) conf} = Nat.card {conf : B → Config B // (tmData B).WellFormed ∧ TMData.IsHaltWalk
    (tmData B) conf}

/-- The value of the problem is the number it is defined by. -/
axiom sharpNtmAccept_eq :
  ∀ (A : Type) [turing.Structure A], SharpNTMAccept A = Nat.card {conf : A → Config A //
    (tmData A).WellFormed ∧ TMData.IsHaltWalk (tmData A) conf}

end Lax366625.CountingRunsValue
