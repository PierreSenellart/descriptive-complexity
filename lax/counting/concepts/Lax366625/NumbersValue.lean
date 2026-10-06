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
title: The values of the number problems
type: lemma
---
The numbers written by a circuit, by unit propagation on a Horn formula, and
by a deterministic Turing machine are invariant under isomorphism of
instances, so the value of each problem on an instance is the number it
writes.
-/

namespace Lax366625.NumbersValue

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The number written by a circuit is isomorphism-invariant. -/
axiom circuitNumber_count_iso : ∀ {A B : Type} [numCircuit.Structure A] [numCircuit.Structure B],
  (A ≃[numCircuit] B) → circuitNumber A = circuitNumber B

/-- The value of the problem is the number it is defined by. -/
axiom circuitNumber_eq : ∀ (A : Type) [numCircuit.Structure A], CircuitNumber A = circuitNumber A

/-- The number written by unit propagation is isomorphism-invariant. -/
axiom hornNumber_count_iso : ∀ {A B : Type} [satOut.Structure A] [satOut.Structure B],
  (A ≃[satOut] B) → hornNumber A = hornNumber B

/-- The value of the problem is the number it is defined by. -/
axiom hornNumber_eq : ∀ (A : Type) [satOut.Structure A], HornNumber A = hornNumber A

/-- The number written by a machine is isomorphism-invariant. -/
axiom dtmNumber_count_iso : ∀ {A B : Type} [turingOut.Structure A] [turingOut.Structure B],
  (A ≃[turingOut] B) → machineNumber A = machineNumber B

/-- The value of the problem is the number it is defined by. -/
axiom dtmNumber_eq : ∀ (A : Type) [turingOut.Structure A], DTMNumber A = machineNumber A

end Lax366625.NumbersValue
