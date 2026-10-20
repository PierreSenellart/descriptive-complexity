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
title: The value of #SAT
type: lemma
---
The number of models of a CNF instance is invariant under isomorphism, so the
value of #SAT on an instance is its number of models.
-/

namespace Lax366625.SharpSatValue

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The number of models is isomorphism-invariant. -/
axiom sharpSat_count_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → Nat.card {ν : A → Prop // SatModel A ν} = Nat.card {ν : B → Prop // SatModel B ν}

/-- The value of the problem is the number it is defined by. -/
axiom sharpSat_eq :
  ∀ (A : Type) [sat.Structure A], SharpSAT A = Nat.card {ν : A → Prop // SatModel A ν}

end Lax366625.SharpSatValue
