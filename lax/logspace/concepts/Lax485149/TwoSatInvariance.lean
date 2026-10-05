import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.KromFragment
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.Reachability
import Lax485149.DeterministicReachability
import Lax485149.TwoSat
import Lax485149.ClassNL
import Lax485149.ClassL

/-!
---
title: Invariance and characterization of 2SAT
type: lemma
---
Being a satisfiable CNF instance of width at most two is invariant under
isomorphism of instances, and an instance is a yes-instance of 2SAT exactly
when it has width at most two and is satisfiable.
-/

namespace Lax485149.TwoSatInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- Being satisfiable of width at most two is isomorphism-invariant. -/
axiom twoSatisfiable_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (TwoSatisfiable A ↔ TwoSatisfiable B)

/-- The yes-instances of 2SAT are exactly the satisfiable instances of width at
most two. -/
axiom twoSat_iff : ∀ (A : Type) [sat.Structure A], TwoSAT A ↔ TwoSatisfiable A

end Lax485149.TwoSatInvariance
