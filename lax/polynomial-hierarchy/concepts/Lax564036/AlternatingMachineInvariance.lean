import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: Invariance and characterization of alternating machine acceptance
type: lemma
---
Being a well-formed alternating machine instance with well-formed blocks
that accepts is invariant under isomorphism of instances, and an instance is
a yes-instance of alternating machine acceptance exactly when it has this
property.
-/

namespace Lax564036.AlternatingMachineInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Being well-formed and accepting is isomorphism-invariant. -/
axiom atmAccepts_iso : ∀ (k : ℕ) (start : Bool) {A B : Type} [(turingAlt k).Structure A]
  [(turingAlt k).Structure B], (A ≃[turingAlt k] B) →
    (ATMAccepts k start A ↔ ATMAccepts k start B)

/-- The yes-instances of alternating machine acceptance are exactly the
well-formed accepting instances. -/
axiom atmAccept_iff : ∀ (k : ℕ) (start : Bool) (A : Type) [(turingAlt k).Structure A],
  ATMAccept k start A ↔ ATMAccepts k start A

end Lax564036.AlternatingMachineInvariance
