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
title: Invariance and characterization of quantified Boolean formulas
type: lemma
---
The truth of a quantified Boolean formula with $k$ blocks, for either
polarity of the first block and either reading of the matrix, is invariant
under isomorphism of instances, and an instance is a yes-instance of the
corresponding problem exactly when the formula is true.
-/

namespace Lax564036.QuantifiedBooleanFormulasInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- The truth of a quantified Boolean formula is isomorphism-invariant. -/
axiom qbfTrue_iso : ∀ (k : ℕ) (start cnf : Bool) {A B : Type} [(qbf k).Structure A]
  [(qbf k).Structure B], (A ≃[qbf k] B) →
    (altQuant A k (fun νs => QbfMatrix cnf νs) start ↔
      altQuant B k (fun νs => QbfMatrix cnf νs) start)

/-- The yes-instances are exactly the true formulas. -/
axiom qbfProblem_iff : ∀ (k : ℕ) (start cnf : Bool) (A : Type) [(qbf k).Structure A],
  QbfProblem k start cnf A ↔ altQuant A k (fun νs => QbfMatrix cnf νs) start

end Lax564036.QuantifiedBooleanFormulasInvariance
